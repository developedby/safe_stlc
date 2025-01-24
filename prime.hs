import Control.Monad (forM, forM_, void)
import Control.Monad.State
import Data.Char (chr, ord)
import Text.Parsec hiding (State)
import Text.Parsec.String
import qualified Data.Map as Map
import Data.Map (Map)


data Type 
  = TVar Int       -- Type variable
  | TFun Type Type -- Function type
  | THol           -- Type hole to be filled during inference
  deriving (Eq, Show)

-- Term represents lambda calculus expressions using de Bruijn indices
data Term
  = Var Int         -- de Bruijn index
  | Lam Type Term   -- Lambda abstraction with type annotation
  | App Term Term   -- Application
  deriving (Eq, Show)

showDeBruijn :: Term -> String
showDeBruijn = go False
  where
    go :: Bool -> Term -> String
    go p (Var n) = show (n + 1)  -- Add 1 when showing variables
    go p (Lam ty t) = addParensIf p $ "λ{" ++ showType ty ++ "} " ++ go False t
    go p (App t1 t2) = addParensIf p $ go True t1 ++ " " ++ go True t2

    addParensIf :: Bool -> String -> String
    addParensIf True s = "(" ++ s ++ ")"
    addParensIf False s = s

showNamed :: Term -> String
showNamed t = evalState (go False t []) 0
  where
    go :: Bool -> Term -> [String] -> State Int String 
    go p (Var n) ctx = return $ ctx !! n
    go p (Lam ty t) ctx = do
      count <- get
      let var = nameFromNumber count
      modify (+1)
      body <- go False t (var:ctx)
      return $ addParensIf p $ "λ{" ++ var ++ ":" ++ showType ty ++ "}. " ++ body
    go p (App t1 t2) ctx = do
      s1 <- go True t1 ctx
      s2 <- go True t2 ctx
      return $ addParensIf p $ s1 ++ " " ++ s2

    addParensIf :: Bool -> String -> String
    addParensIf True s = "(" ++ s ++ ")"
    addParensIf False s = s

-- Generate variable name from number: 0->a, 1->b, ..., 25->z, 26->aa, ...
nameFromNumber :: Int -> String
nameFromNumber n = 
  let (q, r) = n `quotRem` 26
      c = chr (ord 'a' + r)
  in if q == 0 
      then [c]
      else nameFromNumber (q-1) ++ [c]

showType :: Type -> String
showType THol = "_"
showType (TVar n) = nameFromNumber n
showType (TFun t1 t2) = showParenType t1 ++ " → " ++ showType t2
  where
    showParenType t@(TFun _ _) = "(" ++ showType t ++ ")"
    showParenType t = showType t


--- EVAL ---

-- Shift all free variables by d when crossing c binders
shift :: Int -> Int -> Term -> Term
shift d c (Var k)     = if k < c then Var k else Var (k + d)
shift d c (Lam ty t)  = Lam ty (shift d (c + 1) t)
shift d c (App t1 t2) = App (shift d c t1) (shift d c t2)

-- Substitute term s for variable number j in term t
subst :: Int -> Term -> Term -> Term
subst j s (Var k)     = if k == j then s else Var k
subst j s (Lam ty t)  = Lam ty (subst (j + 1) (shift 1 0 s) t)
subst j s (App t1 t2) = App (subst j s t1) (subst j s t2)

-- Evaluate a term to normal form
eval :: Term -> Term
eval (App t1 t2) =
  case eval t1 of
    Lam _ t12 -> eval (subst 0 (shift 1 0 t2) t12)
    t1'       -> App t1' (eval t2)
eval t = t


--- PARSER ---

-- Parse a complete term
parseTerm :: String -> Either ParseError Term
parseTerm = parse (spaces *> pTerm 0 <* spaces <* eof) "lambda"

-- Main term parser that tracks lambda depth
pTerm :: Int -> Parser Term
pTerm depth = try (pApp depth) <|> pAtom depth

-- Parse atomic terms (variables or abstractions)
pAtom :: Int -> Parser Term
pAtom depth = spaces *> (pVar depth <|> pLam depth <|> parens (pTerm depth)) <* spaces

-- Parse a variable (de Bruijn index) and verify it's bound
pVar :: Int -> Parser Term
pVar depth = do
  n <- read <$> many1 digit
  if n > depth || n <= 0  -- Check for positive numbers and depth
    then fail $ "Unbound variable " ++ show n ++ " at lambda depth " ++ show depth
    else return $ Var (n - 1)

-- Parse abstraction (λ followed by a term)
pLam :: Int -> Parser Term
pLam depth = do
  char 'λ' <|> char '\\'
  spaces
  t <- pTerm (depth + 1)
  return $ Lam THol t  -- Insert type hole initially

-- Parse application (space-separated terms)
pApp :: Int -> Parser Term
pApp depth = do
  ts <- many1 (try (pAtom depth <* spaces))  -- Add spaces consumption after each atom
  return $ foldl1 App ts

-- Parse parenthesized expressions
parens :: Parser a -> Parser a
parens = between (char '(') (char ')')


--- TYPE CHECKING ---

-- Substitution map for type variables
type Subst = Map Int Type

apply :: Subst -> Type -> Type
apply s t@(TVar n) = Map.findWithDefault t n s
apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
apply s THol = THol

-- Unification
unify :: Type -> Type -> Either String Subst
unify (TVar n) t = varBind n t
unify t (TVar n) = varBind n t
unify (TFun t1 t2) (TFun t1' t2') = do
    s1 <- unify t1 t1'
    s2 <- unify (apply s1 t2) (apply s1 t2')
    return (compose s2 s1)
unify t1 t2 = Left $ "Cannot unify " ++ show t1 ++ " with " ++ show t2

varBind :: Int -> Type -> Either String Subst
varBind n t | t == TVar n = Right Map.empty
           | occurs n t = Left "Occurs check failed"
           | otherwise = Right $ Map.singleton n t

occurs :: Int -> Type -> Bool
occurs n (TVar m) = n == m
occurs n (TFun t1 t2) = occurs n t1 || occurs n t2

-- Type inference
infer :: [Type] -> Int -> Term -> Either String (Term, Type, Subst, Int)
infer ctx n term = case term of
    Var i ->
      if i < length ctx
      then Right (Var i, ctx !! i, Map.empty, n)
      else Left $ "Unbound variable: " ++ show i
    Lam _ bod -> do
      let tv = TVar n
      (bod', t1, s1, n1) <- infer (tv:ctx) (n + 1) bod
      return (Lam tv bod', TFun (apply s1 tv) t1, s1, n1)
    App fun arg -> do
      (fun', t1, s1, n1) <- infer ctx n fun
      (arg', t2, s2, n2) <- infer (map (apply s1) ctx) n1 arg
      let tv = TVar n2
      s3 <- unify (apply s2 t1) (TFun t2 tv)
      return (App fun' arg', apply s3 tv, compose (compose s3 s2) s1, n2 + 1) 

-- Compose two substitutions
compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.union (Map.map (apply s2) s1) s2

typeCheck :: Term -> Either String (Term, Type)
typeCheck term = do
    (t, typ, s, _) <- infer [] 0 term
    return (substAnn s t, apply s typ)

-- Apply type substitution to terms
substAnn :: Subst -> Term -> Term
substAnn s (Var x) = Var x
substAnn s (Lam t body) = Lam (apply s t) (substAnn s body)
substAnn s (App f x) = App (substAnn s f) (substAnn s x)


--- SAFE TYPE CHECKING ---

-- Check if a term is safe
checkSafe :: Term -> Bool -> [Int] -> Bool
checkSafe (Var _)       unsafePos ctx = True
checkSafe (Lam typ bod) unsafePos ctx =
  let
    ctx'      = typeOrd typ : ctx
    lamOrder  = termOrd ctx (Lam typ bod)
    fvsOrder  = ordFreeVars ctx' 1 bod
    unsafeFvs = any (\fv -> fv < lamOrder) fvsOrder
    lamUnsafe = unsafePos && unsafeFvs
    bodUnsafe = checkSafe bod False ctx'
  in not (lamUnsafe || bodUnsafe)
checkSafe (App t1 t2) unsafePos ctx =
  let
    appOrder    = termOrd ctx (App t1 t2)
    fvsOrder    = ordFreeVars ctx 1 t1 ++ ordFreeVars ctx 1 t2
    unsafeFvs   = any (\fv -> fv < appOrder) fvsOrder
    appUnsafe   = unsafePos && unsafeFvs
    t1UnsafePos = case t1 of { App _ _ -> False; _ -> True }
    t1Unsafe    = checkSafe t1 t1UnsafePos ctx
    t2Unsafe    = checkSafe t2 True ctx
  in not (appUnsafe || t1Unsafe || t2Unsafe)

typeOrd :: Type -> Int
typeOrd (TVar n)   = 0
typeOrd (TFun a b) = max ((typeOrd a) + 1) (typeOrd b)
typeOrd THol       = 0

termOrd :: [Int] -> Term -> Int
termOrd ctx (Var n) = ctx !! n
termOrd ctx (Lam typ bod) = (typeOrd typ)
termOrd ctx (App t1 t2) = max (termOrd ctx t1) (termOrd ctx t2)

ordFreeVars :: [Int] -> Int -> Term -> [Int]
ordFreeVars ctx dep (Var n)       = if n > dep then [n] else []
ordFreeVars ctx dep (Lam typ bod) = ordFreeVars (typeOrd typ : ctx) (dep + 1) bod
ordFreeVars ctx dep (App t1 t2)   = ordFreeVars ctx dep t1 ++ ordFreeVars ctx dep t2


--- MAIN ---

-- Update main
main :: IO ()
main = do
  let examples = [
        "λ λ 2",
        "(λ 1) 2",
        "λ 1 (λ 2 (λ 2))",
        "λ 1 (λ 2 (λ 1))",
        "(λ 1 1) λ 1",
        "λ 1 1",
        "(λ 1 1) (λ λ λ 1 (λ λ 1) ((λ 4 4 1 ((λ 1 1) (λ 2 (1 1)))) (λ λ λ λ 1 3 (2 (6 4))))) (λ λ λ λ 1 (λ λ 2) (2 4))"
        ]
  forM_ examples $ \ex -> do
    putStrLn $ "Term: " ++ ex
    case parseTerm ex of 
      Left err -> putStrLn $ "PErr: " ++ show err
      Right t -> do
        putStrLn $ "Parse: " ++ showNamed t
        case typeCheck t of
          Left err -> putStrLn $ "TErr: " ++ err
          Right (annotated, typ) -> do
            let evaluated = eval annotated
            putStrLn $ "Type: " ++ showType typ
            putStrLn $ "Ann:  " ++ showNamed annotated
            putStrLn $ "Eval: " ++ showNamed evaluated
            putStrLn $ "Safe: " ++ show (checkSafe annotated False [])
    putStrLn "---\n"
