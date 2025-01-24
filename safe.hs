-- Simply typed lambda calculus inference
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State
import Data.Map qualified as Map
import Data.Set qualified as Set
import Text.Parsec qualified as P
import Text.Parsec.String (Parser)
import Data.Char (isAlphaNum, isLetter, isSpace)
import Control.Applicative ((<|>))

data Expr
  = Var String
  | Lam String Type Expr
  | App Expr Expr

data Type
  = TVar String
  | TArr Type Type
  deriving (Eq)


--- Type inference ---

type Env t = Map.Map String t
type Subst = Map.Map String Type
type Infer a = ExceptT String (State Int) a

apply :: Subst -> Type -> Type
apply s (TVar a) = Map.findWithDefault (TVar a) a s
apply s (TArr a b) = TArr (apply s a) (apply s b)

ftv :: Type -> Set.Set String
ftv (TVar a) = Set.singleton a
ftv (TArr a b) = ftv a `Set.union` ftv b

-- Unifies two types.
unify :: Type -> Type -> Infer Subst
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify (TArr a b) (TArr a' b') = do
  s1 <- unify a a'
  s2 <- unify (apply s1 b) (apply s1 b')
  return (compose s2 s1)
-- unify _ _ = throwError "Types do not unify"

-- Tries to bind variable `a` to `t` and return that binding as a substitution.
-- Doesn't bind a variable to itself and doesn't bind a variable if it occurs free in `t`.
bind :: String -> Type -> Infer Subst
bind a t
  | t == TVar a = return Map.empty
  | a `Set.member` ftv t = throwError "Occurs check fails"
  | otherwise = return $ Map.singleton a t

-- Composes two substitutions.
-- Applies the first substitution to the second, and then inserts the result into the first.
compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1

-- Infers the type of a term in the given environment.
infer :: Env Type -> Expr -> Infer (Subst, Type, Expr)
infer env (Var x) =
  case Map.lookup x env of
    Nothing -> throwError $ "Unbound variable: " ++ x
    Just t -> return (Map.empty, t, Var x)
infer env (Lam x _ e) = do
  tv <- fresh
  let env' = Map.insert x tv env
  (s1, t1, e1) <- infer env' e
  return (s1, TArr (apply s1 tv) t1, Lam x (apply s1 tv) e1)
infer env (App e1 e2) = do
  (s1, t1, e1) <- infer env e1
  (s2, t2, e2) <- infer (Map.map (apply s1) env) e2
  tv <- fresh
  s3 <- unify (apply s2 t1) (TArr t2 tv)
  return (compose (compose s3 s2) s1, apply s3 tv, App (applyAnn s3 e1) (applyAnn s3 e2))

applyAnn :: Subst -> Expr -> Expr
applyAnn s (Var x) = Var x
applyAnn s (Lam x t e) = Lam x (apply s t) (applyAnn s e)
applyAnn s (App f x) = App (applyAnn s f) (applyAnn s x)

-- Generates a fresh type variable.
fresh :: Infer Type
fresh = do
  s <- get
  put (s + 1)
  return $ TVar ("a" ++ show s)

-- Main inference function
doInfer :: Expr -> Either String (Type, Expr)
doInfer term =
  evalState
    (runExceptT $ infer Map.empty term >>= \(subst, t, e) -> return $ (apply subst t, e))
    0


-- Check if a term is safe
checkSafe :: Expr -> Bool -> Env Int -> Bool
checkSafe (Var _)     unsafePos ctx = True
checkSafe (Lam n t e) unsafePos ctx =
  let
    lamOrder  = exprOrd ctx (Lam n t e)
    fvsOrder  = fvsOrd ctx (Map.singleton n (typeOrd t)) e
    unsafeFvs = any (\fv -> fv < lamOrder) fvsOrder
    lamSafe   = not (unsafePos && unsafeFvs)
    bodSafe   = checkSafe e False (Map.insert n (typeOrd t) ctx)
  in lamSafe && bodSafe
checkSafe (App t1 t2) unsafePos ctx =
  let
    appOrder    = exprOrd ctx (App t1 t2)
    fvsOrder    = fvsOrd ctx Map.empty t1 ++ fvsOrd ctx Map.empty t2
    unsafeFvs   = any (\fv -> fv < appOrder) fvsOrder
    appSafe     = not (unsafePos && unsafeFvs)
    t1Safe      = checkSafe t1 (case t1 of { App _ _ -> False; _ -> True }) ctx
    t2Safe      = checkSafe t2 True ctx
  in appSafe && t1Safe && t2Safe

-- Order of a type
typeOrd :: Type -> Int
typeOrd (TVar n)   = 0
typeOrd (TArr a b) = max ((typeOrd a) + 1) (typeOrd b)

-- Order of an expression
exprOrd :: Env Int -> Expr -> Int
exprOrd ctx (Var n) = ctx Map.! n
exprOrd ctx (Lam nam typ bod) = max ((typeOrd typ) + 1) (exprOrd (Map.insert nam (typeOrd typ) ctx) bod)
exprOrd ctx (App t1 t2) = max (exprOrd ctx t1) (exprOrd ctx t2)

-- Order of free variables in an expression
fvsOrd :: Env Int -> Env Int -> Expr -> [Int]
fvsOrd ctxO ctxI (Var n)     = if not $ Map.member n ctxI then [ctxO Map.! n] else []
fvsOrd ctxO ctxI (Lam x t e) = fvsOrd ctxO (Map.insert x (typeOrd t) ctxI) e
fvsOrd ctxO ctxI (App t1 t2) = fvsOrd ctxO ctxI t1 ++ fvsOrd ctxO ctxI t2


--- Parser ---
-- Helper parsers

skipSpaces :: Parser ()
skipSpaces = (P.many $ P.satisfy isSpace) >> return ()

lexeme :: Parser a -> Parser a
lexeme p = p <* skipSpaces

symbol :: String -> Parser String
symbol s = lexeme $ P.string s

parens :: Parser a -> Parser a
parens = P.between (symbol "(") (symbol ")")

-- Main parsers


parseFunction :: Parser (String, Expr)
parseFunction = do
  name <- parseName
  symbol "="
  term <- parseTerm
  return (name, term)

parseTerm :: Parser Expr
parseTerm = parseLambdaTerm <|> parseAppTerm <|> parseVarTerm

parseLambdaTerm :: Parser Expr
parseLambdaTerm = do
  symbol "λ" <|> symbol "@"
  name <- parseName
  body <- parseTerm
  return $ Lam name (TVar "") body

parseAppTerm :: Parser Expr
parseAppTerm = parens $ do
  terms <- P.many1 parseTerm
  return $ foldl1 App terms

parseVarTerm :: Parser Expr
parseVarTerm = Var <$> parseName

parseName :: Parser String
parseName = lexeme $ (:) <$> P.satisfy isFirstChar <*> P.many (P.satisfy isRestChar)
  where
    isFirstChar c = isLetter c || c == '_'
    isRestChar c = isAlphaNum c || c == '_'


--- Show ---

showExpr :: Expr -> String
showExpr (Var name) = name
showExpr (Lam name typ body) = "λ{" ++ name ++ ":" ++ showType typ ++ "} " ++ showExpr body
showExpr (App fun arg) = "(" ++ showExpr fun ++ " " ++ showExpr arg ++ ")"

showType :: Type -> String
showType (TVar name) = name
showType (TArr t1 t2) = "(" ++ showType t1 ++ " -> " ++ showType t2 ++ ")"


--- Main ---

test :: IO ()
test = let
  testInputs =
    [ "λf (f (λx (f (λy x))))",
      "λf (f (λx (f (λy y))))",
      "λy (λn (n λy (n λz y)) λx (x (x y)))",
      "λy λn ((n λy (n λz y)) λx (x (x y)))"
    ]
  parseResults = map (P.parse parseTerm "test") testInputs
  res = map (
    \input -> case input of
      Left err -> show err
      Right expr -> case doInfer expr of
        Left err -> err
        Right (t, e) -> showExpr e ++ "\n" ++ showType t ++ "\nSafe: " ++ show (checkSafe e True Map.empty) ++ "\n"
    ) parseResults
  in putStrLn $ unlines res
