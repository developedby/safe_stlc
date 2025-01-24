-- Simply typed lambda calculus inference
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State
import Data.Map qualified as Map
import Data.Set qualified as Set

data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr

data Type
  = TVar String
  | TArr Type Type
  deriving (Eq)

type Env = Map.Map String Type
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
infer :: Env -> Expr -> Infer (Subst, Type)
infer env (Var x) =
  case Map.lookup x env of
    Nothing -> throwError $ "Unbound variable: " ++ x
    Just t -> return (Map.empty, t)
infer env (Lam x e) = do
  tv <- fresh
  let env' = Map.insert x tv env
  (s1, t1) <- infer env' e
  return (s1, TArr (apply s1 tv) t1)
infer env (App e1 e2) = do
  (s1, t1) <- infer env e1
  (s2, t2) <- infer (Map.map (apply s1) env) e2
  tv <- fresh
  s3 <- unify (apply s2 t1) (TArr t2 tv)
  return (compose (compose s3 s2) s1, apply s3 tv)

-- Generates a fresh type variable.
fresh :: Infer Type
fresh = do
  s <- get
  put (s + 1)
  return $ TVar ("a" ++ show s)

-- Main inference function
doInfer :: Expr -> Either String Type
doInfer term =
  evalState
    (runExceptT $ infer Map.empty term >>= \(subst, t) -> return $ apply subst t)
    0

showExpr :: Expr -> String
showExpr (Var name) = name
showExpr (Lam name body) = "λ" ++ name ++ " " ++ showExpr body
showExpr (App fun arg) = "(" ++ showExpr fun ++ " " ++ showExpr arg ++ ")"

showType :: Type -> String
showType (TVar name) = name
showType (TArr t1 t2) = "(" ++ showType t1 ++ " -> " ++ showType t2 ++ ")"

test :: [String]
test = let
  t = [ (Lam "f" (App (Var "f") (Lam "x" (App (Var "f") (Lam "y" (Var "x")))))),
        (Lam "f" (App (Var "f") (Lam "x" (App (Var "f") (Lam "y" (Var "y"))))))
      ]
  res = map doInfer t
  res' = map (either id showType) res
  in res'
