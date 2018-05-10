{-# LANGUAGE GADTs #-}

import Text.ParserCombinators.Parsec
import Control.Monad
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as Token

-- Calculator language extended with an environment to hold defined variables

data TFBAE where
  TNum :: TFBAE
  TBool :: TFBAE
  (:->:) :: TFBAE -> TFBAE -> TFBAE
  deriving (Show,Eq)

data FBAE where
  Num :: Int -> FBAE
  Plus :: FBAE -> FBAE -> FBAE
  Minus :: FBAE -> FBAE -> FBAE
  Mult :: FBAE -> FBAE -> FBAE
  Div :: FBAE -> FBAE -> FBAE
  Bind :: String -> FBAE -> FBAE -> FBAE
  Lambda :: String -> TFBAE -> FBAE -> FBAE
  App :: FBAE -> FBAE -> FBAE
  Id :: String -> FBAE
  Boolean :: Bool -> FBAE
  And :: FBAE -> FBAE -> FBAE
  Or :: FBAE -> FBAE -> FBAE
  Leq :: FBAE -> FBAE -> FBAE
  IsZero :: FBAE -> FBAE
  If :: FBAE -> FBAE -> FBAE -> FBAE
  Fix :: FBAE -> FBAE
  deriving (Show,Eq)

-- Value defintion for statically scoped eval

data FBAEVal where
  NumV :: Int -> FBAEVal
  BooleanV :: Bool -> FBAEVal
  ClosureV :: String -> TFBAE -> FBAE -> Env -> FBAEVal
  deriving (Show,Eq)

-- Enviornment for statically scoped eval

type Env = [(String,FBAEVal)]

subst :: String -> FBAE -> FBAE -> FBAE
subst _ _ (Num x) = (Num x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (Mult l r) = (Mult (subst i v l) (subst i v r))
subst i v (Div l r) = (Div (subst i v l) (subst i v r))
subst i v (Bind i' v' b') = if i==i' then (Bind i' (subst i v v') b') else (Bind i' (subst i v v') (subst i v b'))
subst i v (Lambda i' t' b') = (Lambda i' t' (subst i v b'))
subst i v (App f' a') = (App (subst i v f') (subst i v a') )
subst i v (Id i') = if i==i' then v else (Id i')
subst _ _ (Boolean x) = (Boolean x)
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Or l r) = (Or (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero x) = (IsZero (subst i v x))
subst i v (If c t f) = (If (subst i v c) (subst i v t) (subst i v f))
subst i v (Fix f) = Fix (subst i v f)

-- Statically scoped eval
         
evalM :: Env -> FBAE -> (Maybe FBAEVal)
evalM env (Num x) = return (NumV x)
evalM env (Plus l r) = do { 
  (NumV l') <- (evalM env l);
  (NumV r') <- (evalM env r);
  return (NumV (l'+ r')) 
}
evalM env (Minus l r) = do { 
  (NumV l') <- (evalM env l);
  (NumV r') <- (evalM env r);
  return (NumV (l'- r')) 
}
evalM env (Mult l r) = do   {
    (NumV l') <- (evalM env l);
    (NumV r') <- (evalM env r);
    return (NumV (l' * r')) 
}
evalM env (Div l r) = do    {
    (NumV l') <- (evalM env l);
    (NumV r') <- (evalM env r);
    if r' /= 0 then return (NumV (l' `div` r')) else Nothing
}
evalM env (Bind i v b) = do {
  v' <- (evalM env v);
  evalM ((i,v'):env) b
}
evalM env (Lambda i t b) = return (ClosureV i t b env)
evalM env (App f a) = do { 
  a' <- (evalM env a);
  (ClosureV i t b e) <- (evalM env f);
  evalM ((i,a'):e) b 
}
evalM env (Id id) = (lookup id env)
evalM env (Boolean x) = return (BooleanV x)
evalM env (And l r) = do    {
  (BooleanV l') <- (evalM env l);
  (BooleanV r') <- (evalM env r);
  return (BooleanV (l' && r'))
}
evalM env (Or l r) = do     {
  (BooleanV l') <- (evalM env l);
  (BooleanV r') <- (evalM env r);
  return (BooleanV (l' || r'))
}
evalM env (Leq l r) = do    {
  (NumV l') <- (evalM env l);
  (NumV r') <- (evalM env r);
  return (BooleanV (l' <= r'))
}
evalM env (IsZero l) = do   {
  (NumV l') <- (evalM env l);
  return (BooleanV (l' == 0))
}
evalM env (If c t e) = do   {
  BooleanV v <- (evalM env c);
  if v then (evalM env t) else (evalM env e)
}
evalM env (Fix f) = do { 
  (ClosureV i t b e) <- (evalM env f);
  evalM e (subst i (Fix (Lambda i t b)) b) 
}

-- Type inference function

type Cont = [(String,TFBAE)]

typeofM :: Cont -> FBAE -> (Maybe TFBAE)
typeofM cont (Num _) = return TNum
typeofM cont (Plus l r) = do {
  TNum <- (typeofM cont l);
  TNum <- (typeofM cont r);
  return TNum
}
typeofM cont (Minus l r) = do {
  TNum <- (typeofM cont l);
  TNum <- (typeofM cont r);
  return TNum
}
typeofM cont (Mult l r) = do {
  TNum <- (typeofM cont l);
  TNum <- (typeofM cont r);
  return TNum
}
typeofM cont (Div l r) = do {
  TNum <- (typeofM cont l);
  TNum <- (typeofM cont r);
  return TNum
}
typeofM cont (Bind i v b) = do {
  v' <- typeofM cont v;
  typeofM ((i,v'):cont) b
}
typeofM cont (Lambda i t b) = do { 
  tyB <- typeofM ((i,t):cont) b;
  return (t :->: tyB) 
}
typeofM cont (App x y) = do { 
  tyXd :->: tyXr <- typeofM cont x;
  tyY <- typeofM cont y;
  if (tyXd == tyY) then return tyXr else Nothing 
}
typeofM cont (Id id) = (lookup id cont)
typeofM cont (Boolean _) = return TBool
typeofM cont (And l r) = do {
  TBool <- (typeofM cont l);
  TBool <- (typeofM cont r);
  return TBool
}
typeofM cont (Or l r) = do {
  TBool <- (typeofM cont l);
  TBool <- (typeofM cont r);
  return TBool
}
typeofM cont (Leq l r) = do {
  x <- typeofM cont l;
  y <- typeofM cont r;
  if (x == TNum && y == TNum) then Just TBool else Nothing
}
typeofM cont (IsZero a) = do {
  x <- typeofM cont a;
  if (x == TNum) then Just TBool else Nothing
}
typeofM cont (If c t e) = do {
  tc <- typeofM cont c;
  tt <- typeofM cont t;
  te <- typeofM cont e;
  if tt==te then return tt else Nothing
}
typeofM cont (Fix t) = do { 
  (d :->: r) <- typeofM cont t;
  return r 
}

-- Interpreter

interp :: FBAE -> (Maybe FBAEVal)
interp x = do {
  typeofM [] x;
  evalM [] x;
}

-- Factorial function for testing evalM and typeofM.  the type of test1 should
-- be TNum and the result of evaluating test1`should be (NumV 6).  Remember
-- that Just is used to return both the value and type.

test1 = (Bind "f" (Lambda "g" ((:->:) TNum TNum)
                    (Lambda "x" TNum (If (IsZero (Id "x")) (Num 1)
                                         (Mult (Id "x")
                                               (App (Id "g")
                                                    (Minus (Id "x")
                                                           (Num 1)))))))
         (App (Fix (Id "f")) (Num 3)))
