{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- BBAE AST and Type Definitions

data TBBAE where
  TNum :: TBBAE
  TBool :: TBBAE
  deriving (Show,Eq)

data BBAE where
  Num :: Int -> BBAE
  Plus :: BBAE -> BBAE -> BBAE
  Minus :: BBAE -> BBAE -> BBAE
  Bind :: String -> BBAE -> BBAE -> BBAE
  Id :: String -> BBAE
  Boolean :: Bool -> BBAE
  And :: BBAE -> BBAE -> BBAE
  Leq :: BBAE -> BBAE -> BBAE
  IsZero :: BBAE -> BBAE
  If :: BBAE -> BBAE -> BBAE -> BBAE
  deriving (Show,Eq)

type Env = [(String,BBAE)]

type Cont = [(String,TBBAE)]

liftNum:: (Int -> Int -> Int) -> BBAE -> BBAE -> BBAE
liftNum f (Num x) (Num y) = Num (f x y)

liftBool:: (Bool -> Bool -> Bool) -> BBAE -> BBAE -> BBAE
liftBool f (Boolean x) (Boolean y) = Boolean (f x y)

liftBN:: (Int -> Int -> Bool) -> BBAE -> BBAE -> BBAE
liftBN f (Num x) (Num y) = Boolean (f x y)

subst:: String -> BBAE -> BBAE -> BBAE
subst _ _ (Num x) = (Num x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst _ _ (Boolean x) = (Boolean x)
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero a) = (IsZero (subst i v a))
subst i v (If c t e) = (If (subst i v c) (subst i v t) (subst i v e))
subst i v (Bind i' v' b') = if i==i' then (Bind i' (subst i v v') b') else (Bind i' (subst i v v') (subst i v b'))
subst i v (Id i') = if i==i' then v else (Id i')

evalS :: BBAE -> (Maybe BBAE)
evalS (Num a) = Just (Num a)
evalS (Plus l r) = do {
  x <- evalS l;
  y <- evalS r;
  return (liftNum (+) x y)
}
evalS (Minus l r) = do {
  x <- evalS l;
  y <- evalS r;
  if (evalS (Leq y x) == Just (Boolean True)) then return (liftNum (-) x y) else Nothing
}
evalS (Bind i v b) = do {
  v' <- (evalS v);
  (evalS (subst i v' b))
}
evalS (Id id) = Nothing
evalS (Boolean b) = Just (Boolean b)
evalS (And l r) = do {
  x <- evalS l;
  y <- evalS r;
  return (liftBool (&&) x y)
}
evalS (Leq l r) = do {
  x <- evalS l;
  y <- evalS r;
  return (liftBN (<=) x y)
}
evalS (IsZero a) = do {
  x <- evalS a;
  if x == (Num 0) then Just (Boolean True) else Just (Boolean False)
}
evalS (If c t e) = do {
  x <- evalS c;
  if x == (Boolean True) then (evalS t) else (evalS e)
}

evalM :: Env -> BBAE -> (Maybe BBAE)
evalM env (Num a) = Just (Num a)
evalM env (Plus l r) = do {
  x <- (evalM env l);
  y <- (evalM env r);
  return (liftNum (+) x y)
}
evalM env (Minus l r) = do {
  x <- (evalM env l);
  y <- (evalM env r);
  if (evalM env (Leq y x) == Just (Boolean True)) then return (liftNum (-) x y) else Nothing
}
evalM env (Bind i v b) = do {
  v' <- (evalM env v);
  (evalM ((i,v'):env) b)
}
evalM env (Id id) = lookup id env
evalM env (Boolean b) = Just (Boolean b)
evalM env (And l r) = do {
  x <- (evalM env l);
  y <- (evalM env r);
  return (liftBool (&&) x y)
}
evalM env (Leq l r) = do {
  x <- (evalM env l);
  y <- (evalM env r);
  return (liftBN (<=) x y)
}
evalM env (IsZero a) = do {
  x <- evalM env a;
  if x == (Num 0) then Just (Boolean True) else Just (Boolean False)
}
evalM env (If c t e) = do {
  x <- evalM env c;
  if x == (Boolean True) then (evalM env t) else (evalM env e)
}

testBBAE :: BBAE -> Bool
testBBAE f = do {
  if (evalS f)==(evalM [] f) then True else False
}

typeofM :: Cont -> BBAE -> (Maybe TBBAE)
typeofM cont (Num _) = Just TNum
typeofM cont (Boolean _) = Just TBool
typeofM cont (Plus l r) = do {
  x <- typeofM cont l;
  y <- typeofM cont r;
  if (x == TNum && y == TNum) then Just TNum else Nothing
}
typeofM cont (Minus l r) = do {
  x <- typeofM cont l;
  y <- typeofM cont r;
  if (x == TNum && y == TNum) then Just TNum else Nothing
}
typeofM cont (Bind i v b) = do {
  v' <- typeofM cont v;
  typeofM ((i,v'):cont) b
}
typeofM cont (Id id) = (lookup id cont)
typeofM cont (And l r) = do {
  x <- typeofM cont l;
  y <- typeofM cont r;
  if (x == TBool && y == TBool) then Just TBool else Nothing
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

evalT :: BBAE -> (Maybe BBAE)
evalT f = do {
  t <- typeofM [] f;
  evalM [] f
}

