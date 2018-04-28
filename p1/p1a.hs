{-# LANGUAGE GADTs, FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- AST Definition

data TABE where
  TNum :: TABE
  TBool :: TABE
  deriving (Show,Eq)

data ABE where
  Num :: Int -> ABE
  Plus :: ABE -> ABE -> ABE
  Minus :: ABE -> ABE -> ABE
  Mult :: ABE -> ABE -> ABE
  Div :: ABE -> ABE -> ABE
  Boolean :: Bool -> ABE
  And :: ABE -> ABE -> ABE
  Leq :: ABE -> ABE -> ABE
  IsZero :: ABE -> ABE
  If :: ABE -> ABE -> ABE -> ABE
  deriving (Show,Eq)

-- Evaluation Functions
liftNum:: (Int -> Int -> Int) -> ABE -> ABE -> ABE
liftNum f (Num x) (Num y) = Num (f x y)

liftBool:: (Bool -> Bool -> Bool) -> ABE -> ABE -> ABE
liftBool f (Boolean x) (Boolean y) = Boolean (f x y)

liftBN:: (Int -> Int -> Bool) -> ABE -> ABE -> ABE
liftBN f (Num x) (Num y) = Boolean (f x y)

evalM :: ABE -> (Maybe ABE)
evalM (Num a) = Just (Num a)
evalM (Plus l r) = do {
  x <- evalM l;
  y <- evalM r;
  return (liftNum (+) x y)
}
evalM (Minus l r) = do {
  x <- evalM l;
  y <- evalM r;
  if (evalM (Leq y x) == Just (Boolean True)) then return (liftNum (-) x y) else Nothing
}
evalM (Mult l r) = do {
  x <- evalM l;
  y <- evalM r;
  return (liftNum (*) x y)
}
evalM (Div l r) = do {
  x <- evalM l;
  y <- evalM r;
  if y == (Num 0) then Nothing else return (liftNum (div) x y)
}
evalM (Boolean b) = Just (Boolean b)
evalM (And l r) = do {
  x <- evalM l;
  y <- evalM r;
  return (liftBool (&&) x y)
}
evalM (Leq l r) = do {
  x <- evalM l;
  y <- evalM r;
  return (liftBN (<=) x y)
}
evalM (IsZero a) = do {
  x <- evalM a;
  if x == (Num 0) then Just (Boolean True) else Just (Boolean False)
}
evalM (If c t e) = do {
  x <- evalM c;
  if x == (Boolean True) then (evalM t) else (evalM e)
}

evalErr :: ABE -> (Maybe ABE)
evalErr (Num a) = Just (Num a)
evalErr (Plus l r) = do {
  x <- evalErr l;
  y <- evalErr r;
  case x of
    (Num ex) -> case y of
                  (Num ey) -> return (liftNum (+) x y)
                  _ -> Nothing
    _ -> Nothing
}
evalErr (Minus l r) = do {
  x <- evalErr l;
  y <- evalErr r;
  case x of
    (Num ex) -> case y of
                  (Num ey) -> if (evalErr (Leq y x) == Just (Boolean True)) then return (liftNum (-) x y) else Nothing
                  _ -> Nothing
    _ -> Nothing
}
evalErr (Mult l r) = do {
  x <- evalErr l;
  y <- evalErr r;
  case x of
    (Num ex) -> case y of
                  (Num ey) -> return (liftNum (*) x y)
                  _ -> Nothing
    _ -> Nothing
}
evalErr (Div l r) = do {
  x <- evalErr l;
  y <- evalErr r;
  case x of
    (Num ex) -> case y of
                  (Num ey) -> if y == (Num 0) then Nothing else return (liftNum (div) x y)
                  _ -> Nothing
    _ -> Nothing 
}
evalErr (Boolean b) = Just (Boolean b)
evalErr (And l r) = do {
  x <- evalErr l;
  y <- evalErr r;
  case x of
    (Boolean ex) -> case y of
                  (Boolean ey) -> return (liftBool (&&) x y)
                  _ -> Nothing
    _ -> Nothing
}
evalErr (Leq l r) = do {
  x <- evalErr l;
  y <- evalErr r;
  case x of
    (Num ex) -> case y of
                  (Num ey) -> return (liftBN (<=) x y)
                  _ -> Nothing
    _ -> Nothing
}
evalErr (IsZero a) = do {
  x <- evalErr a;
  case x of
    (Num ex) -> if x == (Num 0) then Just (Boolean True) else Just (Boolean False)
    _ -> Nothing
}
evalErr (If c t e) = do {
  x <- evalErr c;
  case x of
    (Boolean ex) -> if x == (Boolean True) then (evalErr t) else (evalErr e)
    _ -> Nothing
}

-- Type Derivation Function

typeofM :: ABE -> Maybe TABE
typeofM (Num _) = Just TNum
typeofM (Boolean _) = Just TBool
typeofM (Plus l r) = do {
  x <- typeofM l;
  y <- typeofM r;
  if (x == TNum && y == TNum) then Just TNum else Nothing
}
typeofM (Minus l r) = do {
  x <- typeofM l;
  y <- typeofM r;
  if (x == TNum && y == TNum) then Just TNum else Nothing
}
typeofM (Mult l r) = do {
  x <- typeofM l;
  y <- typeofM r;
  if (x == TNum && y == TNum) then Just TNum else Nothing
}
typeofM (Div l r) = do {
  x <- typeofM l;
  y <- typeofM r;
  if (x == TNum && y == TNum) then Just TNum else Nothing
}
typeofM (And l r) = do {
  x <- typeofM l;
  y <- typeofM r;
  if (x == TBool && y == TBool) then Just TBool else Nothing
}
typeofM (Leq l r) = do {
  x <- typeofM l;
  y <- typeofM r;
  if (x == TNum && y == TNum) then Just TBool else Nothing
}
typeofM (IsZero a) = do {
  x <- typeofM a;
  if (x == TNum) then Just TBool else Nothing
}
typeofM (If c t e) = do {
  tc <- typeofM c;
  tt <- typeofM t;
  te <- typeofM e;
  if (tc == TBool) then (if tt == te then Just tt else Nothing) else Nothing
}

-- Combined interpreter

evalTypeM :: ABE -> Maybe ABE
evalTypeM x = do {
  t <- typeofM x;
  evalM x
}

-- Optimizer

optimize :: ABE -> ABE
optimize (Plus x (Num 0)) = optimize x
optimize (If (Boolean True) t e) = optimize t
optimize (If (Boolean False) t e) = optimize e
optimize x = x

interpOptM :: ABE -> Maybe ABE
interpOptM x = do {
  t <- typeofM x;
  evalM (optimize x)
}
