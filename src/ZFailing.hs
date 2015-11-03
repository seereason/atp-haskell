{-# LANGUAGE ImplicitParams #-}
module ZFailing (Failing,failure,fromSuccess,isSuccess,isFailure,try,tryM,sequenceNestedFailing) where

import Control.Applicative
import Control.Monad

import GHC.Stack

data Failing a = Failure String | Success a   deriving (Eq, Ord)

instance Functor Failing where
    fmap _ (Failure x) = Failure x
    fmap f (Success y) = Success (f y)

instance Applicative Failing where
    pure          = Success
    Failure  e <*> _ = Failure e
    Success f <*> r = fmap f r

instance Monad Failing where
    return = Success
    Failure  l >>= _ = Failure l
    Success r >>= k = k r

instance Foldable Failing where
    foldMap _ (Failure _) = mempty
    foldMap f (Success y) = f y

    foldr _ z (Failure _) = z
    foldr f z (Success y) = f y z

    length (Failure _)  = 0
    length (Success _) = 1

    null             = isFailure

instance Traversable Failing where
    traverse _ (Failure x) = pure (Failure x)
    traverse f (Success y) = Success <$> f y

instance (Show a) => Show (Failing a) where
   show (Failure msg) = "<<" ++ msg ++ ">>"
   show (Success x) = show x

failure :: (?loc :: CallStack) => String -> Failing a
failure msg = Failure (msg ++ ": " ++ showCallStack ?loc)

fromSuccess (Success a) = a

isSuccess (Success _) = True
isSuccess _ = False

isFailure (Failure _) = True
isFailure _ = False


try :: Failing c -> c -> c
try (Success success) _ = success
try (Failure _) f = f

tryM :: Failing a -> Failing a -> Failing a
tryM (Success success) _ = return success
tryM (Failure _) f = f

sequenceNestedFailing :: Failing (Failing b) -> Failing b
sequenceNestedFailing (Success (Success x)) = Success x
sequenceNestedFailing (Success (Failure s)) = Failure s
sequenceNestedFailing (Failure s) = Failure s
