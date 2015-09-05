{-# LANGUAGE  DeriveDataTypeable, FlexibleContexts, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lib.Failing
    ( Failing(Success, Failure)
    , failing
    ) where

import Control.Applicative.Error
import Data.Generics
import Lib.Pretty (Classy(..))

failing :: ([String] -> b) -> (a -> b) -> Failing a -> b
failing f _ (Failure errs) = f errs
failing _ f (Success a)    = f a

instance Monad Failing where
  return = Success
  m >>= f =
      case m of
        (Failure errs) -> (Failure errs)
        (Success a) -> f a
  fail errMsg = Failure [errMsg]

deriving instance Typeable Failing
deriving instance Data a => Data (Failing a)
deriving instance Read a => Read (Failing a)
deriving instance Eq a => Eq (Failing a)
deriving instance Ord a => Ord (Failing a)

instance Show (Classy a) => Show (Classy (Failing a)) where
    show (Classy (Failure errs)) = "Failure " ++ show errs
    show (Classy (Success a)) = show (Success (Classy a))
