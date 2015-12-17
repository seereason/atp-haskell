{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Data.Logic.ATP.LitWrapper
    ( JL(unJL)
    ) where

import Data.Logic.ATP.Formulas
import Data.Logic.ATP.Lit
import Data.Logic.ATP.Pretty

-- | Wrapper type to make an IsLiteral value that happens to also be
-- JustLiteral.  The JL constructor is not exported, JL values can be
-- built using 'convertToLiteral'.
newtype JL a = JL {unJL :: a}

instance Pretty a => Pretty (JL a) where
    pPrint (JL x) = pPrint x

instance HasFixity a => HasFixity (JL a) where
    precedence = precedence . unJL
    associativity = associativity . unJL

instance IsLiteral a => IsFormula (JL a) where
    type AtomOf (JL a) = AtomOf a
    asBool (JL x) = asBool x
    true = JL (true :: a)
    false = JL (false :: a)
    atomic = JL . atomic
    overatoms f (JL x) r0 = overatomsLiteral' {-(\y r -> f (JL y) r)-} f x r0
    onatoms f (JL x) = JL (onatoms f x)

instance (IsFormula (JL a), IsLiteral a) => JustLiteral (JL a)

instance (IsFormula (JL a), IsLiteral a) => IsLiteral (JL a) where
    naiveNegate (JL x) = JL (naiveNegate x)
    foldNegation n i (JL x) = foldNegation (n . JL) (i . JL) x
    foldLiteral' ho ne tf at (JL x) = foldLiteral' (ho . JL) (ne . JL) tf at x

-- | Unsafe local version of overatomsLiteral - assumes lit is a JustLiteral.
overatomsLiteral' :: IsLiteral lit => (AtomOf lit -> r -> r) -> lit -> r -> r
overatomsLiteral' f fm r0 =
        foldLiteral' undefined ne (const r0) (flip f r0) fm
        where
          ne fm' = overatomsLiteral' f fm' r0
