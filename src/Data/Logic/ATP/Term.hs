-- | A Term is a expression representing a domain element.  It is
-- composed of variables which can be bound to domain elements, or
-- functions which can be applied to terms to yield other domain
-- elements.

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Logic.ATP.Term
    ( -- * Variables
      IsVariable(variant, prefix)
    , variants
    --, showVariable
    , V(V)
    -- * Functions
    , IsFunction
    , Arity
    , FName(FName)
    -- * Terms
    , IsTerm(TVarOf, FunOf, vt, fApp, foldTerm)
    , zipTerms
    , convertTerm
    , precedenceTerm
    , associativityTerm
    , prettyTerm
    , prettyFunctionApply
    , showTerm
    , showFunctionApply
    , funcs
    , Term(Var, FApply)
    , FTerm
    , testTerm
    ) where

import Data.Data (Data)
import Data.Logic.ATP.Pretty ((<>), Associativity(InfixN), Doc, HasFixity(associativity, precedence), Precedence, prettyShow, text)
import Data.Set as Set (empty, insert, member, Set, singleton)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Prelude hiding (pred)
import Text.PrettyPrint (parens, brackets, punctuate, comma, fsep, space)
import Text.PrettyPrint.HughesPJClass (maybeParens, Pretty(pPrint, pPrintPrec), PrettyLevel, prettyNormal)
import Test.HUnit

---------------
-- VARIABLES --
---------------

class (Ord v, IsString v, Pretty v, Show v) => IsVariable v where
    variant :: v -> Set v -> v
    -- ^ Return a variable based on v but different from any set
    -- element.  The result may be v itself if v is not a member of
    -- the set.
    prefix :: String -> v -> v
    -- ^ Modify a variable by adding a prefix.  This unfortunately
    -- assumes that v is "string-like" but at least one algorithm in
    -- Harrison currently requires this.

-- | Return an infinite list of variations on v
variants :: IsVariable v => v -> [v]
variants v0 =
    loop Set.empty v0
    where loop s v = let v' = variant v s in v' : loop (Set.insert v s) v'

-- | Because IsString is a superclass we can just output a string expression
showVariable :: IsVariable v => v -> String
showVariable v = show (prettyShow v)

newtype V = V String deriving (Eq, Ord, Data, Typeable, Read)

instance IsVariable String where
    variant v vs = if Set.member v vs then variant (v ++ "'") vs else v
    prefix pre s = pre ++ s

instance IsVariable V where
    variant v@(V s) vs = if Set.member v vs then variant (V (s ++ "'")) vs else v
    prefix pre (V s) = V (pre ++ s)

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

instance Pretty V where
    pPrint (V s) = text s

---------------
-- FUNCTIONS --
---------------

class (IsString function, Ord function, Pretty function, Show function) => IsFunction function

type Arity = Int

-- | A simple type to use as the function parameter of Term.  The only
-- reason to use this instead of String is to get nicer pretty
-- printing.
newtype FName = FName String deriving (Eq, Ord)

instance IsFunction FName

instance IsString FName where fromString = FName

instance Show FName where show (FName s) = s

instance Pretty FName where pPrint (FName s) = text s

-----------
-- TERMS --
-----------

-- | A term is an expression representing a domain element, either as
-- a variable reference or a function applied to a list of terms.
class (Eq term, Ord term, Pretty term, Show term, IsString term, HasFixity term,
       IsVariable (TVarOf term), IsFunction (FunOf term)) => IsTerm term where
    type TVarOf term
    -- ^ The associated variable type
    type FunOf term
    -- ^ The associated function type
    vt :: TVarOf term -> term
    -- ^ Build a term which is a variable reference.
    fApp :: FunOf term -> [term] -> term
    -- ^ Build a term by applying terms to an atomic function ('FunOf' @term@).
    foldTerm :: (TVarOf term -> r)          -- ^ Variable references are dispatched here
             -> (FunOf term -> [term] -> r) -- ^ Function applications are dispatched here
             -> term -> r
    -- ^ A fold over instances of 'IsTerm'.

-- | Combine two terms if they are similar (i.e. two variables or
-- two function applications.)
zipTerms :: (IsTerm term1, v1 ~ TVarOf term1, function1 ~ FunOf term1,
             IsTerm term2, v2 ~ TVarOf term2, function2 ~ FunOf term2) =>
            (v1 -> v2 -> Maybe r) -- ^ Combine two variables
         -> (function1 -> [term1] -> function2 -> [term2] -> Maybe r) -- ^ Combine two function applications
         -> term1
         -> term2
         -> Maybe r -- ^ Result for dissimilar terms is 'Nothing'.
zipTerms v ap t1 t2 =
    foldTerm v' ap' t1
    where
      v' v1 =      foldTerm     (v v1)   (\_ _ -> Nothing) t2
      ap' p1 ts1 = foldTerm (\_ -> Nothing) (\p2 ts2 -> if length ts1 == length ts2 then ap p1 ts1 p2 ts2 else Nothing)   t2

-- | Convert between two instances of IsTerm
convertTerm :: (IsTerm term1, v1 ~ TVarOf term1, f1 ~ FunOf term1,
                IsTerm term2, v2 ~ TVarOf term2, f2 ~ FunOf term2) =>
               (v1 -> v2) -- ^ convert a variable
            -> (f1 -> f2) -- ^ convert a function
            -> term1 -> term2
convertTerm cv cf = foldTerm (vt . cv) (\f ts -> fApp (cf f) (map (convertTerm cv cf) ts))

precedenceTerm :: IsTerm term => term -> Precedence
precedenceTerm = const 0

associativityTerm :: IsTerm term => term -> Associativity
associativityTerm = const InfixN

-- | Implementation of pPrint for any term
prettyTerm :: (v ~ TVarOf term, function ~ FunOf term, IsTerm term, HasFixity term, Pretty v, Pretty function) =>
              PrettyLevel -> Rational -> term -> Doc
prettyTerm l r tm = maybeParens (l > prettyNormal || r > precedence tm) (foldTerm pPrint (prettyFunctionApply l) tm)

-- | Format a function application: F(x,y)
prettyFunctionApply :: (function ~ FunOf term, IsTerm term, HasFixity term) => PrettyLevel -> function -> [term] -> Doc
prettyFunctionApply _l f [] = pPrint f
prettyFunctionApply l f ts = pPrint f <> parens (fsep (punctuate comma (map (prettyTerm l 0) ts)))

-- | Implementation of show for any term
showTerm :: (v ~ TVarOf term, function ~ FunOf term, IsTerm term, Pretty v, Pretty function) => term -> String
showTerm = foldTerm showVariable showFunctionApply

-- | Build an expression for a function application: fApp (F) [x, y]
showFunctionApply :: (v ~ TVarOf term, function ~ FunOf term, IsTerm term) => function -> [term] -> String
showFunctionApply f ts = "fApp (" <> show f <> ")" <> show (brackets (fsep (punctuate (comma <> space) (map (text . show) ts))))

funcs :: (IsTerm term, function ~ FunOf term) => term -> Set (function, Arity)
funcs = foldTerm (\_ -> Set.empty) (\f ts -> Set.singleton (f, length ts))

data Term function v
    = Var v
    | FApply function [Term function v]
    deriving (Eq, Ord, Data, Typeable, Read)

instance (IsVariable v, IsFunction function) => IsString (Term function v) where
    fromString = Var . fromString

instance (IsVariable v, IsFunction function) => Show (Term function v) where
    show = showTerm

instance (IsFunction function, IsVariable v) => HasFixity (Term function v) where
    precedence = precedenceTerm
    associativity = associativityTerm

instance (IsFunction function, IsVariable v) => IsTerm (Term function v) where
    type TVarOf (Term function v) = v
    type FunOf (Term function v) = function
    vt = Var
    fApp = FApply
    foldTerm vf fn t =
        case t of
          Var v -> vf v
          FApply f ts -> fn f ts

instance (IsTerm (Term function v)) => Pretty (Term function v) where
    pPrintPrec = prettyTerm

-- | A term type with no Skolem functions
type FTerm = Term FName V

-- Example.
test00 :: Test
test00 = TestCase $ assertEqual "print an expression"
                                "sqrt(-(1, cos(power(+(x, y), 2))))"
                                (prettyShow (fApp "sqrt" [fApp "-" [fApp "1" [],
                                                                     fApp "cos" [fApp "power" [fApp "+" [Var "x", Var "y"],
                                                                                               fApp "2" []]]]] :: Term FName V))

testTerm :: Test
testTerm = TestLabel "Term" (TestList [test00])
