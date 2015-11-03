{-# LANGUAGE RankNTypes, KindSignatures #-}
{-# OPTIONS_GHC -fwarn-unused-binds -fwarn-missing-signatures #-}
module ZTypes (Formula(..), FOL(..), Term(..), Function(..),
              allpairs, Prop(..), PrologRule(..)) where

import Text.PrettyPrint
import Data.List
import Data.Maybe
import Data.Char
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad (foldM)
import Formulas (IsFormula(..))
import FOL (V(V))

newtype Prop = P {pname :: String}  deriving (Eq,Ord)

instance Show Prop where
  show (P s) = s

data PrologRule = Prolog [Formula FOL] (Formula FOL)   deriving (Eq,Ord)

data Formula a = FF
               | TT
               | Atom a
               | Not (Formula a)
               | And (Formula a) (Formula a)
               | Or (Formula a) (Formula a)
               | Imp (Formula a) (Formula a)
               | Iff (Formula a) (Formula a)
               | Forall V (Formula a)
               | Exists V (Formula a)
               deriving (Eq, Ord, Show)

data Term = Var V | Fn Function [Term]  deriving (Eq,Ord, Show)

data FOL = R String [Term]  deriving (Eq,Ord, Show)

newtype Function = FName String deriving (Eq,Ord, Show)

allpairs :: forall t a (t1 :: * -> *) a1.
                  Foldable t1 =>
                  (t -> a -> a1) -> [t] -> t1 a -> [a1]
allpairs f (h1:t1) l2 = itlist (\x a -> f h1 x : a) l2 (allpairs f t1 l2)
allpairs _ [] _ = []

conjuncts :: Formula t -> [Formula t]
conjuncts (And p q) = (conjuncts p) ++ (conjuncts q)
conjuncts fm = [fm]

disjuncts :: Formula t -> [Formula t]
disjuncts (Or p q) = (disjuncts p) ++ (disjuncts q)
disjuncts fm = [fm]

iffs :: Formula t -> [Formula t]
iffs (Iff p q) = (iffs p) ++ (iffs q)
iffs fm = [fm]

itlist :: Foldable t => (a -> b -> b) -> t a -> b -> b
itlist f l b = foldr f b l

-- pretty printing Prop

--instance (Show a) => Show (Formula a) where
-- show fm = render (showFormula fm)

showFormula :: forall a. Show a => Formula a -> Doc
showFormula FF = char '⟘'
showFormula TT = char '⟙'
showFormula (Atom a) = text (show a)
showFormula (Not a@(Atom _)) = (char '¬') <> (showFormula a)
showFormula (Not p) = parens $ (char '¬') <> (showFormula p)
showFormula p@(And _ _) = parens $ hcat (punctuate (text " ⋀ ") (map showFormula (conjuncts p)))
showFormula p@(Or _ _) = parens $ hcat (punctuate (text " ⋁ ") (map showFormula (disjuncts p)))
showFormula (Imp p q) = parens $ (showFormula p) <+> (text "⟹ ") <+> (showFormula q)
showFormula p@(Iff _ _) = parens $ hcat (punctuate (text " ⟺  ") (map showFormula (iffs p)))
showFormula (Forall (V x) p) = (char '∀') <> (text x) <> (char ':') <> (showFormula p)
showFormula (Exists (V x) p) = (char '∃') <> (text x) <> (char ':') <> (showFormula p)

-- pretty printing FOL

isOperator :: Char -> Bool
isOperator c = (isSymbol c) || (isPunctuation c)

showTerm :: Term -> Doc
showTerm (Var (V s)) = text s
showTerm (Fn (FName s) []) = text "'" <> text s <> text "'"
showTerm (Fn (FName s@(h:_)) [x,y]) | isOperator h = parens (showTerm x <+> (text s) <+> showTerm y)
showTerm (Fn (FName s) args) = text s <> (brackets (hcat (punctuate (char ',') (map showTerm args))))

showFOL :: FOL -> Doc
showFOL (R s []) = text s
showFOL (R s@(h:_) [x,y]) | isOperator h = showTerm x <+> (text s) <+> showTerm y
showFOL (R s args) = text s <> (parens (hcat (punctuate (char ',') (map showTerm args))))

showProlog :: PrologRule -> Doc
showProlog (Prolog xs y) = (showFormula y) <+> (text ":-") <+> (hcat (punctuate (text ", ") (map showFormula xs)))
{-
instance Show Term where
   show t = render (showTerm t)

instance Show FOL where
   show t = render (showFOL t)
-}
instance Show PrologRule where
   show prolog = render (showProlog prolog)
