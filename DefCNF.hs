-- | Definitional CNF.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module DefCNF
    ( Literal(foldLiteral)
    , zipLiterals
    , toPropositional
    , prettyLit
    , foldAtomsLiteral
    , NumAtom(ma, ai)
    , defcnfs
    , defcnf1
    , defcnf2
    , defcnf3
    -- * Tests
    , Atom(P), N
    , tests
    ) where

import Formulas
import Lib.Pretty (HasFixity(fixity))
import Prop (PropositionalFormula, cnf, foldPropositional, nenf, simpcnf)
import PropExamples (N)
import FOL (pApp, MyFormula)
import Data.List as List
import Data.Map as Map
import Data.Monoid ((<>))
import Data.Set as Set
import Language.Haskell.TH.Syntax as TH (Fixity(Fixity), FixityDirection(InfixN))
import Test.HUnit
import Text.PrettyPrint.HughesPJClass (Doc, nest, parens, prettyShow, text)

-- | Literals are the building blocks of the clause and implicative normal
-- |forms.  They support negation and must include True and False elements.
class (Negatable lit, Constants lit, HasFixity atom, Formulae lit atom, Ord lit) => Literal lit atom | lit -> atom where
    foldLiteral :: (lit -> r) -> (Bool -> r) -> (atom -> r) -> lit -> r

-- | Unify two literals
zipLiterals :: Literal lit atom =>
               (lit -> lit -> Maybe r)
            -> (Bool -> Bool -> Maybe r)
            -> (atom -> atom -> Maybe r)
            -> lit -> lit -> Maybe r
zipLiterals neg tf at fm1 fm2 =
    foldLiteral neg' tf' at' fm1
    where
      neg' p1 = foldLiteral (neg p1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldLiteral (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' a1 = foldLiteral (\ _ -> Nothing) (\ _ -> Nothing) (at a1) fm2

toPropositional :: forall lit atom1 pf atom2. (Literal lit atom1, PropositionalFormula pf atom2) =>
                   (atom1 -> atom2) -> lit -> pf
toPropositional ca lit = foldLiteral (\ p -> (.~.) (toPropositional ca p)) fromBool (atomic . ca) lit
prettyLit :: forall lit atom v. (Literal lit atom) =>
              (Fixity -> atom -> Doc)
           -> (v -> Doc)
           -> Fixity
           -> lit
           -> Doc
prettyLit pa pv pprec lit =
    parensIf (pprec > prec) $ foldLiteral neg tf at lit
    where
      neg :: lit -> Doc
      neg x = text "¬" <> prettyLit pa pv (Fixity 6 InfixN) x
      tf x = prettyBool x
      at x = pa (Fixity 6 InfixN) x
      parensIf False = id
      parensIf _ = parens . nest 1
      prec = fixityLiteral lit

fixityLiteral :: (Literal formula atom) => formula -> Fixity
fixityLiteral formula =
    foldLiteral neg tf at formula
    where
      neg _ = Fixity 5 InfixN
      tf _ = Fixity 10 InfixN
      at = fixity

foldAtomsLiteral :: Literal lit atom => (r -> atom -> r) -> r -> lit -> r
foldAtomsLiteral f i lit = foldLiteral (foldAtomsLiteral f i) (const i) (f i) lit

-- | Example (p. 74)
test01 :: Test
test01 = TestCase $ assertEqual "cnf test (p. 74)"
                                "(p[]∨q[]∨r[])∧(p[]∨¬q[]∨¬r[])∧(q[]∨¬p[]∨¬r[])∧(r[]∨¬p[]∨¬q[])"
                                (let (p, q, r) = (pApp "p" [], pApp "q" [], pApp "r" []) in
                                 prettyShow (cnf (p .<=>. (q .<=>. r)) :: MyFormula))

-- | Make a stylized variable and update the index.
data Atom a = P a

class NumAtom atom where
    ma :: N -> atom
    ai :: atom -> N

instance NumAtom (Atom N) where
    ma = P
    ai (P n) = n

mkprop :: forall pf atom. (PropositionalFormula pf atom, NumAtom atom) => N -> (pf, N)
mkprop n = (atomic (ma n :: atom), n + 1)

-- |  Core definitional CNF procedure.
maincnf :: (NumAtom atom, PropositionalFormula pf atom) => (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
maincnf trip@(fm, _defs, _n) =
    foldPropositional co tf at fm
    where
      co (BinOp p (:&:) q) = defstep (.&.) (p,q) trip
      co (BinOp p (:|:) q) = defstep (.|.) (p,q) trip
      co (BinOp p (:<=>:) q) = defstep (.<=>.) (p,q) trip
      co (BinOp _ (:=>:) _) = trip
      co ((:~:) _) = trip
      tf _ = trip
      at _ = trip

defstep :: (PropositionalFormula pf atom, NumAtom atom, Ord pf) => (pf -> pf -> pf) -> (pf, pf) -> (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
defstep op (p,q) (_fm, defs, n) =
  let (fm1,defs1,n1) = maincnf (p,defs,n) in
  let (fm2,defs2,n2) = maincnf (q,defs1,n1) in
  let fm' = op fm1 fm2 in
  case Map.lookup fm' defs2 of
    Just _ -> (fm', defs2, n2)
    Nothing -> let (v,n3) = mkprop n2 in (v, Map.insert v (v .<=>. fm') defs2,n3)

-- | Make n large enough that "v_m" won't clash with s for any m >= n
max_varindex :: NumAtom atom =>  atom -> Int -> Int
max_varindex atom n = max n (ai atom)

-- | Overall definitional CNF.
{-
mk_defcnf :: forall pf lit atom. (PropositionalFormula pf atom, Literal lit atom, NumAtom atom, Ord lit) =>
             ((pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)) -> pf -> Set.Set (Set.Set lit)
-}
mk_defcnf :: (PropositionalFormula formula atom, PropositionalFormula lit atom, NumAtom atom) => ((formula, Map pf pf, Int) -> (lit, Map pf lit, Int)) -> formula -> Set (Set lit)
mk_defcnf fn fm =
  let fm' = nenf fm in
  let n = 1 + overatoms max_varindex fm' 0 in
  let (fm'',defs,_) = fn (fm',Map.empty,n) in
  let (deflist {- :: [pf]-}) = Map.elems defs in
  Set.unions (simpcnf fm'' : List.map simpcnf deflist)

-- defcnf1 :: forall pf lit atom. (PropositionalFormula pf atom, Literal lit atom, NumAtom atom, Ord lit) => lit -> atom -> pf -> pf
defcnf1 :: (PropositionalFormula pf atom, PropositionalFormula (Set (Set pf)) atom, NumAtom atom) =>
           lit -> atom -> pf -> Set (Set pf)
defcnf1 _ _ fm = cnf (mk_defcnf maincnf fm {- :: Set.Set (Set.Set lit)-})


-- Example.
{-
START_INTERACTIVE;;
defcnf1 <<(p \/ (q /\ ~r)) /\ s>>;;
END_INTERACTIVE;;
-}

-- | Version tweaked to exploit initial structure.
subcnf :: (PropositionalFormula pf atom, NumAtom atom) =>
          ((pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int))
       -> (pf -> pf -> pf)
       -> pf
       -> pf
       -> (pf, Map.Map pf pf, Int)
       -> (pf, Map.Map pf pf, Int)
subcnf sfn op p q (_fm,defs,n) =
  let (fm1,defs1,n1) = sfn (p,defs,n) in
  let (fm2,defs2,n2) = sfn (q,defs1,n1) in
  (op fm1 fm2, defs2, n2)

orcnf :: (NumAtom atom, PropositionalFormula pf atom) => (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
orcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:|:) q) = subcnf orcnf (.|.) p q trip
      co _ = maincnf trip

andcnf :: (PropositionalFormula pf atom, NumAtom atom, Ord pf) => (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
andcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> orcnf trip) (\ _ -> orcnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf (.&.) p q trip
      co _ = orcnf trip

defcnfs :: (PropositionalFormula pf atom, NumAtom atom) => pf -> Set (Set pf)
defcnfs fm = mk_defcnf andcnf fm

-- defcnf2 :: forall pf lit atom.(PropositionalFormula pf atom, Literal lit atom, NumAtom atom, Ord lit) => lit -> atom -> pf -> pf
defcnf2 :: (PropositionalFormula pf atom, PropositionalFormula (Set (Set pf)) atom, NumAtom atom) =>
           lit -> atom -> pf -> Set (Set pf)
defcnf2 _ _ fm = cnf (defcnfs fm)

-- Examples.
{-
START_INTERACTIVE;;
defcnf <<(p \/ (q /\ ~r)) /\ s>>;;
END_INTERACTIVE;;
-}

-- | Version that guarantees 3-CNF.
andcnf3 :: (PropositionalFormula pf atom, NumAtom atom, Ord pf) => (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
andcnf3 trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf3 (.&.) p q trip
      co _ = maincnf trip

-- defcnf3 :: forall pf lit atom. (PropositionalFormula pf atom, Literal lit atom, NumAtom atom, Ord lit) => lit -> atom -> pf -> pf
defcnf3 :: (PropositionalFormula pf atom, PropositionalFormula (Set (Set pf)) atom, NumAtom atom) =>
           lit -> atom -> pf -> Set (Set pf)
defcnf3 _ _ fm = cnf (mk_defcnf andcnf3 fm)

tests :: Test
tests = TestList [test01]
