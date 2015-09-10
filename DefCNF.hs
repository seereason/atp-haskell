-- | Definitional CNF.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module DefCNF
    ( NumAtom(ma, ai)
    , defcnfs
    , defcnf1
    , defcnf2
    , defcnf3
    -- * Tests
    , tests
    ) where

import Formulas as P
import Lit (IsLiteral)
import Pretty (HasFixity(fixity), botFixity)
import Prop as P (IsPropositional, cnf', cnf_, foldPropositional, nenf, PFormula, simpcnf)
-- import PropExamples (Knows(K), mk_knows, Atom(P), N)
import FOL (pApp)
import Data.Function (on)
import Data.List as List
import Data.Map as Map hiding (fromList)
import Data.Set as Set
import Skolem (MyFormula)
import Test.HUnit
import Text.PrettyPrint.HughesPJClass (Pretty(pPrint), prettyShow, text)

data Atom = P String Integer deriving (Eq, Ord, Show)

instance Pretty Atom where
    pPrint (P s n) = text (s ++ if n == 0 then "" else show n)

class NumAtom atom where
    ma :: Integer -> atom
    ai :: atom -> Integer

instance NumAtom Atom where
    ma = P "p_"
    ai (P _ n) = n

instance HasFixity Atom where
    fixity _ = botFixity

-- | Example (p. 74)
test01 :: Test
test01 = TestCase $ assertEqual "cnf test (p. 74)"
                                "(p[]∨q[]∨r[])∧(p[]∨¬q[]∨¬r[])∧(q[]∨¬p[]∨¬r[])∧(r[]∨¬p[]∨¬q[])"
                                (let (p, q, r) = (pApp "p" [], pApp "q" [], pApp "r" []) in
                                 prettyShow (cnf' (p .<=>. (q .<=>. r)) :: MyFormula))

mkprop :: forall pf atom. (IsPropositional pf atom, NumAtom atom) => Integer -> (pf, Integer)
mkprop n = (atomic (ma n :: atom), n + 1)

-- |  Core definitional CNF procedure.
maincnf :: (NumAtom atom, IsPropositional pf atom, Ord pf) => (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
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

defstep :: (IsPropositional pf atom, NumAtom atom, Ord pf) => (pf -> pf -> pf) -> (pf, pf) -> (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
defstep op (p,q) (_fm, defs, n) =
  let (fm1,defs1,n1) = maincnf (p,defs,n) in
  let (fm2,defs2,n2) = maincnf (q,defs1,n1) in
  let fm' = op fm1 fm2 in
  case Map.lookup fm' defs2 of
    Just _ -> (fm', defs2, n2)
    Nothing -> let (v,n3) = mkprop n2 in (v, Map.insert v (v .<=>. fm') defs2,n3)

-- | Make n large enough that "v_m" won't clash with s for any m >= n
max_varindex :: NumAtom atom =>  atom -> Integer -> Integer
max_varindex atom n = max n (ai atom)

-- | Overall definitional CNF.
{-
mk_defcnf :: forall pf lit atom. (IsPropositional pf atom, IsLiteral lit atom, NumAtom atom, Ord lit) =>
             ((pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)) -> pf -> Set.Set (Set.Set lit)
-}
mk_defcnf :: (IsPropositional formula atom, IsPropositional lit atom, Ord lit, NumAtom atom) => ((formula, Map pf pf, Integer) -> (lit, Map pf lit, Integer)) -> formula -> Set (Set lit)
mk_defcnf fn fm =
  let fm' = nenf fm in
  let n = 1 + overatoms max_varindex fm' 0 in
  let (fm'',defs,_) = fn (fm',Map.empty,n) in
  let (deflist {- :: [pf]-}) = Map.elems defs in
  Set.unions (simpcnf fm'' : List.map simpcnf deflist)

-- defcnf1 :: forall pf lit atom. (IsPropositional pf atom, IsLiteral lit atom, NumAtom atom, Ord lit) => lit -> atom -> pf -> pf
-- defcnf1 :: (IsPropositional pf atom, IsPropositional pf atom, NumAtom atom) => pf -> pf
defcnf1 :: (HasBoolean pf, Ord pf, IsPropositional pf atom, NumAtom atom, IsLiteral pf atom) => pf -> pf
defcnf1 fm = cnf_ (mk_defcnf maincnf fm)

-- Example.
test02 :: Test
test02 =
    let fm :: PFormula Atom
        fm = let (p, q, r, s) = (atomic (P "p" 0), atomic (P "q" 0), atomic (P "r" 0), atomic (P "s" 0)) in
             (p .|. (q .&. ((.~.) r))) .&. s in
    TestCase $ assertEqual "defcnf1 (p. 77)"
                           (sortBy (compare `on` length) . sort . List.map sort $
                            [["p","p_1","¬p_2"],
                             ["p_1","r","¬q"],
                             ["p_2","¬p"],
                             ["p_2","¬p_1"],
                             ["p_2","¬p_3"],
                             ["p_3"],
                             ["p_3","¬p_2","¬s"],
                             ["q","¬p_1"],
                             ["s","¬p_3"],
                             ["¬p_1","¬r"]])
                           (strings (mk_defcnf maincnf fm))

strings :: Pretty a => Set (Set a) -> [[String]]
strings ss = sortBy (compare `on` length) . sort . Set.toList $ Set.map (sort . Set.toList . Set.map prettyShow) ss
{-
START_INTERACTIVE;;
defcnf1 <<(p \/ (q /\ ~r)) /\ s>>;;
END_INTERACTIVE;;
-}

-- | Version tweaked to exploit initial structure.
subcnf :: (IsPropositional pf atom, NumAtom atom) =>
          ((pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer))
       -> (pf -> pf -> pf)
       -> pf
       -> pf
       -> (pf, Map.Map pf pf, Integer)
       -> (pf, Map.Map pf pf, Integer)
subcnf sfn op p q (_fm,defs,n) =
  let (fm1,defs1,n1) = sfn (p,defs,n) in
  let (fm2,defs2,n2) = sfn (q,defs1,n1) in
  (op fm1 fm2, defs2, n2)

orcnf :: (NumAtom atom, IsPropositional pf atom, Ord pf) => (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
orcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:|:) q) = subcnf orcnf (.|.) p q trip
      co _ = maincnf trip

andcnf :: (IsPropositional pf atom, NumAtom atom, Ord pf) => (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
andcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> orcnf trip) (\ _ -> orcnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf (.&.) p q trip
      co _ = orcnf trip

defcnfs :: (IsPropositional pf atom, Ord pf, NumAtom atom) => pf -> Set (Set pf)
defcnfs fm = mk_defcnf andcnf fm

-- Don't we need an IsPropositional (Set (Set pf)) instance for this to work?
defcnf2 :: (IsPropositional pf atom, IsPropositional (Set (Set pf)) atom, Ord pf, NumAtom atom) =>
           pf -> Set (Set pf)
defcnf2 fm = cnf' (defcnfs fm)

-- Examples.
{-
START_INTERACTIVE;;
defcnf <<(p \/ (q /\ ~r)) /\ s>>;;
END_INTERACTIVE;;
-}

-- | Version that guarantees 3-CNF.
andcnf3 :: (IsPropositional pf atom, NumAtom atom, Ord pf) => (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
andcnf3 trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf3 (.&.) p q trip
      co _ = maincnf trip

-- defcnf3 :: forall pf lit atom. (IsPropositional pf atom, IsLiteral lit atom, NumAtom atom, Ord lit) => lit -> atom -> pf -> pf
defcnf3 :: (IsPropositional pf atom, IsPropositional (Set (Set pf)) atom, Ord pf, NumAtom atom) =>
           pf -> Set (Set pf)
defcnf3 fm = cnf' (mk_defcnf andcnf3 fm)

tests :: Test
tests = TestList [test01, test02]
