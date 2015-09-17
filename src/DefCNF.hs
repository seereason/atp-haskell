-- | Definitional CNF.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE CPP #-}
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
    -- * Instance
    , Atom(N)
    -- * Tests
#ifndef NOTESTS
    , tests
#endif
    ) where

import Data.Function (on)
import Data.List as List
import Data.Map as Map hiding (fromList)
import Data.Set as Set

import Formulas as P
import Lit (IsLiteral)
import Pretty (HasFixity(fixity), leafFixity, Pretty, prettyShow, text)
import Prop as P (IsPropositional, cnf', foldPropositional, nenf, simpcnf, list_conj, list_disj)

#ifndef NOTESTS
import Test.HUnit
import Prop (Prop(P), PFormula)
#endif

#ifndef NOTESTS
-- | Example (p. 74)
test01 :: Test
test01 = TestCase $ assertEqual "cnf test (p. 74)"
                                "(p∨q∨r)∧(p∨¬q∨¬r)∧(q∨¬p∨¬r)∧(r∨¬p∨¬q)"
                                (let [p, q, r] = (List.map (atomic . P) ["p", "q", "r"]) in
                                 prettyShow (cnf' (p .<=>. (q .<=>. r)) :: PFormula Prop))
#endif

class NumAtom atom where
    ma :: Integer -> atom
    ai :: atom -> Integer

data Atom = N String Integer deriving (Eq, Ord, Show)

instance IsAtom Atom where
    prettyAtom _ _ (N s n) = text (s ++ if n == 0 then "" else show n)

instance NumAtom Atom where
    ma = N "p_"
    ai (N _ n) = n

instance HasFixity Atom where
    fixity _ = leafFixity

-- | Make a stylized variable and update the index.
mkprop :: forall pf atom. (IsPropositional pf atom, NumAtom atom) => Integer -> (pf, Integer)
mkprop n = (atomic (ma n :: atom), n + 1)

-- |  Core definitional CNF procedure.
maincnf :: (IsPropositional pf atom, NumAtom atom) => (pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer)
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

defstep :: (IsPropositional pf atom, NumAtom atom) =>
           (pf -> pf -> pf) -> (pf, pf) -> (pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer)
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
defcnf1 :: forall pf atom. (IsPropositional pf atom, NumAtom atom) => pf -> pf
defcnf1 fm = list_conj (Set.map list_disj (mk_defcnf id maincnf fm))

mk_defcnf :: forall formula atom lit atom2. (IsPropositional formula atom, NumAtom atom, IsLiteral lit atom2) =>
             (atom -> atom2)
          -> ((formula, Map formula formula, Integer) -> (formula, Map formula formula, Integer))
          -> formula -> Set (Set lit)
mk_defcnf ca fn fm =
  let (fm' :: formula) = nenf fm in
  let n = 1 + overatoms max_varindex fm' 0 in
  let (fm'',defs,_) = fn (fm',Map.empty,n) in
  let (deflist :: [formula]) = Map.elems defs in
  Set.unions (List.map (simpcnf ca :: formula -> Set (Set lit)) (fm'' : deflist))

#ifndef NOTESTS
testfm :: PFormula Atom
testfm = let (p, q, r, s) = (atomic (N "p" 0), atomic (N "q" 0), atomic (N "r" 0), atomic (N "s" 0)) in
     (p .|. (q .&. ((.~.) r))) .&. s

-- Example.
{-
START_INTERACTIVE;;
defcnf1 <<(p \/ (q /\ ~r)) /\ s>>;;
END_INTERACTIVE;;
-}

test02 :: Test
test02 =
    let input = strings (mk_defcnf id maincnf testfm :: Set (Set (PFormula Atom)))
        expected = [["p_3"],
                    ["p_2","¬p"],
                    ["p_2","¬p_1"],
                    ["p_2","¬p_3"],
                    ["q","¬p_1"],
                    ["s","¬p_3"],
                    ["¬p_1","¬r"],
                    ["p","p_1","¬p_2"],
                    ["p_1","r","¬q"],
                    ["p_3","¬p_2","¬s"]] in
    TestCase $ assertEqual "defcnf1 (p. 77)" expected input

strings :: Pretty a => Set (Set a) -> [[String]]
strings ss = sortBy (compare `on` length) . sort . Set.toList $ Set.map (sort . Set.toList . Set.map prettyShow) ss
#endif

-- | Version tweaked to exploit initial structure.
defcnf2 :: (IsPropositional formula atom, NumAtom atom) => formula -> formula
defcnf2 fm = list_conj (Set.map list_disj (defcnfs fm))

defcnfs :: (IsPropositional pf atom, NumAtom atom) => pf -> Set (Set pf)
defcnfs fm = mk_defcnf id andcnf fm

andcnf :: (IsPropositional pf atom, NumAtom atom) => (pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer)
andcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> orcnf trip) (\ _ -> orcnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf (.&.) p q trip
      co _ = orcnf trip

orcnf :: (IsPropositional pf atom, NumAtom atom) => (pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer)
orcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:|:) q) = subcnf orcnf (.|.) p q trip
      co _ = maincnf trip

subcnf :: (IsPropositional pf atom, NumAtom atom) =>
          ((pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer))
       -> (pf -> pf -> pf)
       -> pf
       -> pf
       -> (pf, Map pf pf, Integer)
       -> (pf, Map pf pf, Integer)
subcnf sfn op p q (_fm,defs,n) =
  let (fm1,defs1,n1) = sfn (p,defs,n) in
  let (fm2,defs2,n2) = sfn (q,defs1,n1) in
  (op fm1 fm2, defs2, n2)

-- | Version that guarantees 3-CNF.
defcnf3 :: (IsPropositional formula atom, NumAtom atom, IsLiteral formula atom) => formula -> formula
defcnf3 = list_conj . Set.map list_disj . mk_defcnf id andcnf3

andcnf3 :: (IsPropositional pf atom, NumAtom atom) => (pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer)
andcnf3 trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf3 (.&.) p q trip
      co _ = maincnf trip

#ifndef NOTESTS
test03 :: Test
test03 =
    let input = strings (mk_defcnf id andcnf3 testfm :: Set (Set (PFormula Atom)))
        expected = [["p_2"],
                    ["s"],
                    ["p_2","¬p"],
                    ["p_2","¬p_1"],
                    ["q","¬p_1"],
                    ["¬p_1","¬r"],
                    ["p","p_1","¬p_2"],
                    ["p_1","r","¬q"]] in
    TestCase $ assertEqual "defcnf1 (p. 77)" expected input

tests :: Test
tests = TestList [test01, test02, test03]
#endif
