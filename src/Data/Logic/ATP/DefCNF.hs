-- | Definitional CNF.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Logic.ATP.DefCNF
    ( NumAtom(ma, ai)
    , defcnfs
    , defcnf1
    , defcnf2
    , defcnf3
    -- * Instance
    , Atom(N)
    -- * Tests
    , testDefCNF
    ) where

import Data.Function (on)
import Data.List as List
import Data.Logic.ATP.Formulas as P
import Data.Logic.ATP.Lit ((.~.), (¬), convertLiteral, IsLiteral, JustLiteral, LFormula)
import Data.Logic.ATP.Pretty (assertEqual', HasFixity, Pretty(pPrint), prettyShow, text)
import Data.Logic.ATP.Prop (cnf', foldPropositional, IsPropositional(foldPropositional'), JustPropositional,
                            list_conj, list_disj, nenf, PFormula, Prop(P), simpcnf,
                            (∨), (∧), (.<=>.), (.&.), (.|.), BinOp(..))
import Data.Map.Strict as Map hiding (fromList)
import Data.Set as Set
import Test.HUnit

-- | Example (p. 74)
test01 :: Test
test01 =
    let p :: PFormula Prop
        q :: PFormula Prop
        r :: PFormula Prop
        [p, q, r] = (List.map (atomic . P) ["p", "q", "r"]) in
    TestCase $ assertEqual' "cnf test (p. 74)"
                 ((p∨q∨r)∧(p∨(¬)q∨(¬)r)∧(q∨(¬)p∨(¬)r)∧(r∨(¬)p∨(¬)q))
                 (cnf' (p .<=>. (q .<=>. r)) :: PFormula Prop)

class NumAtom atom where
    ma :: Integer -> atom
    ai :: atom -> Integer

data Atom = N String Integer deriving (Eq, Ord, Show)

instance Pretty Atom where
    pPrint (N s n) = text (s ++ if n == 0 then "" else show n)

instance NumAtom Atom where
    ma = N "p_"
    ai (N _ n) = n

instance HasFixity Atom

instance IsAtom Atom

-- | Make a stylized variable and update the index.
mkprop :: forall pf. (IsPropositional pf, NumAtom (AtomOf pf)) => Integer -> (pf, Integer)
mkprop n = (atomic (ma n :: AtomOf pf), n + 1)

-- |  Core definitional CNF procedure.
maincnf :: (IsPropositional pf, Ord pf, NumAtom (AtomOf pf)) => (pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer)
maincnf trip@(fm, _defs, _n) =
    foldPropositional' ho co ne tf at fm
    where
      ho _ = trip
      co p (:&:) q = defstep (.&.) (p,q) trip
      co p (:|:) q = defstep (.|.) (p,q) trip
      co p (:<=>:) q = defstep (.<=>.) (p,q) trip
      co _ (:=>:) _ = trip
      ne _ = trip
      tf _ = trip
      at _ = trip

defstep :: (IsPropositional pf, NumAtom (AtomOf pf), Ord pf) =>
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
defcnf1 :: forall pf. (IsPropositional pf, JustPropositional pf, NumAtom (AtomOf pf), Ord pf) => pf -> pf
defcnf1 = list_conj . Set.map (list_disj . Set.map (convertLiteral id)) . (mk_defcnf id maincnf :: pf -> Set (Set (LFormula (AtomOf pf))))

mk_defcnf :: forall pf lit.
             (IsPropositional pf, JustPropositional pf,
              IsLiteral lit, JustLiteral lit, Ord lit,
              NumAtom (AtomOf pf)) =>
             (AtomOf pf -> AtomOf lit)
          -> ((pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer))
          -> pf -> Set (Set lit)
mk_defcnf ca fn fm =
  let (fm' :: pf) = nenf fm in
  let n = 1 + overatoms max_varindex fm' 0 in
  let (fm'',defs,_) = fn (fm',Map.empty,n) in
  let (deflist :: [pf]) = Map.elems defs in
  Set.unions (List.map (simpcnf ca :: pf -> Set (Set lit)) (fm'' : deflist))

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
    let input = strings (mk_defcnf id maincnf testfm :: Set (Set (LFormula Atom)))
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

-- | Version tweaked to exploit initial structure.
defcnf2 :: (IsPropositional pf, JustPropositional pf, Ord pf, NumAtom (AtomOf pf)) => pf -> pf
defcnf2 fm = list_conj (Set.map (list_disj . Set.map (convertLiteral id)) (defcnfs fm))

defcnfs :: (IsPropositional pf, JustPropositional pf, Ord pf, NumAtom (AtomOf pf)) => pf -> Set (Set (LFormula (AtomOf pf)))
defcnfs fm = mk_defcnf id andcnf fm

andcnf :: (IsPropositional pf, JustPropositional pf, Ord pf, NumAtom (AtomOf pf)) => (pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer)
andcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> orcnf trip) (\ _ -> orcnf trip) (\ _ -> orcnf trip) fm
    where
      co p (:&:) q = subcnf andcnf (.&.) p q trip
      co _ _ _ = orcnf trip

orcnf :: (IsPropositional pf, JustPropositional pf, Ord pf, NumAtom (AtomOf pf)) => (pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer)
orcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co p (:|:) q = subcnf orcnf (.|.) p q trip
      co _ _ _ = maincnf trip

subcnf :: (IsPropositional pf, NumAtom (AtomOf pf)) =>
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
defcnf3 :: forall pf. (JustPropositional pf, Ord pf, NumAtom (AtomOf pf)) => pf -> pf
defcnf3 = list_conj . Set.map (list_disj . Set.map (convertLiteral id)) . (mk_defcnf id andcnf3 :: pf -> Set (Set (LFormula (AtomOf pf))))

andcnf3 :: (IsPropositional pf, JustPropositional pf, Ord pf, NumAtom (AtomOf pf)) => (pf, Map pf pf, Integer) -> (pf, Map pf pf, Integer)
andcnf3 trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co p (:&:) q = subcnf andcnf3 (.&.) p q trip
      co _ _ _ = maincnf trip

test03 :: Test
test03 =
    let input = strings (mk_defcnf id andcnf3 testfm :: Set (Set (LFormula Atom)))
        expected = [["p_2"],
                    ["s"],
                    ["p_2","¬p"],
                    ["p_2","¬p_1"],
                    ["q","¬p_1"],
                    ["¬p_1","¬r"],
                    ["p","p_1","¬p_2"],
                    ["p_1","r","¬q"]] in
    TestCase $ assertEqual "defcnf1 (p. 77)" expected input

testDefCNF :: Test
testDefCNF = TestLabel "DefCNF" (TestList [test01, test02, test03])
