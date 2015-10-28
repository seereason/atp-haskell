-- | First order logic with equality.
--
-- Copyright (co) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}

module Equal
    ( function_congruence
    , equalitize
#ifndef NOTESTS
    -- * Tests
    , testEqual
#endif
    ) where

import Data.List as List (foldr, map)
import Data.Set as Set
import Data.String (IsString(fromString))
import Formulas ((∧), (⇒), IsFormula(atomic), atom_union)
import FOL ((.=.), HasFunctions(funcs), HasApply(applyPredicate), HasApplyAndEquate(foldEquate),
            IsQuantified(..), (∀), IsTerm(..))
import Lib ((∅))
import Prelude hiding ((*))
#ifndef NOTESTS
import Data.Map as Map (fromList, Map)
import FOL ((∃), pApp, Predicate, V)
import Formulas ((.&.), (.=>.), (.<=>.))
import Lib (Failing (Success, Failure))
import Meson (meson)
import Pretty (assertEqual', prettyShow)
import Skolem
import Tableaux (Depth(Depth))
import Test.HUnit
#endif

-- is_eq :: (IsQuantified fof atom v, IsAtomWithEquate atom p term) => fof -> Bool
-- is_eq = foldFirstOrder (\ _ _ _ -> False) (\ _ -> False) (\ _ -> False) (foldAtomEq (\ _ _ -> False) (\ _ -> False) (\ _ _ -> True))
--
-- mk_eq :: (IsQuantified fof atom v, IsAtomWithEquate atom p term) => term -> term -> fof
-- mk_eq = (.=.)
--
-- dest_eq :: (IsQuantified fof atom v, IsAtomWithEquate atom p term) => fof -> Failing (term, term)
-- dest_eq fm =
--     foldFirstOrder (\ _ _ _ -> err) (\ _ -> err) (\ _ -> err) at fm
--     where
--       at = foldAtomEq (\ _ _ -> err) (\ _ -> err) (\ s t -> Success (s, t))
--       err = Failure ["dest_eq: not an equation"]
--
-- lhs :: (IsQuantified fof atom v, IsAtomWithEquate atom p term) => fof -> Failing term
-- lhs eq = dest_eq eq >>= return . fst
-- rhs :: (IsQuantified fof atom v, IsAtomWithEquate atom p term) => fof -> Failing term
-- rhs eq = dest_eq eq >>= return . snd

-- | The set of predicates in a formula.
-- predicates :: (IsQuantified formula atom v, IsAtomWithEquate atom p term, Ord atom, Ord p) => formula -> Set atom
predicates :: IsFormula formula r => formula -> Set r
predicates fm = atom_union Set.singleton fm

-- | Code to generate equate axioms for functions.
function_congruence :: forall fof atom term v p f.
                       (IsQuantified fof atom v, HasApplyAndEquate atom p term, IsTerm term v f, Ord fof) =>
                       (f, Int) -> Set fof
function_congruence (_,0) = (∅)
function_congruence (f,n) =
    Set.singleton (List.foldr (∀) (ant ⇒ con) (argnames_x ++ argnames_y))
    where
      argnames_x :: [v]
      argnames_x = List.map (\ m -> fromString ("x" ++ show m)) [1..n]
      argnames_y :: [v]
      argnames_y = List.map (\ m -> fromString ("y" ++ show m)) [1..n]
      args_x = List.map vt argnames_x
      args_y = List.map vt argnames_y
      ant = foldr1 (∧) (List.map (uncurry (.=.)) (zip args_x args_y))
      con = fApp f args_x .=. fApp f args_y

-- | And for predicates.
predicate_congruence :: (IsQuantified fof atom v, HasApplyAndEquate atom p term, IsTerm term v f, Ord p) =>
                        atom -> Set fof
predicate_congruence =
    foldEquate (\_ _ _ -> Set.empty) (\p ts -> ap p (length ts))
    where
      ap _ 0 = Set.empty
      ap p n = Set.singleton (List.foldr (∀) (ant ⇒ con) (argnames_x ++ argnames_y))
          where
            argnames_x = List.map (\ m -> fromString ("x" ++ show m)) [1..n]
            argnames_y = List.map (\ m -> fromString ("y" ++ show m)) [1..n]
            args_x = List.map vt argnames_x
            args_y = List.map vt argnames_y
            ant = foldr1 (∧) (List.map (uncurry (.=.)) (zip args_x args_y))
            con = atomic (applyPredicate p args_x) ⇒ atomic (applyPredicate p args_y)

-- | Hence implement logic with equate just by adding equate "axioms".
equivalence_axioms :: forall fof atom term v p f. (IsQuantified fof atom v, HasApplyAndEquate atom p term, IsTerm term v f, Ord fof) => Set fof
equivalence_axioms =
    Set.fromList
    [(∀) "x" (x .=. x),
     (∀) "x" ((∀) "y" ((∀) "z" (x .=. y ∧ x .=. z ⇒ y .=. z)))]
    where
      x :: term
      x = vt (fromString "x")
      y :: term
      y = vt (fromString "y")
      z :: term
      z = vt (fromString "z")

equalitize :: forall formula atom term v p f.
              (IsQuantified formula atom v, IsFormula formula atom, HasApplyAndEquate atom p term, HasFunctions formula f, HasFunctions term f, Ord p, Show p, IsTerm term v f, Ord formula, Ord atom, Ord f) =>
              formula -> formula
equalitize fm =
    if Set.null eqPreds then fm else foldr1 (∧) (Set.toList axioms) ⇒ fm
    where
      axioms = Set.fold (Set.union . function_congruence)
                        (Set.fold (Set.union . predicate_congruence) equivalence_axioms otherPreds)
                        (funcs fm)
      (eqPreds, otherPreds) = Set.partition (foldEquate (\_ _ _ -> True) (\_ _ -> False)) (predicates fm)

#ifndef NOTESTS

-- -------------------------------------------------------------------------
-- Example.
-- -------------------------------------------------------------------------

test01 :: Test
test01 = TestCase $ assertEqual "function_congruence" expected input
    where input = List.map function_congruence [(fromString "f", 3 :: Int), (fromString "+",2)]
          expected :: [Set.Set MyFormula]
          expected = [Set.fromList
                      [(∀) x1
                       ((∀) x2
                        ((∀) x3
                         ((∀) y1
                          ((∀) y2
                           ((∀) y3 ((((vt x1) .=. (vt y1)) ∧ (((vt x2) .=. (vt y2)) ∧ ((vt x3) .=. (vt y3)))) ⇒
                                          ((fApp (fromString "f") [vt x1,vt x2,vt x3]) .=. (fApp (fromString "f") [vt y1,vt y2,vt y3]))))))))],
                      Set.fromList
                      [(∀) x1
                       ((∀) x2
                        ((∀) y1
                         ((∀) y2 ((((vt x1) .=. (vt y1)) ∧ ((vt x2) .=. (vt y2))) ⇒
                                        ((fApp (fromString "+") [vt x1,vt x2]) .=. (fApp (fromString "+") [vt y1,vt y2]))))))]]
          x1 = fromString "x1"
          x2 = fromString "x2"
          x3 = fromString "x3"
          y1 = fromString "y1"
          y2 = fromString "y2"
          y3 = fromString "y3"

-- -------------------------------------------------------------------------
-- A simple example (see EWD1266a and the application to Morley's theorem).
-- -------------------------------------------------------------------------

test02 :: Test
test02 = TestCase $ assertEqual' "equalitize 1 (p. 241)" (expected, expectedProof) input
    where input = (ewd, runSkolem (meson (Just (Depth 10)) ewd))
          ewd = equalitize fm :: MyFormula
          fm :: MyFormula
          fm = ((∀) "x" (fx ⇒ gx)) ∧
               ((∃) "x" fx) ∧
               ((∀) "x" ((∀) "y" (gx ∧ gy ⇒ x .=. y))) ⇒
               ((∀) "y" (gy ⇒ fy))
          fx = pApp' "f" [x]
          gx = pApp' "g" [x]
          fy = pApp' "f" [y]
          gy = pApp' "g" [y]
          x = vt "x"
          y = vt "y"
          z = vt "z"
          x1 = vt "x1"
          y1 = vt "y1"
          fx1 = pApp' "f" [x1]
          gx1 = pApp' "g" [x1]
          fy1 = pApp' "f" [y1]
          gy1 = pApp' "g" [y1]
          -- y1 = fromString "y1"
          -- z = fromString "z"
          expected =
              ((∀) "x" (x .=. x)) .&.
              ((∀) "x" ((∀) "y" ((∀) "z" (x .=. y .&. x .=. z .=>. y .=. z)))) .&.
              ((∀) "x1" ((∀) "y1" (x1 .=. y1 .=>. fx1 .=>. fy1))) .&.
              ((∀) "x1" ((∀) "y1" (x1 .=. y1 .=>. gx1 .=>. gy1))) .=>.
              ((∀) "x" (fx .=>. gx)) .&.
              ((∃) "x" (fx)) .&.
              ((∀) "x" ((∀) "y" (gx .&. gy .=>. x .=. y))) .=>.
              ((∀) "y" (gy .=>. fy))
{-
          -- I don't yet know if this is right.  Almost certainly not.
          expectedProof = Set.fromList [Success ((Map.fromList [("_0",vt "_1")],0,2),1),
                                        Success ((Map.fromList [("_0",vt "_2"),("_1",vt "_2")],0,3),1),
                                        Success ((Map.fromList [("_0",fApp (Skolem 1) [] :: MyTerm)],0,1),1),
                                        Success ((Map.fromList [("_0",fApp (Skolem 2) [] :: MyTerm)],0,1),1)]

          expected = ("<<(forall x. x = x) /\ " ++
                      "    (forall x y z. x = y /\ x = z ==> y = z) /\ " ++
                      "    (forall x1 y1. x1 = y1 ==> f(x1) ==> f(y1)) /\ " ++
                      "    (forall x1 y1. x1 = y1 ==> g(x1) ==> g(y1)) ==> " ++
                      "    (forall x. f(x) ==> g(x)) /\ " ++
                      "    (exists x. f(x)) /\ (forall x y. g(x) /\ g(y) ==> x = y) ==> " ++
                      "    (forall y. g(y) ==> f(y))>> ")
-}
          expectedProof =
              Set.fromList [Success ((Map.fromList [(fromString "_0",fApp (toSkolem "x") []),
                                                    (fromString "_1",fApp (toSkolem "y") []),
                                                    (fromString "_2",fApp (toSkolem "x") []),
                                                    (fromString "_3",fApp (toSkolem "y") []),
                                                    (fromString "_4",fApp (toSkolem "x") [])],0,5),Depth 6)]
{-
          expectedProof =
              Set.singleton (Success ((Map.fromList [(fromString "_0",vt' "_2"),
                                                     (fromString "_1",fApp (toSkolem "x") []),
                                                     (fromString "_2",vt' "_4"),
                                                     (fromString "_3",fApp (toSkolem "x") []),
                                                     (fromString "_4",fApp (toSkolem "x") []),
                                                     (fromString "_5",fApp (toSkolem "x") [])], 0, 6), 5))
          fApp' :: String -> [term] -> term
          fApp' s ts = fApp (fromString s) ts
          for_all' s = for_all (fromString s)
          exists' s = exists (fromString s)
-}
          pApp' :: String -> [MyTerm] -> MyFormula
          pApp' s ts = pApp (fromString s :: Predicate) ts
          --vt' :: String -> MyTerm
          --vt' s = vt (fromString s)

-- | Wishnu Prasetya's example (even nicer with an "exists unique" primitive).
wishnu :: MyFormula
wishnu = ((∃) ("x") ((x .=. f[g[x]]) ∧ (∀) ("x'") ((x' .=. f[g[x']]) ⇒ (x .=. x')))) .<=>.
         ((∃) ("y") ((y .=. g[f[y]]) ∧ (∀) ("y'") ((y' .=. g[f[y']]) ⇒ (y .=. y'))))
    where
      x = vt "x"
      y = vt "y"
      x' = vt "x'"
      y' = vt "y"
      f terms = fApp (fromString "f") terms
      g terms = fApp (fromString "g") terms

test03 :: Test
test03 = TestLabel "equalitize 2" $ TestCase $ assertEqual "equalitize 2 (p. 241)" (prettyShow expected, expectedProof) input
    where -- It should finish with Depth 16, but that takes a long time.
          input = (prettyShow (equalitize wishnu), runSkolem (meson (Just (Depth 16)) wishnu))
          x = vt "x" :: MyTerm
          x1 = vt "x1"
          y = vt "y"
          y1 = vt "y1"
          z = vt "z"
          x' = vt "x'"
          y' = vt "y"
          f terms = fApp (fromString "f") terms
          g terms = fApp (fromString "g") terms
          expected :: MyFormula
          expected =
                     ((∀) "x" (x .=. x)) .&.
                     ((∀) "x" . (∀) "y" . (∀) "z" $ (x .=. y .&. x .=. z .=>. y .=. z)) .&.
                     ((∀) "x1" . (∀) "y1" $ (x1 .=. y1 .=>. f[x1] .=. f[y1])) .&.
                     ((∀) "x1" . (∀) "y1" $ (x1 .=. y1 .=>. g[x1] .=. g[y1])) .=>.
                     (((∃) "x" $ x .=. f[g[x]] .&. ((∀) "x'" $ (x' .=. f[g[x']] .=>. x .=. x'))) .<=>.
                      ((∃) "y" $ y .=. g[f[y]] .&. ((∀) "y'" $ (y' .=. g[f[y']] .=>. y .=. y'))))
          expectedProof =
              Set.fromList [Failure ["Not sure what this should be"]]
{-
              Set.fromList [Success ((Map.fromList [("_0",vt "_1")],0,2 :: Map String MyTerm),1),
                            Success ((Map.fromList [("_0",vt "_1"),("_1",fApp "f" [fApp "g" [vt "_0"]])],0,2),1),
                            Success ((Map.fromList [("_0",vt "_1"),("_1",fApp "g" [fApp "f" [vt "_0"]])],0,2),1),
                            Success ((Map.fromList [("_0",vt "_1"),("_2",fApp (fromSkolem 2) [vt "_0"])],0,3),1),
                            Success ((Map.fromList [("_0",vt "_2"),("_1",vt "_2")],0,3),1)] -}

-- -------------------------------------------------------------------------
-- More challenging equational problems. (Size 18, 61814 seconds.)
-- -------------------------------------------------------------------------

test04 :: Test
test04 = TestCase $ assertEqual "equalitize 3 (p. 248)" (prettyShow expected, expectedProof) input
    where
      input = (prettyShow (equalitize fm), runSkolem (meson (Just (Depth 20)) . equalitize $ fm))
      fm :: MyFormula
      fm = ((∀) "x" . (∀) "y" . (∀) "z") ((*) [x', (*) [y', z']] .=. (*) [((*) [x', y']), z']) ∧
           (∀) "x" ((*) [one, x'] .=. x') ∧
           (∀) "x" ((*) [i [x'], x'] .=. one) ⇒
           (∀) "x" ((*) [x', i [x']] .=. one)
      x' = vt "x" :: MyTerm
      y' = vt "y" :: MyTerm
      z' = vt "z" :: MyTerm
      (*) = fApp (fromString "*")
      i = fApp (fromString "i")
      one = fApp (fromString "1") []
      expected :: MyFormula
      expected =
          ((∀) "x" ((vt "x") .=. (vt "x")) .&.
           ((∀) "x" ((∀) "y" ((∀) "z" ((((vt "x") .=. (vt "y")) .&. ((vt "x") .=. (vt "z"))) .=>. ((vt "y") .=. (vt "z"))))) .&.
            ((∀) "x1" ((∀) "x2" ((∀) "y1" ((∀) "y2" ((((vt "x1") .=. (vt "y1")) .&. ((vt "x2") .=. (vt "y2"))) .=>.
                                                                     ((fApp "*" [vt "x1",vt "x2"]) .=. (fApp "*" [vt "y1",vt "y2"])))))) .&.
             (∀) "x1" ((∀) "y1" (((vt "x1") .=. (vt "y1")) .=>. ((fApp "i" [vt "x1"]) .=. (fApp "i" [vt "y1"]))))))) .=>.
          ((((∀) "x" ((∀) "y" ((∀) "z" ((fApp "*" [vt "x",fApp "*" [vt "y",vt "z"]]) .=. (fApp "*" [fApp "*" [vt "x",vt "y"],vt "z"])))) .&.
             (∀) "x" ((fApp "*" [fApp "1" [],vt "x"]) .=. (vt "x"))) .&.
            (∀) "x" ((fApp "*" [fApp "i" [vt "x"],vt "x"]) .=. (fApp "1" []))) .=>.
           (∀) "x" ((fApp "*" [vt "x",fApp "i" [vt "x"]]) .=. (fApp "1" [])))
      expectedProof :: Set.Set (Failing ((Map V MyTerm, Int, Int), Depth))
      expectedProof =
          Set.fromList
                 [Success ((Map.fromList
                                   [( "_0",  (*) [one, vt' "_3"]),
                                    ( "_1",  (*) [fApp (toSkolem "x") [],i [fApp (toSkolem "x") []]]),
                                    ( "_2",  one),
                                    ( "_3",  (*) [fApp (toSkolem "x") [],i [fApp (toSkolem "x") []]]),
                                    ( "_4",  vt' "_8"),
                                    ( "_5",  (*) [one, vt' "_3"]),
                                    ( "_6",  one),
                                    ( "_7",  vt' "_11"),
                                    ( "_8",  vt' "_12"),
                                    ( "_9",  (*) [one, vt' "_3"]),
                                    ("_10", (*) [vt' "_13",(*) [vt' "_14", vt' "_15"]]),
                                    ("_11", (*) [(*) [vt' "_13", vt' "_14"], vt' "_15"]),
                                    ("_12", (*) [vt' "_19", vt' "_18"]),
                                    ("_13", vt' "_16"),
                                    ("_14", vt' "_21"),
                                    ("_15", (*) [vt' "_22", vt' "_23"]),
                                    ("_16", vt' "_20"),
                                    ("_17", (*) [vt' "_14", vt' "_15"]),
                                    ("_18", (*) [(*) [vt' "_21", vt' "_22"], vt' "_23"]),
                                    ("_19", vt' "_20"),
                                    ("_20", i [vt' "_28"]),
                                    ("_21", vt' "_28"),
                                    ("_22", fApp (toSkolem "x") []),
                                    ("_23", i [fApp (toSkolem "x") []]),
                                    ("_24", (*) [vt' "_13", vt' "_14"]),
                                    ("_25", (*) [vt' "_22", vt' "_23"]),
                                    ("_26", (*) [fApp (toSkolem "x") [],i [fApp (toSkolem "x") []]]),
                                    ("_27", one),
                                    ("_28", vt' "_30"),
                                    ("_29", (*) [vt' "_22", vt' "_23"]),
                                    ("_30", (*) [(*) [vt' "_21", vt' "_22"], vt' "_23"])],
                            0,31),Depth 13)]
      vt' = vt . fromString

testEqual :: Test
testEqual = TestLabel "Equal" (TestList [test01, test02 {-, test03, test04-}])

#endif

{-
functions' :: (IsFormula formula atom, Ord f) => (atom -> Set (f, Int)) -> formula -> Set (f, Arity)
functions' fa fm = overatoms (\ a s -> Set.union s (fa a)) fm Set.empty

funcsAtomEq :: (IsAtomWithEquate atom p term, HasFunctions term f, IsTerm term v f, Ord f) => atom -> Set (f, Arity)
funcsAtomEq = foldEquate (\ _ ts -> Set.unions (List.map funcs ts)) (\ t1 t2 -> Set.union (funcs t1) (funcs t2))
-}

-- -------------------------------------------------------------------------
-- Other variants not mentioned in book.
-- -------------------------------------------------------------------------

{-
{- ************

(meson ** equalitize)
 <<(forall x y z. x * (y * z) = (x * y) * z) /\
   (forall x. 1 * x = x) /\
   (forall x. x * 1 = x) /\
   (forall x. x * x = 1)
   ==> forall x y. x * y  = y * x>>;;

-- -------------------------------------------------------------------------
-- With symmetry at leaves and one-sided congruences (Size = 16, 54659 s).
-- -------------------------------------------------------------------------

let fm =
 <<(forall x. x = x) /\
   (forall x y z. x * (y * z) = (x * y) * z) /\
   (forall x y z. =((x * y) * z,x * (y * z))) /\
   (forall x. 1 * x = x) /\
   (forall x. x = 1 * x) /\
   (forall x. i(x) * x = 1) /\
   (forall x. 1 = i(x) * x) /\
   (forall x y. x = y ==> i(x) = i(y)) /\
   (forall x y z. x = y ==> x * z = y * z) /\
   (forall x y z. x = y ==> z * x = z * y) /\
   (forall x y z. x = y /\ y = z ==> x = z)
   ==> forall x. x * i(x) = 1>>;;

time meson fm;;

-- -------------------------------------------------------------------------
-- Newer version of stratified equalities.
-- -------------------------------------------------------------------------

let fm =
 <<(forall x y z. axiom(x * (y * z),(x * y) * z)) /\
   (forall x y z. axiom((x * y) * z,x * (y * z)) /\
   (forall x. axiom(1 * x,x)) /\
   (forall x. axiom(x,1 * x)) /\
   (forall x. axiom(i(x) * x,1)) /\
   (forall x. axiom(1,i(x) * x)) /\
   (forall x x'. x = x' ==> cchain(i(x),i(x'))) /\
   (forall x x' y y'. x = x' /\ y = y' ==> cchain(x * y,x' * y'))) /\
   (forall s t. axiom(s,t) ==> achain(s,t)) /\
   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\
   (forall x x' u. x = x' /\ achain(i(x'),u) ==> cchain(i(x),u)) /\
   (forall x x' y y' u.
        x = x' /\ y = y' /\ achain(x' * y',u) ==> cchain(x * y,u)) /\
   (forall s t. cchain(s,t) ==> s = t) /\
   (forall s t. achain(s,t) ==> s = t) /\
   (forall t. t = t)
   ==> forall x. x * i(x) = 1>>;;

time meson fm;;

let fm =
 <<(forall x y z. axiom(x * (y * z),(x * y) * z)) /\
   (forall x y z. axiom((x * y) * z,x * (y * z)) /\
   (forall x. axiom(1 * x,x)) /\
   (forall x. axiom(x,1 * x)) /\
   (forall x. axiom(i(x) * x,1)) /\
   (forall x. axiom(1,i(x) * x)) /\
   (forall x x'. x = x' ==> cong(i(x),i(x'))) /\
   (forall x x' y y'. x = x' /\ y = y' ==> cong(x * y,x' * y'))) /\
   (forall s t. axiom(s,t) ==> achain(s,t)) /\
   (forall s t. cong(s,t) ==> cchain(s,t)) /\
   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\
   (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\
   (forall s t. cchain(s,t) ==> s = t) /\
   (forall s t. achain(s,t) ==> s = t) /\
   (forall t. t = t)
   ==> forall x. x * i(x) = 1>>;;

time meson fm;;

-- -------------------------------------------------------------------------
-- Showing congruence closure.
-- -------------------------------------------------------------------------

let fm = equalitize
 <<forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c>>;;

time meson fm;;

let fm =
 <<axiom(f(f(f(f(f(c))))),c) /\
   axiom(c,f(f(f(f(f(c)))))) /\
   axiom(f(f(f(c))),c) /\
   axiom(c,f(f(f(c)))) /\
   (forall s t. axiom(s,t) ==> achain(s,t)) /\
   (forall s t. cong(s,t) ==> cchain(s,t)) /\
   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\
   (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\
   (forall s t. cchain(s,t) ==> s = t) /\
   (forall s t. achain(s,t) ==> s = t) /\
   (forall t. t = t) /\
   (forall x y. x = y ==> cong(f(x),f(y)))
   ==> f(c) = c>>;;

time meson fm;;

-- -------------------------------------------------------------------------
-- With stratified equalities.
-- -------------------------------------------------------------------------

let fm =
 <<(forall x y z. eqA (x * (y * z),(x * y) * z)) /\
   (forall x y z. eqA ((x * y) * z)) /\
   (forall x. eqA (1 * x,x)) /\
   (forall x. eqA (x,1 * x)) /\
   (forall x. eqA (i(x) * x,1)) /\
   (forall x. eqA (1,i(x) * x)) /\
   (forall x. eqA (x,x)) /\
   (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\
   (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\
   (forall x y. eqT (x,y) ==> eqC (i(x),i(y))) /\
   (forall w x y z. eqA (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqA (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqA (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqC (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqC (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqC (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqT (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqT (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqT (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\
   (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z))
   ==> forall x. eqT (x * i(x),1)>>;;

-- -------------------------------------------------------------------------
-- With transitivity chains...
-- -------------------------------------------------------------------------

let fm =
 <<(forall x y z. eqA (x * (y * z),(x * y) * z)) /\
   (forall x y z. eqA ((x * y) * z)) /\
   (forall x. eqA (1 * x,x)) /\
   (forall x. eqA (x,1 * x)) /\
   (forall x. eqA (i(x) * x,1)) /\
   (forall x. eqA (1,i(x) * x)) /\
   (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\
   (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\
   (forall w x y. eqA (w,x) ==> eqC (w * y,x * y)) /\
   (forall w x y. eqC (w,x) ==> eqC (w * y,x * y)) /\
   (forall x y z. eqA (y,z) ==> eqC (x * y,x * z)) /\
   (forall x y z. eqC (y,z) ==> eqC (x * y,x * z)) /\
   (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z))
   ==> forall x. eqT (x * i(x),1) \/ eqC (x * i(x),1)>>;;

time meson fm;;

-- -------------------------------------------------------------------------
-- Enforce canonicity (proof size = 20).
-- -------------------------------------------------------------------------

let fm =
 <<(forall x y z. eq1(x * (y * z),(x * y) * z)) /\
   (forall x y z. eq1((x * y) * z,x * (y * z))) /\
   (forall x. eq1(1 * x,x)) /\
   (forall x. eq1(x,1 * x)) /\
   (forall x. eq1(i(x) * x,1)) /\
   (forall x. eq1(1,i(x) * x)) /\
   (forall x y z. eq1(x,y) ==> eq1(x * z,y * z)) /\
   (forall x y z. eq1(x,y) ==> eq1(z * x,z * y)) /\
   (forall x y z. eq1(x,y) /\ eq2(y,z) ==> eq2(x,z)) /\
   (forall x y. eq1(x,y) ==> eq2(x,y))
   ==> forall x. eq2(x,i(x))>>;;

time meson fm;;

***************** -}
END_INTERACTIVE;;
-}
