{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeFamilies #-}
-- | First order logic with equality.
--
-- Copyright (co) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}

module Data.Logic.ATP.Equal
    ( function_congruence
    , equalitize
    -- * Tests
    , wishnu
    , testEqual
    ) where

import Data.Logic.ATP.Apply (functions, HasApply(TermOf, PredOf, applyPredicate), pApp)
import Data.Logic.ATP.Equate ((.=.), HasEquate(foldEquate))
import Data.Logic.ATP.Formulas (IsFormula(AtomOf, atomic), atom_union)
import Data.Logic.ATP.Lib ((∅), Depth(Depth), Failing (Success, Failure), timeMessage)
import Data.Logic.ATP.Meson (meson)
import Data.Logic.ATP.Pretty (assertEqual')
import Data.Logic.ATP.Prop ((.&.), (.=>.), (∧), (⇒))
import Data.Logic.ATP.Quantified ((∃), (∀), IsQuantified(..))
import Data.Logic.ATP.Parser (fof)
import Data.Logic.ATP.Skolem (runSkolem, Formula)
import Data.Logic.ATP.Term (IsTerm(..))
import Data.List as List (foldr, map)
import Data.Set as Set
import Data.String (IsString(fromString))
import Prelude hiding ((*))
import Test.HUnit

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
predicates :: IsFormula formula => formula -> Set (AtomOf formula)
predicates fm = atom_union Set.singleton fm

-- | Code to generate equate axioms for functions.
function_congruence :: forall fof atom term v p function.
                       (atom ~ AtomOf fof, term ~ TermOf atom, p ~ PredOf atom, v ~ VarOf fof, v ~ TVarOf term, function ~ FunOf term,
                        IsQuantified fof, HasEquate atom, IsTerm term, Ord fof) =>
                       (function, Int) -> Set fof
function_congruence (_,0) = (∅)
function_congruence (f,n) =
    Set.singleton (List.foldr (∀) (ant ⇒ con) (argnames_x ++ argnames_y))
    where
      argnames_x :: [VarOf fof]
      argnames_x = List.map (\ m -> fromString ("x" ++ show m)) [1..n]
      argnames_y :: [VarOf fof]
      argnames_y = List.map (\ m -> fromString ("y" ++ show m)) [1..n]
      args_x = List.map vt argnames_x
      args_y = List.map vt argnames_y
      ant = foldr1 (∧) (List.map (uncurry (.=.)) (zip args_x args_y))
      con = fApp f args_x .=. fApp f args_y

-- | And for predicates.
predicate_congruence :: (atom ~ AtomOf fof, predicate ~ PredOf atom, term ~ TermOf atom, v ~ VarOf fof, v ~ TVarOf term,
                         IsQuantified fof, HasEquate atom, IsTerm term, Ord predicate) =>
                        AtomOf fof -> Set fof
predicate_congruence =
    foldEquate (\_ _ -> Set.empty) (\p ts -> ap p (length ts))
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
equivalence_axioms :: forall fof atom term v.
                      (atom ~ AtomOf fof, term ~ TermOf atom, v ~ VarOf fof,
                       IsQuantified fof, HasEquate atom, IsTerm term, Ord fof) => Set fof
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

equalitize :: forall formula atom term v function.
              (atom ~ AtomOf formula, term ~ TermOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
               IsQuantified formula, HasEquate atom,
               IsTerm term, Ord formula, Ord atom) =>
              formula -> formula
equalitize fm =
    if Set.null eqPreds then fm else foldr1 (∧) axioms ⇒ fm
    where
      axioms = Set.fold (Set.union . function_congruence)
                        (Set.fold (Set.union . predicate_congruence) equivalence_axioms otherPreds)
                        (functions fm)
      (eqPreds, otherPreds) = Set.partition (foldEquate (\_ _ -> True) (\_ _ -> False)) (predicates fm)

-- -------------------------------------------------------------------------
-- Example.
-- -------------------------------------------------------------------------

testEqual01 :: Test
testEqual01 = TestLabel "function_congruence" $ TestCase $ assertEqual "function_congruence" expected input
    where input = List.map function_congruence [(fromString "f", 3 :: Int), (fromString "+",2)]
          expected :: [Set.Set Formula]
          expected = [Set.fromList
                      [(∀) "x1"
                       ((∀) "x2"
                        ((∀) "x3"
                         ((∀) "y1"
                          ((∀) "y2"
                           ((∀) "y3" ((("x1" .=. "y1") ∧ (("x2" .=. "y2") ∧ ("x3" .=. "y3"))) ⇒
                                          ((fApp (fromString "f") ["x1","x2","x3"]) .=. (fApp (fromString "f") ["y1","y2","y3"]))))))))],
                      Set.fromList
                      [(∀) "x1"
                       ((∀) "x2"
                        ((∀) "y1"
                         ((∀) "y2" ((("x1" .=. "y1") ∧ ("x2" .=. "y2")) ⇒
                                        ((fApp (fromString "+") ["x1","x2"]) .=. (fApp (fromString "+") ["y1","y2"]))))))]]

-- -------------------------------------------------------------------------
-- A simple example (see EWD1266a and the application to Morley's theorem).
-- -------------------------------------------------------------------------

ewd :: Formula
ewd = equalitize fm
    where
      fm = ((∀) "x" (fx ⇒ gx)) ∧
           ((∃) "x" fx) ∧
           ((∀) "x" ((∀) "y" (gx ∧ gy ⇒ x .=. y))) ⇒
           ((∀) "y" (gy ⇒ fy))
      fx = pApp "f" [x]
      gx = pApp "g" [x]
      fy = pApp "f" [y]
      gy = pApp "g" [y]
      x = vt "x"
      y = vt "y"

testEqual02 :: Test
testEqual02 = TestLabel "equalitize 1 (p. 241)" $ TestCase $ assertEqual "equalitize 1 (p. 241)" (expected, expectedProof) input
    where input = (ewd, runSkolem (meson (Just (Depth 17)) ewd))
          fx = pApp "f" [x]
          gx = pApp "g" [x]
          fy = pApp "f" [y]
          gy = pApp "g" [y]
          x = vt "x"
          y = vt "y"
          z = vt "z"
          x1 = vt "x1"
          y1 = vt "y1"
          fx1 = pApp "f" [x1]
          gx1 = pApp "g" [x1]
          fy1 = pApp "f" [y1]
          gy1 = pApp "g" [y1]
          -- y1 = fromString "y1"
          -- z = fromString "z"
          expected =
              ((∀) "x" (x .=. x) .&.
               (((∀) "x" ((∀) "y" ((∀) "z" (x .=. y .&. x .=. z .=>. y .=. z)))) .&.
                (((∀) "x1" ((∀) "y1" (x1 .=. y1 .=>. fx1 .=>. fy1))) .&.
                 ((∀) "x1" ((∀) "y1" (x1 .=. y1 .=>. gx1 .=>. gy1)))))) .=>.
              ((∀) "x" (fx .=>. gx)) .&.
              ((∃) "x" (fx)) .&.
              ((∀) "x" ((∀) "y" (gx .&. gy .=>. x .=. y))) .=>.
              ((∀) "y" (gy .=>. fy))
          expectedProof =
              Set.fromList [Success (Depth 6)]

-- | Wishnu Prasetya's example (even nicer with an "exists unique" primitive).

--instance IsString ([MyTerm] -> MyTerm) where
--    fromString = fApp . fromString

wishnu :: Formula
wishnu = [fof| (∃x. x=f (g (x))∧(∀x'. x'=f (g (x'))⇒x=x'))⇔(∃y. y=g (f (y))∧(∀y'. y'=g (f (y'))⇒y=y')) |]

-- This takes 0.7 seconds on my machine.
testEqual03 :: Test
testEqual03 =
    (TestLabel "equalitize 2" . TestCase . timeMessage (\_ t -> "\nEqualitize 2 compute time: " ++ show t))
       (assertEqual' "equalitize 2 (p. 241)" (expected, expectedProof) input)
    where input = (equalitize wishnu, runSkolem (meson Nothing (equalitize wishnu)))
          expected :: Formula
          expected = [fof| (∀x. x=x)∧
                           (∀x y z. x=y∧x=z⇒y=z)∧
                           (∀x1 y1. x1=y1⇒f(x1)=f(y1))∧
                           (∀x1 y1. x1=y1⇒g(x1)=g(y1))⇒
                           ((∃x. x=f(g(x))∧(∀x'. x'=f(g(x'))⇒x=x'))⇔
                            (∃y. y=g(f(y))∧(∀y'. y'=g(f(y'))⇒y=y'))) |]
          expectedProof = Set.fromList [Success (Depth 16)]

-- -------------------------------------------------------------------------
-- More challenging equational problems. (Size 18, 61814 seconds.)
-- -------------------------------------------------------------------------

{-
(meson ** equalitize)
 <<(forall x y z. x * (y * z) = (x * y) * z) /\
   (forall x. 1 * x = x) /\
   (forall x. i(x) * x = 1)
   ==> forall x. x * i(x) = 1>>;;
-}

testEqual04 :: Test
testEqual04 = TestLabel "equalitize 3 (p. 248)" $ TestCase $
  timeMessage (\_ t -> "\nCompute time: " ++ show t) $
  assertEqual' "equalitize 3 (p. 248)" (expected, expectedProof) input
    where
      input = (equalitize fm, runSkolem (meson (Just (Depth 20)) . equalitize $ fm))
      fm :: Formula
      fm = [fof| (forall x y z. x * (y * z) = (x * y) * z) .&.
                 (forall x. 1 * x = x) .&.
                 (forall x. i(x) * x = 1)
                 ==> (forall x. x * i(x) = 1) |]
{-
      fm = [fof| (∀x y z. ((*) ["x'", (*) ["y'", "z'"]] .=. (*) [((*) ["x'", "y'"]), "z'"]) ∧
           (∀) "x" ((*) [one, "x'"] .=. "x'") ∧
           (∀) "x" ((*) [i ["x'"], "x'"] .=. one) ⇒
           (∀) "x" ((*) ["x'", i ["x'"]] .=. one)
      fm = ((∀) "x" . (∀) "y" . (∀) "z") ((*) ["x'", (*) ["y'", "z'"]] .=. (*) [((*) ["x'", "y'"]), "z'"]) ∧
           (∀) "x" ((*) [one, "x'"] .=. "x'") ∧
           (∀) "x" ((*) [i ["x'"], "x'"] .=. one) ⇒
           (∀) "x" ((*) ["x'", i ["x'"]] .=. one)
      (*) = fApp (fromString "*")
      i = fApp (fromString "i")
      one = fApp (fromString "1") []
-}
      expected :: Formula
      expected =
          [fof| (∀x. x=x)∧
                (∀x y z. x=y∧x=z⇒y=z)∧
                (∀x' x'' y' y''. x'=y'∧x''=y''⇒(x' * x'')=(y' * y''))⇒
                (∀x y z. (x' * (y' * z'))=((x'* y') * z'))∧
                (∀x. (1 * x')=x')∧
                (∀x. (i(x') * x')=1)⇒
                (∀x. (x' * i(x'))=1) |]
{-
          ((∀) "x" ("x" .=. "x") .&.
           ((∀) "x" ((∀) "y" ((∀) "z" ((("x" .=. "y") .&. ("x" .=. "z")) .=>. ("y" .=. "z")))) .&.
            ((∀) "x1" ((∀) "x2" ((∀) "y1" ((∀) "y2" ((("x1" .=. "y1") .&. ("x2" .=. "y2")) .=>.
                                                                     ((fApp "*" ["x1","x2"]) .=. (fApp "*" ["y1","y2"])))))) .&.
             (∀) "x1" ((∀) "y1" (("x1" .=. "y1") .=>. ((fApp "i" ["x1"]) .=. (fApp "i" ["y1"]))))))) .=>.
          ((((∀) "x" ((∀) "y" ((∀) "z" ((fApp "*" ["x",fApp "*" ["y","z"]]) .=. (fApp "*" [fApp "*" ["x","y"],"z"])))) .&.
             (∀) "x" ((fApp "*" [fApp "1" [],"x"]) .=. "x")) .&.
            (∀) "x" ((fApp "*" [fApp "i" ["x"],"x"]) .=. (fApp "1" []))) .=>.
           (∀) "x" ((fApp "*" ["x",fApp "i" ["x"]]) .=. (fApp "1" []))) -}
      expectedProof :: Set.Set (Failing Depth)
      expectedProof = Set.fromList [Failure ["Exceeded maximum depth limit"]]

testEqual :: Test
testEqual = TestLabel "Equal" (TestList [testEqual01, testEqual02, testEqual03 {-, testEqual04-}])

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
