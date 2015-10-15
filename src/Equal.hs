{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}
module Equal
{-  ( function_congruence
    , equalitize
    ) -} where

-- ========================================================================= 
-- First order logic with equality.                                          
--                                                                           
-- Copyright (co) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

import FOL (HasPredicate(applyPredicate))
import Formulas ((∧), (⇒))
import Formulas (HasBoolean(fromBool))
import FOL (HasEquality(..), foldEquals, HasEquals(..), (.=.))
import FOL (IsQuantified(..), (∀))
import Formulas (IsFormula(atomic, overatoms))
import FOL (IsTerm(..))
import Formulas (atom_union)
import Skolem (funcs)
import Lib ((∅))
-- import Data.Logic.Harrison.Skolem (functions)
import qualified Data.Set as Set
import Data.String (IsString(fromString))

-- is_eq :: (IsQuantified fof atom v, HasEquality atom p term) => fof -> Bool
-- is_eq = foldFirstOrder (\ _ _ _ -> False) (\ _ -> False) (\ _ -> False) (foldAtomEq (\ _ _ -> False) (\ _ -> False) (\ _ _ -> True))
-- 
-- mk_eq :: (IsQuantified fof atom v, HasEquality atom p term) => term -> term -> fof
-- mk_eq = (.=.)
-- 
-- dest_eq :: (IsQuantified fof atom v, HasEquality atom p term) => fof -> Failing (term, term)
-- dest_eq fm =
--     foldFirstOrder (\ _ _ _ -> err) (\ _ -> err) (\ _ -> err) at fm
--     where
--       at = foldAtomEq (\ _ _ -> err) (\ _ -> err) (\ s t -> Success (s, t))
--       err = Failure ["dest_eq: not an equation"]
-- 
-- lhs :: (IsQuantified fof atom v, HasEquality atom p term) => fof -> Failing term
-- lhs eq = dest_eq eq >>= return . fst
-- rhs :: (IsQuantified fof atom v, HasEquality atom p term) => fof -> Failing term
-- rhs eq = dest_eq eq >>= return . snd

-- ------------------------------------------------------------------------- 
-- The set of predicates in a formula.                                       
-- ------------------------------------------------------------------------- 

predicates :: forall formula atom term v p. (IsQuantified formula atom v, HasEquality atom p term, Ord atom, Ord p) => formula -> Set.Set atom
predicates fm =
    atom_union pair fm
    where pair atom = foldEquals (\ p ts -> Set.singleton atom) (\ _ _ -> Set.singleton atom) atom

{-
-- | Traverse a formula and pass all (predicates, arity) pairs to a function.
-- To collect
foldPredicates :: forall formula atom term v p r. (IsQuantified formula atom v, HasEquality atom p term, Ord p) =>
                  (PredicateName p -> Maybe Int -> r -> r) -> formula -> r -> r
foldPredicates f fm acc =
    foldFirstOrder qu co tf at fm
    where
      fold = foldPredicates f
      qu _ _ p = fold p acc
      co (BinOp l _ r) = fold r (fold l acc)
      co ((:~:) p) = fold p acc
      tf x = fold (fromBool x) acc
      at = foldAtomEq ap tf eq
      ap p _ = f (Name p) (arity p) acc
      eq _ _ = f Equals (Just 2) acc
-}

-- ------------------------------------------------------------------------- 
-- Code to generate equality axioms for functions.                           
-- ------------------------------------------------------------------------- 

function_congruence :: forall fof atom term v p f. (IsQuantified fof atom v, HasEquality atom p term, IsTerm term v f, Ord fof) =>
                       (f, Int) -> Set.Set fof
function_congruence (_,0) = (∅)
function_congruence (f,n) =
    Set.singleton (foldr (∀) (ant ⇒ con) (argnames_x ++ argnames_y))
    where
      argnames_x :: [v]
      argnames_x = map (\ m -> fromString ("x" ++ show m)) [1..n]
      argnames_y :: [v]
      argnames_y = map (\ m -> fromString ("y" ++ show m)) [1..n]
      args_x = map vt argnames_x
      args_y = map vt argnames_y
      ant = foldr1 (∧) (map (uncurry (.=.)) (zip args_x args_y))
      con = fApp f args_x .=. fApp f args_y
  
-- ------------------------------------------------------------------------- 
-- And for predicates.                                                       
-- ------------------------------------------------------------------------- 

predicate_congruence :: (IsQuantified fof atom v, HasEquality atom p term, IsTerm term v f, Ord p) =>
                        atom -> Set.Set fof
predicate_congruence =
    foldEquals (\p ts -> ap p (length ts)) (\_ _ -> Set.empty)
    where
      ap _ 0 = Set.empty
      ap p n = Set.singleton (foldr (∀) (ant ⇒ con) (argnames_x ++ argnames_y))
          where
            argnames_x = map (\ m -> fromString ("x" ++ show m)) [1..n]
            argnames_y = map (\ m -> fromString ("y" ++ show m)) [1..n]
            args_x = map vt argnames_x
            args_y = map vt argnames_y
            ant = foldr1 (∧) (map (uncurry (.=.)) (zip args_x args_y))
            con = atomic (applyPredicate p args_x) ⇒ atomic (applyPredicate p args_y)

-- ------------------------------------------------------------------------- 
-- Hence implement logic with equality just by adding equality "axioms".     
-- ------------------------------------------------------------------------- 

equivalence_axioms :: forall fof atom term v p f. (IsQuantified fof atom v, HasEquality atom p term, IsTerm term v f, Ord fof) => Set.Set fof
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

equalitize :: forall formula atom term v p f. (IsQuantified formula atom v, IsFormula formula atom, HasEquality atom p term, Ord p, Show p, IsTerm term v f, Ord formula, Ord atom, Ord f) =>
              formula -> formula
equalitize fm =
    if Set.null (Set.filter (foldEquals (\_ _ -> False) (\_ _ -> True)) allpreds)
    then fm
    else foldr1 (∧) (Set.toList axioms) ⇒ fm
    where
      axioms = Set.fold (Set.union . function_congruence) (Set.fold (Set.union . predicate_congruence) equivalence_axioms preds) (functions' funcsAtomEq' fm)
      funcsAtomEq' :: atom -> Set.Set (f, Int)
      funcsAtomEq' = funcsAtomEq
      allpreds = predicates fm
      preds = Set.filter (not . foldEquals (\_ _ -> False) (\_ _ -> True)) allpreds

functions' :: forall formula atom f. (IsFormula formula atom, Ord f) => (atom -> Set.Set (f, Int)) -> formula -> Set.Set (f, Int)
-- functions' fa fm = foldAtoms (\ s a -> Set.union s (fa a)) Set.empty fm
functions' fa fm = overatoms (\ a s -> Set.union s (fa a)) fm Set.empty

-- ------------------------------------------------------------------------- 
-- Other variants not mentioned in book.                                     
-- ------------------------------------------------------------------------- 

funcsAtomEq :: (HasEquality atom p term, IsTerm term v f, Ord f) => atom -> Set.Set (f, Int)
funcsAtomEq = foldEquals (\ _ ts -> Set.unions (map funcs ts)) (\ t1 t2 -> Set.union (funcs t1) (funcs t2))

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

