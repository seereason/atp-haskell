-- | The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}
module DP
    ( tests
    , dpll
    , dpllsat
    , dplltaut
    , dplb
    , dplbsat
    , dplbtaut
    ) where

import Control.Applicative.Error (Failing(..))
import Data.Map as Map
import Data.Set as Set
import DefCNF hiding (tests)
-- import FOL (Formula)
import Formulas
import Lib hiding (tests)
import Lit
import Prelude hiding (negate, pure)
import Prop hiding (tests)
import PropExamples (prime, Knows(K))
import Test.HUnit

instance NumAtom (Knows Integer) where
    ma n = K "p" n Nothing
    ai (K _ n _) = n

flatten :: Ord a => Set (Set a) -> Set a
flatten ss' = Set.fold Set.union Set.empty ss'

#if 0
-- * The DP procedure.
one_literal_rule :: (IsLiteral lit atom, Ord lit) => Set (Set lit) -> Failing (Set (Set lit))
one_literal_rule clauses =
    case Set.minView (Set.filter (\ cl -> Set.size cl == 1) clauses) of
      Nothing -> Failure ["one_literal_rule"]
      Just (s, _) ->
          let u = Set.findMin s in
          let u' = negate u in
          let clauses1 = Set.filter (not . Set.member u) clauses in
          Success (Set.map (\cl -> Set.difference cl (Set.singleton u')) clauses1)
{-
    where
      t1 x = trace ("clauses: " ++ prettyShow x) x
      t2 x = trace ("s: " ++ prettyShow x) x
      t3 x = trace ("u: " ++ prettyShow x) x
      t4 x = trace ("clauses1: " ++ prettyShow x) x
-}

affirmative_negative_rule :: (IsLiteral lit atom, Ord lit) => Set (Set lit) -> Failing (Set (Set lit))
affirmative_negative_rule clauses =
  let (neg', pos) = Set.partition negative (flatten clauses) in
  let neg = Set.map negate neg' in
  let (pos_only, neg_only) = (Set.difference pos neg, Set.difference neg pos) in
  let pure = Set.union pos_only (Set.map negate neg_only) in
  if Set.null pure
  then Failure ["affirmative_negative_rule"]
  else Success (Set.filter (\ cl -> Set.null (Set.intersection cl pure)) clauses)

resolve_on :: forall lit atom. (IsLiteral lit atom, Ord lit) =>
              lit -> Set (Set lit) -> Set (Set lit)
resolve_on p clauses =
  let p' = negate p
      (pos,notpos) = Set.partition (Set.member p) clauses in
  let (neg,other) = Set.partition (Set.member p') notpos in
  let pos' = Set.map (Set.filter (/= p)) pos
      neg' = Set.map (Set.filter (/= p')) neg in
  let res0 = allpairs Set.union pos' neg' in
  Set.union other (Set.filter (not . trivial) res0)

resolution_blowup :: forall formula. (IsNegatable formula, Ord formula) =>
                     Set (Set formula) -> formula -> Int
resolution_blowup cls l =
  let m = Set.size (Set.filter (Set.member l) cls)
      n = Set.size (Set.filter (Set.member (negate l)) cls) in
  m * n - m - n

resolution_rule :: forall lit atom. (IsLiteral lit atom, Ord lit) =>
                   Set (Set lit) -> Failing (Set (Set lit))
resolution_rule clauses =
    let pvs = Set.filter positive (flatten clauses) in
    case minimize' (resolution_blowup clauses) pvs of
      Just p -> Success (resolve_on p clauses)
      Nothing -> Failure ["resolution_rule"]

-- | Overall procedure.
dp :: forall lit atom. (IsLiteral lit atom, Ord lit) => Set (Set lit) -> Failing Bool
dp clauses =
  if Set.null (t1 clauses)
  then Success True
  else if Set.member Set.empty clauses
       then Success False
       else case one_literal_rule clauses >>= dp of
              Success x -> Success x
              Failure _ ->
                  case affirmative_negative_rule clauses >>= dp of
                    Success x -> Success x
                    Failure _ -> resolution_rule clauses >>= dp
#else
one_literal_rule :: (IsLiteral lit atom, Ord lit) => Set.Set (Set.Set lit) -> Failing (Set.Set (Set.Set lit))
one_literal_rule clauses =
    case Set.minView (Set.filter (\ cl -> Set.size cl == 1) clauses) of
      Nothing -> Failure ["one_literal_rule"]
      Just (s, _) ->
          let u = Set.findMin s in
          let u' = (.~.) u in
          let clauses1 = Set.filter (\ cl -> not (Set.member u cl)) clauses in
          Success (Set.map (\ cl -> Set.delete u' cl) clauses1)

affirmative_negative_rule :: (IsLiteral lit atom, Ord lit) => Set.Set (Set.Set lit) -> Failing (Set.Set (Set.Set lit))
affirmative_negative_rule clauses =
  let (neg',pos) = Set.partition negative (flatten clauses) in
  let neg = Set.map (.~.) neg' in
  let pos_only = Set.difference pos neg
      neg_only = Set.difference neg pos in
  let pure = Set.union pos_only (Set.map (.~.) neg_only) in
  if Set.null pure
  then Failure ["affirmative_negative_rule"]
  else Success (Set.filter (\ cl -> Set.null (Set.intersection cl pure)) clauses)

resolve_on :: forall lit atom. (IsLiteral lit atom, Ord lit) =>
              lit -> Set.Set (Set.Set lit) -> Set.Set (Set.Set lit)
resolve_on p clauses =
  let p' = (.~.) p
      (pos,notpos) = Set.partition (Set.member p) clauses in
  let (neg,other) = Set.partition (Set.member p') notpos in
  let pos' = Set.map (Set.filter (\ l -> l /= p)) pos
      neg' = Set.map (Set.filter (\ l -> l /= p')) neg in
  let res0 = allpairs Set.union pos' neg' in
  Set.union other (Set.filter (not . trivial) res0)

resolution_blowup :: forall formula. (IsNegatable formula, Ord formula) =>
                     Set.Set (Set.Set formula) -> formula -> Int
resolution_blowup cls l =
  let m = Set.size (Set.filter (Set.member l) cls)
      n = Set.size (Set.filter (Set.member ((.~.) l)) cls) in
  m * n - m - n

resolution_rule :: forall lit atom. (IsLiteral lit atom, Ord lit) =>
                   Set.Set (Set.Set lit) -> Failing (Set.Set (Set.Set lit))
resolution_rule clauses =
    let pvs = Set.filter positive (flatten clauses) in
    case minimize' (resolution_blowup clauses) pvs of
      Just p -> Success (resolve_on p clauses)
      Nothing -> Failure ["resolution_rule"]

-- ------------------------------------------------------------------------- 
-- Overall procedure.                                                        
-- ------------------------------------------------------------------------- 

dp :: forall lit atom. (IsLiteral lit atom, Ord lit) => Set (Set lit) -> Failing Bool
dp clauses =
  if Set.null clauses
  then Success True
  else if Set.member Set.empty clauses
       then Success False
       else case one_literal_rule clauses >>= dp of
              Success x -> Success x
              Failure _ ->
                  case affirmative_negative_rule clauses >>= dp of
                    Success x -> Success x
                    Failure _ -> resolution_rule clauses >>= dp
#endif

-- | Davis-Putnam satisfiability tester and tautology checker.
dpsat :: forall pf atom. (IsPropositional pf atom, IsLiteral pf atom, NumAtom atom, Ord pf) => pf -> Failing Bool
dpsat fm = dp (defcnfs fm :: Set (Set pf))

dptaut :: forall pf atom. (IsPropositional pf atom, IsLiteral pf atom, NumAtom atom, Ord pf) => pf -> Failing Bool
dptaut fm = not <$> dpsat (negate fm)

-- Examples.

test01 :: Test
test01 = TestCase (assertEqual "dptaut(prime 11) p. 84" (Success True) (dptaut (prime 11 :: PFormula (Knows Integer))))

-- | The same thing but with the DPLL procedure. (p. 84)
posneg_count :: forall formula. (IsNegatable formula, Ord formula) =>
                Set (Set formula) -> formula -> Int
posneg_count cls l =
  let m = Set.size(Set.filter (Set.member l) cls)
      n = Set.size(Set.filter (Set.member (negate l)) cls) in
  m + n

dpll :: forall lit atom. (IsLiteral lit atom, Ord lit) =>
        Set (Set lit) -> Failing Bool
dpll clauses =
  if clauses == Set.empty
  then Success True
  else if Set.member Set.empty clauses
       then Success False
       else case one_literal_rule clauses >>= dpll of
              Success x -> Success x
              Failure _ ->
                  case affirmative_negative_rule clauses >>= dpll of
                    Success x -> Success x
                    Failure _ ->
                        let pvs = Set.filter positive (flatten clauses) in
                        case maximize' (posneg_count clauses) pvs of
                          Nothing -> Failure ["dpll"]
                          Just p ->
                              case (dpll (Set.insert (Set.singleton p) clauses), dpll (Set.insert (Set.singleton (negate p)) clauses)) of
                                (Success a, Success b) -> Success (a || b)
                                (Failure a, Failure b) -> Failure (a ++ b)
                                (Failure a, _) -> Failure a
                                (_, Failure b) -> Failure b

dpllsat :: forall pf. (IsPropositional pf (Knows Integer), IsLiteral pf (Knows Integer), Ord pf) =>
           pf -> Failing Bool
dpllsat fm = dpll(defcnfs fm :: Set (Set pf))

dplltaut :: forall pf. (IsPropositional pf (Knows Integer), IsLiteral pf (Knows Integer), Ord pf) =>
            pf -> Failing Bool
dplltaut fm = dpllsat (negate fm) >>= return . not

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test02 :: Test
test02 = TestCase (assertEqual "dplltaut(prime 11)" (Success True) (dplltaut (prime 11 :: PFormula (Knows Integer))))

-- ------------------------------------------------------------------------- 
-- Iterative implementation with explicit trail instead of recursion.        
-- ------------------------------------------------------------------------- 

data TrailMix = Guessed | Deduced deriving (Eq, Ord)

unassigned :: forall formula. (IsNegatable formula, Ord formula) =>
              Set (Set formula) -> Set (formula, TrailMix) -> Set formula
unassigned cls trail =
    Set.difference (flatten (Set.map (Set.map litabs) cls)) (Set.map (litabs . fst) trail)
    where litabs p = if negated p then negate p else p

unit_subpropagate :: forall formula. (IsNegatable formula, Ord formula) =>
                     (Set (Set formula), Map.Map formula (), Set (formula, TrailMix))
                  -> (Set (Set formula), Map.Map formula (), Set (formula, TrailMix))
unit_subpropagate (cls,fn,trail) =
  let cls' = Set.map (Set.filter (not . defined fn . negate)) cls in
  let uu cs =
          case Set.minView cs of
            Nothing -> Failure ["unit_subpropagate"]
            Just (c, _) -> if Set.size cs == 1 && not (defined fn c)
                           then Success cs
                           else Failure ["unit_subpropagate"] in
  let newunits = flatten (setmapfilter uu cls') in
  if Set.null newunits then (cls',fn,trail) else
  let trail' = Set.fold (\ p t -> Set.insert (p,Deduced) t) trail newunits
      fn' = Set.fold (\ u -> (u |-> ())) fn newunits in
  unit_subpropagate (cls',fn',trail')

unit_propagate :: forall t. (IsNegatable t, Ord t) =>
                  (Set (Set t), Set (t, TrailMix))
               -> (Set (Set t), Set (t, TrailMix))
unit_propagate (cls,trail) =
  let fn = Set.fold (\ (x,_) -> (x |-> ())) Map.empty trail in
  let (cls',fn',trail') = unit_subpropagate (cls,fn,trail) in (cls',trail')

backtrack :: forall t. Set (t, TrailMix) -> Set (t, TrailMix)
backtrack trail =
  case Set.minView trail of
    Just ((p,Deduced), tt) -> backtrack tt
    _ -> trail

dpli :: forall atomic pf. (IsPropositional pf atomic, Ord pf) =>
        Set (Set pf) -> Set (pf, TrailMix) -> Failing Bool
dpli cls trail =
  let (cls', trail') = unit_propagate (cls, trail) in
  if Set.member Set.empty cls' then
    case Set.minView trail of
      Just ((p,Guessed), tt) -> dpli cls (Set.insert (negate p, Deduced) tt)
      _ -> Success False
  else
      case unassigned cls (trail' :: Set (pf, TrailMix)) of
        s | Set.null s -> Success True
        ps -> case maximize' (posneg_count cls') ps of
                Just p -> dpli cls (Set.insert (p :: pf, Guessed) trail')
                Nothing -> Failure ["dpli"]

dplisat :: forall pf atom. (IsPropositional pf atom, IsLiteral pf atom, NumAtom atom, Ord pf) =>
           pf -> Failing Bool
dplisat fm = dpli (defcnfs fm :: Set (Set pf)) Set.empty

dplitaut :: forall pf atom. (IsPropositional pf atom, IsLiteral pf atom, NumAtom atom, Ord pf) =>
            pf -> Failing Bool
dplitaut fm = dplisat (negate fm) >>= return . not

-- ------------------------------------------------------------------------- 
-- With simple non-chronological backjumping and learning.                   
-- ------------------------------------------------------------------------- 

backjump :: forall a. (IsNegatable a, Ord a) =>
            Set (Set a) -> a -> Set (a, TrailMix) -> Set (a, TrailMix)
backjump cls p trail =
  case Set.minView (backtrack trail) of
    Just ((q,Guessed), tt) ->
        let (cls',trail') = unit_propagate (cls, Set.insert (p,Guessed) tt) in
        if Set.member Set.empty cls' then backjump cls p tt else trail
    _ -> trail

dplb :: forall a. (IsNegatable a, Ord a) =>
        Set (Set a) -> Set (a, TrailMix) -> Failing Bool
dplb cls trail =
  let (cls',trail') = unit_propagate (cls,trail) in
  if Set.member Set.empty cls' then
    case Set.minView (backtrack trail) of
      Just ((p,Guessed), tt) ->
        let trail'' = backjump cls p tt in
        let declits = Set.filter (\ (_,d) -> d == Guessed) trail'' in
        let conflict = Set.insert (negate p) (Set.map (negate . fst) declits) in
        dplb (Set.insert conflict cls) (Set.insert (negate p, Deduced) trail'')
      _ -> Success False
  else
    case unassigned cls trail' of
      s | Set.null s -> Success True
      ps -> case maximize' (posneg_count cls') ps of
              Just p -> dplb cls (Set.insert (p,Guessed) trail')
              Nothing -> Failure ["dpib"]

dplbsat :: forall pf atom. (IsPropositional pf atom, IsLiteral pf atom, NumAtom atom, Ord pf) =>
           pf -> Failing Bool
dplbsat fm = dplb (defcnfs fm :: Set (Set pf)) Set.empty

dplbtaut :: forall pf atom. (IsPropositional pf atom, IsLiteral pf atom, NumAtom atom, Ord pf) =>
            pf -> Failing Bool
dplbtaut fm = dplbsat (negate fm) >>= return . not

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 

test03 :: Test
test03 = TestList [TestCase (assertEqual "dplitaut(prime 101)" (Success True) (dplitaut (prime 101 :: PFormula (Knows Integer)))),
                   TestCase (assertEqual "dplbtaut(prime 101)" (Success True) (dplbtaut (prime 101 :: PFormula (Knows Integer))))]

tests :: Test
tests = TestList [test01, test02, test03]
