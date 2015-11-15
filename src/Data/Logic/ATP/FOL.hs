-- | Basic stuff for first order logic.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

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

module Data.Logic.ATP.FOL
    ( IsFirstOrder
    -- * Semantics
    , Interp
    , holds
    , holdsQuantified
    , holdsAtom
    , termval
    -- * Free Variables
    , var
    , fv, fva, fvt
    , generalize
    -- * Substitution
    , subst, substq, asubst, tsubst, lsubst
    , bool_interp
    , mod_interp
    -- * Concrete instances of formula types for use in unit tests.
    , ApFormula, EqFormula
    -- * Tests
    , testFOL
    ) where

import Data.Logic.ATP.Apply (ApAtom, HasApply(PredOf, TermOf, overterms, onterms), Predicate)
import Data.Logic.ATP.Equate ((.=.), EqAtom, foldEquate, HasEquate)
import Data.Logic.ATP.Formulas (fromBool, IsFormula(..))
import Data.Logic.ATP.Lib (setAny, tryApplyD, undefine, (|->))
import Data.Logic.ATP.Lit ((.~.), foldLiteral, JustLiteral)
import Data.Logic.ATP.Pretty (prettyShow)
import Data.Logic.ATP.Prop (BinOp(..), IsPropositional((.&.), (.|.), (.=>.), (.<=>.)))
import Data.Logic.ATP.Quantified (exists, foldQuantified, for_all, IsQuantified(VarOf), Quant((:!:), (:?:)), QFormula)
import Data.Logic.ATP.Term (FName, foldTerm, IsTerm(FunOf, TVarOf, vt, fApp), V, variant)
import Data.Map.Strict as Map (empty, fromList, insert, lookup, Map)
import Data.Maybe (fromMaybe)
import Data.Set as Set (difference, empty, fold, fromList, member, Set, singleton, union, unions)
import Data.String (IsString(fromString))
import Prelude hiding (pred)
import Test.HUnit

-- | Combine IsQuantified, HasApply, IsTerm, and make sure the term is
-- using the same variable type as the formula.
class (IsQuantified formula,
       HasApply (AtomOf formula),
       IsTerm (TermOf (AtomOf formula)),
       VarOf formula ~ TVarOf (TermOf (AtomOf formula)))
    => IsFirstOrder formula

-- | A formula type with no equality predicate
type ApFormula = QFormula V ApAtom
instance IsFirstOrder ApFormula

-- | A formula type with equality predicate
type EqFormula = QFormula V EqAtom
instance IsFirstOrder EqFormula

{-
(* Trivial example of "x + y < z".                                           *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
Atom(R("<",[Fn("+",[Var "x"; Var "y"]); Var "z"]));;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Parsing of terms.                                                         *)
(* ------------------------------------------------------------------------- *)

let is_const_name s = forall numeric (explode s) or s = "nil";;

let rec parse_atomic_term vs inp =
  match inp with
    [] -> failwith "term expected"
  | "("::rest -> parse_bracketed (parse_term vs) ")" rest
  | "-"::rest -> papply (fun t -> Fn("-",[t])) (parse_atomic_term vs rest)
  | f::"("::")"::rest -> Fn(f,[]),rest
  | f::"("::rest ->
      papply (fun args -> Fn(f,args))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | a::rest ->
      (if is_const_name a & not(mem a vs) then Fn(a,[]) else Var a),rest

and parse_term vs inp =
  parse_right_infix "::" (fun (e1,e2) -> Fn("::",[e1;e2]))
    (parse_right_infix "+" (fun (e1,e2) -> Fn("+",[e1;e2]))
       (parse_left_infix "-" (fun (e1,e2) -> Fn("-",[e1;e2]))
          (parse_right_infix "*" (fun (e1,e2) -> Fn("*",[e1;e2]))
             (parse_left_infix "/" (fun (e1,e2) -> Fn("/",[e1;e2]))
                (parse_left_infix "^" (fun (e1,e2) -> Fn("^",[e1;e2]))
                   (parse_atomic_term vs)))))) inp;;

let parset = make_parser (parse_term []);;

(* ------------------------------------------------------------------------- *)
(* Parsing of formulas.                                                      *)
(* ------------------------------------------------------------------------- *)

let parse_infix_atom vs inp =
  let tm,rest = parse_term vs inp in
  if exists (nextin rest) ["="; "<"; "<="; ">"; ">="] then
        papply (fun tm' -> Atom(R(hd rest,[tm;tm'])))
               (parse_term vs (tl rest))
  else failwith "";;

let parse_atom vs inp =
  try parse_infix_atom vs inp with Failure _ ->
  match inp with
  | p::"("::")"::rest -> Atom(R(p,[])),rest
  | p::"("::rest ->
      papply (fun args -> Atom(R(p,args)))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | p::rest when p <> "(" -> Atom(R(p,[])),rest
  | _ -> failwith "parse_atom";;

let parse = make_parser
  (parse_formula (parse_infix_atom,parse_atom) []);;

(* ------------------------------------------------------------------------- *)
(* Set up parsing of quotations.                                             *)
(* ------------------------------------------------------------------------- *)

let default_parser = parse;;

let secondary_parser = parset;;

{-
(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
<<(forall x. x < 2 ==> 2 * x <= 3) \/ false>>;;

<<|2 * x|>>;;
END_INTERACTIVE;;
-}

(* ------------------------------------------------------------------------- *)
(* Printing of terms.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec print_term prec fm =
  match fm with
    Var x -> print_string x
  | Fn("^",[tm1;tm2]) -> print_infix_term true prec 24 "^" tm1 tm2
  | Fn("/",[tm1;tm2]) -> print_infix_term true prec 22 " /" tm1 tm2
  | Fn("*",[tm1;tm2]) -> print_infix_term false prec 20 " *" tm1 tm2
  | Fn("-",[tm1;tm2]) -> print_infix_term true prec 18 " -" tm1 tm2
  | Fn("+",[tm1;tm2]) -> print_infix_term false prec 16 " +" tm1 tm2
  | Fn("::",[tm1;tm2]) -> print_infix_term false prec 14 "::" tm1 tm2
  | Fn(f,args) -> print_fargs f args

and print_fargs f args =
  print_string f;
  if args = [] then () else
   (print_string "(";
    open_box 0;
    print_term 0 (hd args); print_break 0 0;
    do_list (fun t -> print_string ","; print_break 0 0; print_term 0 t)
            (tl args);
    close_box();
    print_string ")")

and print_infix_term isleft oldprec newprec sym p q =
  if oldprec > newprec then (print_string "("; open_box 0) else ();
  print_term (if isleft then newprec else newprec+1) p;
  print_string sym;
  print_break (if String.sub sym 0 1 = " " then 1 else 0) 0;
  print_term (if isleft then newprec+1 else newprec) q;
  if oldprec > newprec then (close_box(); print_string ")") else ();;

let printert tm =
  open_box 0; print_string "<<|";
  open_box 0; print_term 0 tm; close_box();
  print_string "|>>"; close_box();;

#install_printer printert;;

(* ------------------------------------------------------------------------- *)
(* Printing of formulas.                                                     *)
(* ------------------------------------------------------------------------- *)

let print_atom prec (R(p,args)) =
  if mem p ["="; "<"; "<="; ">"; ">="] & length args = 2
  then print_infix_term false 12 12 (" "^p) (el 0 args) (el 1 args)
  else print_fargs p args;;

let print_fol_formula = print_qformula print_atom;;

#install_printer print_fol_formula;;

(* ------------------------------------------------------------------------- *)
(* Examples in the main text.                                                *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
<<forall x y. exists z. x < z /\ y < z>>;;

<<~(forall x. P(x)) <=> exists y. ~P(y)>>;;
END_INTERACTIVE;;
-}

-- | Specify the domain of a formula interpretation, and how to
-- interpret its functions and predicates.
data Interp function predicate d
    = Interp { domain :: [d]
             , funcApply :: function -> [d] -> d
             , predApply :: predicate -> [d] -> Bool
             , eqApply :: d -> d -> Bool }

-- | The holds function computes the value of a formula for a finite domain.
class FiniteInterpretation a function predicate v dom where
    holds :: Interp function predicate dom -> Map v dom -> a -> Bool

-- | Implementation of holds for IsQuantified formulas.
holdsQuantified :: forall formula function predicate dom.
                   (IsQuantified formula,
                    FiniteInterpretation (AtomOf formula) function predicate (VarOf formula) dom,
                    FiniteInterpretation formula function predicate (VarOf formula) dom) =>
                   Interp function predicate dom -> Map (VarOf formula) dom -> formula -> Bool
holdsQuantified m v fm =
    foldQuantified qu co ne tf at fm
    where
      qu (:!:) x p = and (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- >>= return . any (== True)
      qu (:?:) x p = or (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- return . all (== True)?
      ne p = not (holds m v p)
      co p (:&:) q = (holds m v p) && (holds m v q)
      co p (:|:) q = (holds m v p) || (holds m v q)
      co p (:=>:) q = not (holds m v p) || (holds m v q)
      co p (:<=>:) q = (holds m v p) == (holds m v q)
      tf x = x
      at = (holds m v :: AtomOf formula -> Bool)

-- | Implementation of holds for atoms with equate predicates.
holdsAtom :: (HasEquate atom, IsTerm term, Eq dom,
              term ~ TermOf atom, v ~ TVarOf term, function ~ FunOf term, predicate ~ PredOf atom) =>
             Interp function predicate dom -> Map v dom -> atom -> Bool
holdsAtom m v at = foldEquate (\t1 t2 -> eqApply m (termval m v t1) (termval m v t2))
                                (\r args -> predApply m r (map (termval m v) args)) at

termval :: (IsTerm term, v ~ TVarOf term, function ~ FunOf term) => Interp function predicate r -> Map v r -> term -> r
termval m v tm =
    foldTerm (\x -> fromMaybe (error ("Undefined variable: " ++ show x)) (Map.lookup x v))
             (\f args -> funcApply m f (map (termval m v) args)) tm

{-
START_INTERACTIVE;;
holds bool_interp undefined <<forall x. (x = 0) \/ (x = 1)>>;;

holds (mod_interp 2) undefined <<forall x. (x = 0) \/ (x = 1)>>;;

holds (mod_interp 3) undefined <<forall x. (x = 0) \/ (x = 1)>>;;

let fm = <<forall x. ~(x = 0) ==> exists y. x * y = 1>>;;

filter (fun n -> holds (mod_interp n) undefined fm) (1--45);;

holds (mod_interp 3) undefined <<(forall x. x = 0) ==> 1 = 0>>;;
holds (mod_interp 3) undefined <<forall x. x = 0 ==> 1 = 0>>;;
END_INTERACTIVE;;
-}

-- | Examples of particular interpretations.
bool_interp :: Interp FName Predicate Bool
bool_interp =
    Interp [False, True] func pred (==)
    where
      func f [] | f == fromString "False" = False
      func f [] | f == fromString "True" = True
      func f [x,y] | f == fromString "+" = x /= y
      func f [x,y] | f == fromString "*" = x && y
      func f _ = error ("bool_interp - uninterpreted function: " ++ show f)
      pred p _ = error ("bool_interp - uninterpreted predicate: " ++ show p)

mod_interp :: Int -> Interp FName Predicate Int
mod_interp n =
    Interp [0..(n-1)] func pred (==)
    where
      func f [] | f == fromString "0" = 0
      func f [] | f == fromString "1" = 1 `mod` n
      func f [x,y] | f == fromString "+" = (x + y) `mod` n
      func f [x,y] | f == fromString "*" = (x * y) `mod` n
      func f _ = error ("mod_interp - uninterpreted function: " ++ show f)
      pred p _ = error ("mod_interp - uninterpreted predicate: " ++ show p)

instance Eq dom => FiniteInterpretation EqFormula FName Predicate V dom where holds = holdsQuantified
instance Eq dom => FiniteInterpretation EqAtom FName Predicate V dom where holds = holdsAtom

test01 :: Test
test01 = TestCase $ assertEqual "holds bool test (p. 126)" expected input
    where input = holds bool_interp (Map.empty :: Map V Bool) (for_all "x" ((vt "x") .=. (fApp "False" []) .|. (vt "x") .=. (fApp "True" [])) :: EqFormula)
          expected = True
test02 :: Test
test02 = TestCase $ assertEqual "holds mod test 1 (p. 126)" expected input
    where input =  holds (mod_interp 2) (Map.empty :: Map V Int) (for_all "x" (vt "x" .=. (fApp "0" []) .|. vt "x" .=. (fApp "1" [])) :: EqFormula)
          expected = True
test03 :: Test
test03 = TestCase $ assertEqual "holds mod test 2 (p. 126)" expected input
    where input =  holds (mod_interp 3) (Map.empty :: Map V Int) (for_all "x" (vt "x" .=. fApp "0" [] .|. vt "x" .=. fApp "1" []) :: EqFormula)
          expected = False

test04 :: Test
test04 = TestCase $ assertEqual "holds mod test 3 (p. 126)" expected input
    where input = filter (\ n -> holds (mod_interp n) (Map.empty :: Map V Int) fm) [1..45]
                  where fm = for_all "x" ((.~.) (vt "x" .=. fApp "0" []) .=>. exists "y" (fApp "*" [vt "x", vt "y"] .=. fApp "1" [])) :: EqFormula
          expected = [1,2,3,5,7,11,13,17,19,23,29,31,37,41,43]

test05 :: Test
test05 = TestCase $ assertEqual "holds mod test 4 (p. 129)" expected input
    where input = holds (mod_interp 3) (Map.empty :: Map V Int) ((for_all "x" (vt "x" .=. fApp "0" [])) .=>. fApp "1" [] .=. fApp "0" [] :: EqFormula)
          expected = True
test06 :: Test
test06 = TestCase $ assertEqual "holds mod test 5 (p. 129)" expected input
    where input = holds (mod_interp 3) (Map.empty :: Map V Int) (for_all "x" (vt "x" .=. fApp "0" [] .=>. fApp "1" [] .=. fApp "0" []) :: EqFormula)
          expected = False

-- Free variables in terms and formulas.

-- | Find the free variables in a formula.
fv :: (IsFirstOrder formula, v ~ VarOf formula) => formula -> Set v
fv fm =
    foldQuantified qu co ne tf at fm
    where
      qu _ x p = difference (fv p) (singleton x)
      ne p = fv p
      co p _ q = union (fv p) (fv q)
      tf _ = Set.empty
      at = fva

-- | Find all the variables in a formula.
-- var :: (IsFirstOrder formula, v ~ VarOf formula) => formula -> Set v
var :: (IsFormula formula, HasApply atom,
        atom ~ AtomOf formula, term ~ TermOf atom, v ~ TVarOf term) =>
       formula -> Set v
var fm = overatoms (\a s -> Set.union (fva a) s) fm mempty

-- | Find the variables in an atom
fva :: (HasApply atom, IsTerm term, term ~ TermOf atom, v ~ TVarOf term) => atom -> Set v
fva = overterms (\t s -> Set.union (fvt t) s) mempty

-- | Find the variables in a term
fvt :: (IsTerm term, v ~ TVarOf term) => term -> Set v
fvt tm = foldTerm singleton (\_ args -> unions (map fvt args)) tm

-- | Universal closure of a formula.
generalize :: IsFirstOrder formula => formula -> formula
generalize fm = Set.fold for_all fm (fv fm)

test07 :: Test
test07 = TestCase $ assertEqual "variant 1 (p. 133)" expected input
    where input = variant "x" (Set.fromList ["y", "z"]) :: V
          expected = "x"
test08 :: Test
test08 = TestCase $ assertEqual "variant 2 (p. 133)" expected input
    where input = variant "x" (Set.fromList ["x", "y"]) :: V
          expected = "x'"
test09 :: Test
test09 = TestCase $ assertEqual "variant 3 (p. 133)" expected input
    where input = variant "x" (Set.fromList ["x", "x'"]) :: V
          expected = "x''"

-- | Substitution in formulas, with variable renaming.
subst :: (IsFirstOrder formula, term ~ TermOf (AtomOf formula), v ~ VarOf formula) => Map v term -> formula -> formula
subst subfn fm =
    foldQuantified qu co ne tf at fm
    where
      qu (:!:) x p = substq subfn for_all x p
      qu (:?:) x p = substq subfn exists x p
      ne p = (.~.) (subst subfn p)
      co p (:&:) q = (subst subfn p) .&. (subst subfn q)
      co p (:|:) q = (subst subfn p) .|. (subst subfn q)
      co p (:=>:) q = (subst subfn p) .=>. (subst subfn q)
      co p (:<=>:) q = (subst subfn p) .<=>. (subst subfn q)
      tf False = false
      tf True = true
      at = atomic . asubst subfn

-- | Substitution within terms.
tsubst :: (IsTerm term, v ~ TVarOf term) => Map v term -> term -> term
tsubst sfn tm =
    foldTerm (\x -> fromMaybe tm (Map.lookup x sfn))
             (\f args -> fApp f (map (tsubst sfn) args))
             tm

-- | Substitution within a Literal
lsubst :: (JustLiteral lit, HasApply atom, IsTerm term,
           atom ~ AtomOf lit,
           term ~ TermOf atom,
           v ~ TVarOf term) =>
          Map v term -> lit -> lit
lsubst subfn fm =
    foldLiteral ne fromBool at fm
    where
      ne p = (.~.) (lsubst subfn p)
      at = atomic . asubst subfn

-- | Substitution within atoms.
asubst :: (HasApply atom, IsTerm term, term ~ TermOf atom, v ~ TVarOf term) => Map v term -> atom -> atom
asubst sfn a = onterms (tsubst sfn) a

-- | Substitution within quantifiers
substq :: (IsFirstOrder formula, v ~ VarOf formula, term ~ TermOf (AtomOf formula)) =>
          Map v term -> (v -> formula -> formula) -> v -> formula -> formula
substq subfn qu x p =
  let x' = if setAny (\y -> Set.member x (fvt(tryApplyD subfn y (vt y))))
                     (difference (fv p) (singleton x))
           then variant x (fv (subst (undefine x subfn) p)) else x in
  qu x' (subst ((x |-> vt x') subfn) p)

-- Examples.

test10 :: Test
test10 =
    let [x, x', y] = [vt "x", vt "x'", vt "y"]
        fm = for_all "x" ((x .=. y)) :: EqFormula
        expected = for_all "x'" (x' .=. x) :: EqFormula in
    TestCase $ assertEqual ("subst (\"y\" |=> Var \"x\") " ++ prettyShow fm ++ " (p. 134)")
                           expected
                           (subst (Map.fromList [("y", x)]) fm)

test11 :: Test
test11 =
    let [x, x', x'', y] = [vt "x", vt "x'", vt "x''", vt "y"]
        fm = (for_all "x" (for_all "x'" ((x .=. y) .=>. (x .=. x')))) :: EqFormula
        expected = for_all "x'" (for_all "x''" ((x' .=. x) .=>. ((x' .=. x'')))) :: EqFormula in
    TestCase $ assertEqual ("subst (\"y\" |=> Var \"x\") " ++ prettyShow fm ++ " (p. 134)")
                           expected
                           (subst (Map.fromList [("y", x)]) fm)

testFOL :: Test
testFOL = TestLabel "FOL" (TestList [test01, test02, test03, test04,
                                     test05, test06, test07, test08, test09,
                                     test10, test11])
