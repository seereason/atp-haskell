-- | Basic stuff for first order logic.  'IsQuantified' is a subclass
-- of 'IsPropositional' of formula types that support existential and
-- universal quantification.
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

module FOL
    (
    -- * Quantified Formulas
      Quant((:!:), (:?:))
    , IsQuantified(VarOf, quant, foldQuantified)
    , for_all, (∀)
    , exists, (∃)
    , precedenceQuantified
    , associativityQuantified
    , prettyQuantified
    , showQuantified
    , zipQuantified
    , convertQuantified
    , onatomsQuantified
    , overatomsQuantified
    , IsFirstOrder
    , QFormula(F, T, Atom, Not, And, Or, Imp, Iff, Forall, Exists)
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
    -- * Concrete instances of types for use in unit tests.
    , ApFormula, EqFormula
    -- * Tests
    , testFOL
    ) where

import Apply (ApAtom, HasApply(PredOf, TermOf, overterms, onterms), Predicate)
import Data.Data (Data)
--import Data.Function (on)
import Data.Map as Map (empty, fromList, insert, lookup, Map)
import Data.Maybe (fromMaybe)
import Data.Set as Set (difference, empty, fold, fromList, member, Set, singleton, union, unions)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Equate ((.=.), EqAtom, foldEquate, HasEquate)
import Formulas (fromBool, IsAtom, IsFormula(..), onatoms, prettyBool)
import Lib (setAny, tryApplyD, undefine, (|->))
import Lit ((.~.), foldLiteral, IsLiteral(foldLiteral'), IsLiteral(..), JustLiteral)
import Prelude hiding (pred)
import Pretty ((<>), Associativity(InfixN, InfixR, InfixA), Doc, HasFixity(precedence, associativity), Precedence,
               prettyShow, Side(Top, LHS, RHS, Unary), testParen, text,
               andPrec, orPrec, impPrec, iffPrec, notPrec, leafPrec, quantPrec)
import Prop (BinOp(..), binop, IsPropositional((.&.), (.|.), (.=>.), (.<=>.), foldPropositional', foldCombination))
import Term (FName, foldTerm, IsTerm(FunOf, TVarOf, vt, fApp), IsVariable, V, variant)
import Text.PrettyPrint (fsep)
import Text.PrettyPrint.HughesPJClass (maybeParens, Pretty(pPrint, pPrintPrec), PrettyLevel)
import Test.HUnit

-------------------------
-- QUANTIFIED FORMULAS --
-------------------------

-- | The two types of quantification
data Quant
    = (:!:) -- ^ for_all
    | (:?:) -- ^ exists
    deriving (Eq, Ord, Data, Typeable, Show)

-- | Class of quantified formulas.
class (IsPropositional formula, IsVariable (VarOf formula)) => IsQuantified formula where
    type (VarOf formula) -- A type function mapping formula to the associated variable
    quant :: Quant -> VarOf formula -> formula -> formula
    foldQuantified :: (Quant -> VarOf formula -> formula -> r)
                   -> (formula -> BinOp -> formula-> r)
                   -> (formula -> r)
                   -> (Bool -> r)
                   -> (AtomOf formula -> r)
                   -> formula -> r

for_all :: IsQuantified formula => VarOf formula -> formula -> formula
for_all = quant (:!:)
exists :: IsQuantified formula => VarOf formula -> formula -> formula
exists = quant (:?:)

-- | ∀ can't be a function when -XUnicodeSyntax is enabled.
(∀) :: IsQuantified formula => VarOf formula -> formula -> formula
infixr 1 ∀
(∀) = for_all
(∃) :: IsQuantified formula => VarOf formula -> formula -> formula
infixr 1 ∃
(∃) = exists

precedenceQuantified :: forall formula. IsQuantified formula => formula -> Precedence
precedenceQuantified = foldQuantified qu co ne tf at
    where
      qu _ _ _ = quantPrec
      co _ (:&:) _ = andPrec
      co _ (:|:) _ = orPrec
      co _ (:=>:) _ = impPrec
      co _ (:<=>:) _ = iffPrec
      ne _ = notPrec
      tf _ = leafPrec
      at = precedence

associativityQuantified :: forall formula. IsQuantified formula => formula -> Associativity
associativityQuantified = foldQuantified qu co ne tf at
    where
      qu _ _ _ = Pretty.InfixR
      ne _ = Pretty.InfixA
      co _ (:&:) _ = Pretty.InfixA
      co _ (:|:) _ = Pretty.InfixA
      co _ (:=>:) _ = Pretty.InfixR
      co _ (:<=>:) _ = Pretty.InfixA
      tf _ = Pretty.InfixN
      at = associativity

-- | Implementation of 'Pretty' for 'IsQuantified' types.
prettyQuantified :: forall fof v. (IsQuantified fof, v ~ VarOf fof) =>
                    Side -> PrettyLevel -> Rational -> fof -> Doc
prettyQuantified side l r fm =
    maybeParens (testParen side r (precedence fm) (associativity fm)) $ foldQuantified (\op v p -> qu op [v] p) co ne tf at fm
    -- maybeParens (r > precedence fm) $ foldQuantified (\op v p -> qu op [v] p) co ne tf at fm
    where
      -- Collect similarly quantified variables
      qu :: Quant -> [v] -> fof -> Doc
      qu op vs p' = foldQuantified (qu' op vs p') (\_ _ _ -> qu'' op vs p') (\_ -> qu'' op vs p')
                                                      (\_ -> qu'' op vs p') (\_ -> qu'' op vs p') p'
      qu' :: Quant -> [v] -> fof -> Quant -> v -> fof -> Doc
      qu' op vs _ op' v p' | op == op' = qu op (v : vs) p'
      qu' op vs p _ _ _ = qu'' op vs p
      qu'' :: Quant -> [v] -> fof -> Doc
      qu'' _op [] p = prettyQuantified Unary l r p
      qu'' op vs p = text (case op of (:!:) -> "∀"; (:?:) -> "∃") <>
                     fsep (map pPrint (reverse vs)) <>
                     text ". " <> prettyQuantified Unary l (precedence fm + 1) p
      co :: fof -> BinOp -> fof -> Doc
      co p (:&:) q = prettyQuantified LHS l (precedence fm) p <> text "∧" <>  prettyQuantified RHS l (precedence fm) q
      co p (:|:) q = prettyQuantified LHS l (precedence fm) p <> text "∨" <> prettyQuantified RHS l (precedence fm) q
      co p (:=>:) q = prettyQuantified LHS l (precedence fm) p <> text "⇒" <> prettyQuantified RHS l (precedence fm) q
      co p (:<=>:) q = prettyQuantified LHS l (precedence fm) p <> text "⇔" <> prettyQuantified RHS l (precedence fm) q
      ne p = text "¬" <> prettyQuantified Unary l (precedence fm) p
      tf x = pPrint x
      at x = pPrintPrec l r x -- maybeParens (d > PrettyLevel atomPrec) $ pPrint x

-- | Implementation of 'showsPrec' for 'IsQuantified' types.
showQuantified :: IsQuantified formula => Side -> Int -> formula -> ShowS
showQuantified side r fm =
    showParen (testParen side r (precedence fm) (associativity fm)) $ foldQuantified qu co ne tf at fm
    where
      qu (:!:) x p = showString "for_all " . showString (show x) . showString " " . showQuantified Unary (precedence fm + 1) p
      qu (:?:) x p = showString "exists " . showString (show x) . showString " " . showQuantified Unary (precedence fm + 1) p
      co p (:&:) q = showQuantified LHS (precedence fm) p . showString " .&. " . showQuantified RHS (precedence fm) q
      co p (:|:) q = showQuantified LHS (precedence fm) p . showString " .|. " . showQuantified RHS (precedence fm) q
      co p (:=>:) q = showQuantified LHS (precedence fm) p . showString " .=>. " . showQuantified RHS (precedence fm) q
      co p (:<=>:) q = showQuantified LHS (precedence fm) p . showString " .<=>. " . showQuantified RHS (precedence fm) q
      ne p = showString "(.~.) " . showQuantified Unary (succ (precedence fm)) p
      tf x = showsPrec (precedence fm) x
      at x = showsPrec (precedence fm) x

-- | Combine two formulas if they are similar.
zipQuantified :: IsQuantified formula =>
                 (Quant -> VarOf formula -> formula -> Quant -> VarOf formula -> formula -> Maybe r)
              -> (formula -> BinOp -> formula -> formula -> BinOp -> formula -> Maybe r)
              -> (formula -> formula -> Maybe r)
              -> (Bool -> Bool -> Maybe r)
              -> ((AtomOf formula) -> (AtomOf formula) -> Maybe r)
              -> formula -> formula -> Maybe r
zipQuantified qu co ne tf at fm1 fm2 =
    foldQuantified qu' co' ne' tf' at' fm1
    where
      qu' op1 v1 p1 = foldQuantified (qu op1 v1 p1)       (\ _ _ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      co' l1 op1 r1 = foldQuantified (\ _ _ _ -> Nothing) (co l1 op1 r1)       (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      ne' x1 =        foldQuantified (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing) (ne x1)          (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 =        foldQuantified (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing) (\ _ -> Nothing) (tf x1)          (\ _ -> Nothing) fm2
      at' atom1 =     foldQuantified (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (at atom1)       fm2

-- | Convert any instance of IsQuantified to any other by
-- specifying the result type.
convertQuantified :: forall f1 f2.
                     (IsQuantified f1, IsQuantified f2) =>
                     (AtomOf f1 -> AtomOf f2) -> (VarOf f1 -> VarOf f2) -> f1 -> f2
convertQuantified ca cv f1 =
    foldQuantified qu co ne tf at f1
    where
      qu :: Quant -> VarOf f1 -> f1 -> f2
      qu (:!:) x p = for_all (cv x :: VarOf f2) (convertQuantified ca cv p :: f2)
      qu (:?:) x p = exists (cv x :: VarOf f2) (convertQuantified ca cv p :: f2)
      co p (:&:) q = convertQuantified ca cv p .&. convertQuantified ca cv q
      co p (:|:) q = convertQuantified ca cv p .|. convertQuantified ca cv q
      co p (:=>:) q = convertQuantified ca cv p .=>. convertQuantified ca cv q
      co p (:<=>:) q = convertQuantified ca cv p .<=>. convertQuantified ca cv q
      ne p = (.~.) (convertQuantified ca cv p)
      tf :: Bool -> f2
      tf = fromBool
      at :: AtomOf f1 -> f2
      at = atomic . ca

onatomsQuantified :: IsQuantified formula => (AtomOf formula -> formula) -> formula -> formula
onatomsQuantified f fm =
    foldQuantified qu co ne tf at fm
    where
      qu op v p = quant op v (onatomsQuantified f p)
      ne p = (.~.) (onatomsQuantified f p)
      co p op q = binop (onatomsQuantified f p) op (onatomsQuantified f q)
      tf flag = fromBool flag
      at x = f x

overatomsQuantified :: IsQuantified fof => (AtomOf fof -> r -> r) -> fof -> r -> r
overatomsQuantified f fof r0 =
    foldQuantified qu co ne (const r0) (flip f r0) fof
    where
      qu _ _ fof' = overatomsQuantified f fof' r0
      ne fof' = overatomsQuantified f fof' r0
      co p _ q = overatomsQuantified f p (overatomsQuantified f q r0)

-- | Combine IsQuantified, HasApply, IsTerm, and make sure the term is
-- using the same variable type as the formula.
class (IsQuantified formula,
       HasApply (AtomOf formula),
       IsTerm (TermOf (AtomOf formula)),
       VarOf formula ~ TVarOf (TermOf (AtomOf formula)))
    => IsFirstOrder formula

data QFormula v atom
    = F
    | T
    | Atom atom
    | Not (QFormula v atom)
    | And (QFormula v atom) (QFormula v atom)
    | Or (QFormula v atom) (QFormula v atom)
    | Imp (QFormula v atom) (QFormula v atom)
    | Iff (QFormula v atom) (QFormula v atom)
    | Forall v (QFormula v atom)
    | Exists v (QFormula v atom)
    deriving (Eq, Ord, Data, Typeable, Read)

instance (HasApply atom, IsTerm term, term ~ TermOf atom, v ~ TVarOf term) => Pretty (QFormula v atom) where
    pPrintPrec = prettyQuantified Top

-- The IsFormula instance for QFormula
instance (HasApply atom, v ~ TVarOf (TermOf atom)) => IsFormula (QFormula v atom) where
    type AtomOf (QFormula v atom) = atom
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    true = T
    false = F
    atomic = Atom
    overatoms = overatomsQuantified
    onatoms = onatomsQuantified

instance (IsFormula (QFormula v atom), HasApply atom, v ~ TVarOf (TermOf atom)) => IsPropositional (QFormula v atom) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff
    foldPropositional' ho co ne tf at fm =
        case fm of
          And p q -> co p (:&:) q
          Or p q -> co p (:|:) q
          Imp p q -> co p (:=>:) q
          Iff p q -> co p (:<=>:) q
          _ -> foldLiteral' ho ne tf at fm
    foldCombination other dj cj imp iff fm =
        case fm of
          Or a b -> a `dj` b
          And a b -> a `cj` b
          Imp a b -> a `imp` b
          Iff a b -> a `iff` b
          _ -> other fm

instance (IsPropositional (QFormula v atom), IsVariable v, IsAtom atom) => IsQuantified (QFormula v atom) where
    type VarOf (QFormula v atom) = v
    quant (:!:) = Forall
    quant (:?:) = Exists
    foldQuantified qu _co _ne _tf _at (Forall v fm) = qu (:!:) v fm
    foldQuantified qu _co _ne _tf _at (Exists v fm) = qu (:?:) v fm
    foldQuantified _qu co ne tf at fm =
        foldPropositional' (\_ -> error "IsQuantified QFormula") co ne tf at fm

-- Build a Haskell expression for this formula
instance IsQuantified (QFormula v atom) => Show (QFormula v atom) where
    showsPrec = showQuantified Top

-- Precedence information for QFormula
instance IsQuantified (QFormula v atom) => HasFixity (QFormula v atom) where
    precedence = precedenceQuantified
    associativity = associativityQuantified

instance (HasApply atom, v ~ TVarOf (TermOf atom)) => IsLiteral (QFormula v atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x
    foldLiteral' ho ne tf at fm =
        case fm of
          T -> tf True
          F -> tf False
          Atom a -> at a
          Not p -> ne p
          _ -> ho fm

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
