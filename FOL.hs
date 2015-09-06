{-# LANGUAGE GADTs, OverloadedStrings #-}
module FOL
    ( Term(Var, FApply), vt, fApp
    , FName(FName)
    , FOL(R), FOLEQ(R', (:=:)), (.=.)
    , onformula
    , termval
    , holds
    , bool_interp
    , mod_interp
    , var
    , fv
    , fvFOL, fvFOLEQ
    , generalize
    , variant
    , mapTermsFOL, mapTermsFOLEQ
    , subst, substq
    , tests
    ) where

import Formulas
import Lib (setAny, tryApplyD, undefine, (|->))
import Data.List (intersperse)
import Data.Map as Map (empty, fromList, insert, lookup, Map)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Set as Set (difference, empty, fold, fromList, insert, member, Set, singleton, union, unions)
import Data.String (IsString(fromString))
import Prelude hiding (pred)
import Test.HUnit
import Text.PrettyPrint.HughesPJClass (Pretty(pPrint), prettyShow, text)

-- =========================================================================
-- Basic stuff for first order logic.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)
-- =========================================================================

-- | Terms.
data Term function
    = Var V
    | FApply function [Term function]
    deriving (Eq, Ord, Show)

instance Pretty function => Pretty (Term function) where
    pPrint (Var v) = pPrint v
    pPrint (FApply fn []) = pPrint fn
    pPrint (FApply fn args) = pPrint fn <> text " [" <> mconcat (intersperse (text ", ") (map pPrint args)) <> "]"

-- | A simple type to use as the function parameter of Term, FOL, etc.
newtype FName = FName String deriving (Eq, Ord)

instance IsString FName where fromString = FName

instance Show FName where show (FName s) = s

instance Pretty FName where pPrint (FName s) = text s

vt :: V -> Term function
vt = Var

-- | Build a new term by applying some terms to a function.
fApp :: function -> [Term function] -> Term function
fApp = FApply

-- Example.
test00 :: Test
test00 = TestCase $ assertEqual "print an expression"
                                "sqrt [- [1, cos [power [+ [x, y], 2]]]]"
                                (prettyShow (fApp "sqrt" [fApp "-" [fApp "1" [],
                                                                     fApp "cos" [fApp "power" [fApp "+" [Var "x", Var "y"],
                                                                                               fApp "2" []]]]] :: Term FName))

-- | First order logic formula atom type.
data FOL function = R String [Term function] deriving (Eq, Ord, Show)

-- | First order logic formula atom type with equality.
data FOLEQ function
    = R' String [Term function]
    | Term function :=: Term function
    deriving (Eq, Ord, Show)

(.=.) :: Term function -> Term function -> Formula (FOLEQ function)
a .=. b = Atom (a :=: b)

infix 5 .=. -- , .!=., ≡, ≢

-- | Special case of applying a subfunction to the top *terms*.
onformula :: (Term function -> Term function) -> Formula (FOL function) -> Formula (FOL function)
onformula f = onatoms (\(R p a) -> Atom (R p (map f a)))

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

type Interp function predicate d = ([d], function -> [d] -> d, predicate -> [d] -> Bool)

-- | Semantics, implemented of course for finite domains only.
termval :: Interp function predicate a -> Map V a -> Term function -> a
termval m@(_domain,func,_pred) v tm =
  case tm of
    Var x -> fromMaybe (error $ "Undefined variable: " ++ show x) (Map.lookup x v)
    FApply f args -> func f $ map (termval m v) args

holds :: Interp function String d -> Map V d -> Formula (FOLEQ function) -> Bool
holds m@(domain,_func,pred) v fm =
  case fm of
    F -> False
    T -> True
    Atom (R' r args) -> pred r (map (termval m v) args)
    Atom (a :=: b) -> pred "=" (map (termval m v) [a, b])
    Not p -> not  (holds m v p)
    And p q -> (holds m v p) && (holds m v q)
    Or p q -> (holds m v p) || (holds m v q)
    Imp p q -> (not (holds m v p)) || (holds m v q)
    Iff p q -> (holds m v p) == (holds m v q)
    Forall x p -> and (map (\a -> holds m (Map.insert x a v) p) domain) -- >>= return . any (== True)
    Exists x p -> or (map (\a -> holds m (Map.insert x a v) p) domain) -- return . all (== True)?

-- | Examples of particular interpretations.
bool_interp :: (Eq function, IsString function, Eq predicate, IsString predicate) => Interp function predicate Bool
bool_interp =
  ([False, True],func,pred)
    where
      func f [] | f == fromString "False" = False
      func f [] | f == fromString "True" = True
      func f [x,y] | f == fromString "+" = not(x == y)
      func f [x,y] | f == fromString "*" = x && y
      func _ _ = error "uninterpreted function"
      pred "=" [x,y] = x == y
      pred _ _ = error "uninterpreted predicate"

mod_interp :: (Eq function, IsString function, Eq predicate, IsString predicate) => Int -> Interp function predicate Int
mod_interp n =
  ([0..(n-1)],func,pred)
    where
      func f [] | f == fromString "0" = 0
      func f [] | f == fromString "1" = 1 `mod` n
      func f [x,y] | f == fromString "+" = (x + y) `mod` n
      func f [x,y] | f == fromString "*" = (x * y) `mod` n
      func _ _ = error "uninterpreted function"
      pred "=" [x,y] = x == y
      pred _ _ = error "uninterpreted predicate"

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

test01 :: Test
test01 = TestCase $ assertEqual "holds bool test (p. 126)" expected input
    where input = holds bool_interp Map.empty (for_all  "x" (vt "x" .=. fApp "False" [] .|. vt "x" .=. fApp "True" []) :: Formula (FOLEQ FName))
          expected = True
test02 :: Test
test02 = TestCase $ assertEqual "holds mod test 1 (p. 126)" expected input
    where input =  holds (mod_interp 2) Map.empty (for_all "x" (vt "x" .=. (fApp "0" []) .|. vt "x" .=. (fApp "1" [])) :: Formula (FOLEQ FName))
          expected = True
test03 :: Test
test03 = TestCase $ assertEqual "holds mod test 2 (p. 126)" expected input
    where input =  holds (mod_interp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .|. vt "x" .=. fApp "1" []) :: Formula (FOLEQ FName))
          expected = False

test04 :: Test
test04 = TestCase $ assertEqual "holds mod test 3 (p. 126)" expected input
    where input = filter (\ n -> holds (mod_interp n) Map.empty fm) [1..45]
                  where fm = for_all "x" ((.~.) (vt "x" .=. fApp "0" []) .=>. exists "y" (fApp "*" [vt "x", vt "y"] .=. fApp "1" [])) :: Formula (FOLEQ FName)
          expected = [1,2,3,5,7,11,13,17,19,23,29,31,37,41,43]

test05 :: Test
test05 = TestCase $ assertEqual "holds mod test 4 (p. 129)" expected input
    where input = holds (mod_interp 3) Map.empty ((for_all "x" (vt "x" .=. fApp "0" [])) .=>. fApp "1" [] .=. fApp "0" [] :: Formula (FOLEQ FName))
          expected = True
test06 :: Test
test06 = TestCase $ assertEqual "holds mod test 5 (p. 129)" expected input
    where input = holds (mod_interp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .=>. fApp "1" [] .=. fApp "0" []) :: Formula (FOLEQ FName))
          expected = False

-- | Free variables in terms and formulas.
fvt :: Term function -> Set V
fvt tm =
  case tm of
    Var x -> singleton x
    FApply _f args -> unions (map fvt args)

var :: Formula (FOL function) -> Set V
var fm =
   case fm of
    F -> Set.empty
    T -> Set.empty
    Atom (R _p args) -> unions (map fvt args)
    Not p -> var p
    And p q -> union (var p) (var q)
    Or p q -> union (var p) (var q)
    Imp p q -> union (var p) (var q)
    Iff p q -> union (var p) (var q)
    Forall x p -> Set.insert x (var p)
    Exists x p -> Set.insert x (var p)

fvFOL :: FOL function -> Set V
fvFOL (R _p args) = unions (map fvt args)

fvFOLEQ :: FOLEQ function -> Set V
fvFOLEQ (R' _p args) = unions (map fvt args)
fvFOLEQ (a :=: b) = union (fvt a) (fvt b)

fv :: (a -> Set V) -> Formula a -> Set V
fv fva fm =
  case fm of
    F -> Set.empty
    T -> Set.empty
    Atom a -> fva a
    Not p -> fv fva p
    And p q -> union (fv fva p) (fv fva q)
    Or p q -> union (fv fva p) (fv fva q)
    Imp p q -> union (fv fva p) (fv fva q)
    Iff p q -> union (fv fva p) (fv fva q)
    Forall x p -> difference (fv fva p) (singleton x)
    Exists x p -> difference (fv fva p) (singleton x)

-- | Universal closure of a formula.
generalize :: Formula (FOL function) -> Formula (FOL function)
generalize fm = Set.fold Forall fm (fv fvFOL fm)

-- | Substitution within terms.
tsubst :: Map V (Term function) -> Term function -> Term function
tsubst sfn tm =
  case tm of
    Var x -> fromMaybe tm (Map.lookup x sfn)
    FApply f args -> FApply f (map (tsubst sfn) args)

-- | Variant function and examples.
variant :: V -> Set V -> V
variant x@(V s) vars =
    if Set.member x vars then variant (V (s ++ "'")) vars else x

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

mapTermsFOL :: (Term function -> Term function) -> FOL function -> FOL function
mapTermsFOL f (R p args) = R p (map f args)

mapTermsFOLEQ :: (Term function -> Term function) -> FOLEQ function -> FOLEQ function
mapTermsFOLEQ f (R' p args) = R' p (map f args)
mapTermsFOLEQ f (a :=: b) = (f a :=: f b)

-- | Substitution in formulas, with variable renaming.
subst :: (a -> Set V) -> ((Term function -> Term function) -> a -> a) -> Map V (Term function) -> Formula a -> Formula a
subst fva mapTerms subfn fm =
  case fm of
    F -> F
    T -> T
    Atom a -> Atom (mapTerms (tsubst subfn) a)
    Not(p) -> Not (subst fva mapTerms subfn p)
    And p q -> And (subst fva mapTerms subfn p) (subst fva mapTerms subfn q)
    Or p q -> Or (subst fva mapTerms subfn p) (subst fva mapTerms subfn q)
    Imp p q -> Imp (subst fva mapTerms subfn p) (subst fva mapTerms subfn q)
    Iff p q -> Iff (subst fva mapTerms subfn p) (subst fva mapTerms subfn q)
    Forall x p -> substq fva mapTerms subfn Forall x p
    Exists x p -> substq fva mapTerms subfn Exists x p

substq :: (a -> Set V)
       -> ((Term function -> Term function) -> a -> a)
       -> Map V (Term function)
       -> (V -> Formula a -> Formula a)
       -> V
       -> Formula a
       -> Formula a
substq fva mapTerms subfn quant x p =
  let x' = if setAny (\y -> Set.member x (fvt(tryApplyD subfn y (Var y))))
                     (difference (fv fva p) (singleton x))
           then variant x (fv fva (subst fva mapTerms (undefine x subfn) p)) else x in
  quant x' (subst fva mapTerms ((x |-> Var x') subfn) p)


-- Examples.

test10 :: Test
test10 = TestCase $ assertEqual "subst (\"y\" |=> Var \"x\") <<forall x. x = y>>;;"
                                (for_all "x'" (Atom (Var "x'" :=: Var "x")))
                                (let (x, y) = (vt "x", vt "y") in
                                 subst fvFOLEQ mapTermsFOLEQ
                                       (Map.fromList [("y", Var "x")])
                                       (for_all "x" (x .=. y)) :: Formula (FOLEQ FName))

test11 :: Test
test11 = TestCase $ assertEqual "subst (\"y\" |=> Var \"x\") <<forall x x'. x = y ==> x = x'>>;;"
                                (for_all "x'" (for_all "x''" (Atom (Var "x'" :=: Var "x") .=>. (Atom (Var "x'" :=: Var "x''")))))
                                (let (x, x', y) = (vt "x", vt "x'", vt "y") in
                                 subst fvFOLEQ mapTermsFOLEQ
                                       (Map.fromList [("y", Var "x")])
                                       (for_all "x" (for_all "x'" ((x .=. y) .=>. (x .=. x'))) :: Formula (FOLEQ FName)))

tests :: Test
tests = TestLabel "FOL" $
        TestList [test00, test01, test02, test03, test04,
                  test05, test06, test07, test08, test09,
                  test10, test11]
