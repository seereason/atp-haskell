-- | Basic stuff for first order logic.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE GADTs, OverloadedStrings #-}
module FOL
    ( -- * Terms
      Term(Var, FApply), vt, fApp
    , FName(FName)
    , FOL(R), (.=.)
    , HasEquality(equals)
    , Predicate(NamedPredicate, Equals)
    , onformula
    , Interp
    -- * Semantics
    , termval
    , holds
    , bool_interp
    , mod_interp
    -- * Free Variables
    , var
    , fv
    , generalize
    -- * Substitution
    , subst, substq
    -- * Tests
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

-- | Terms are combined by predicates to build the atoms of a formula.
data Term function
    = Var V
    | FApply function [Term function]
    deriving (Eq, Ord, Show)

instance Pretty function => Pretty (Term function) where
    pPrint (Var v) = pPrint v
    pPrint (FApply fn []) = pPrint fn
    pPrint (FApply fn args) = pPrint fn <> text " [" <> mconcat (intersperse (text ", ") (map pPrint args)) <> "]"

-- | A simple type to use as the function parameter of Term, FOL, etc.
-- The only reason to use this instead of String is to get nicer
-- pretty printing.
newtype FName = FName String deriving (Eq, Ord)

instance IsString FName where fromString = FName

instance Show FName where show (FName s) = s

instance Pretty FName where pPrint (FName s) = text s

-- | Build a term from a variable.
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

-- | Class of predicates that have an equality predicate.
class HasEquality predicate where
    equals :: predicate

-- | Predicates with a 'HasEquality' instance are needed whenever the
-- '.=.' combiner is used.
instance HasEquality Predicate where
    equals = Equals

-- | First order logic formula atom type.
data FOL predicate function = R predicate [Term function] deriving (Eq, Ord, Show)

-- | This Predicate type includes an distinct Equals constructor, so
-- that we can build a HasEquality instance for it.
data Predicate
    = NamedPredicate String
    | Equals
    deriving (Eq, Ord, Show)

instance IsString Predicate where
    fromString = NamedPredicate

-- | Apply the equals predicate to two terms and build a formula.
(.=.) :: HasEquality predicate => (Term function) -> Term function -> Formula (FOL predicate function)
a .=. b = Atom (R equals [a, b])

infix 5 .=. -- , .!=., ≡, ≢

-- | Special case of applying a subfunction to the top *terms*.
onformula :: (Term function -> Term function) -> Formula (FOL predicate function) -> Formula (FOL predicate function)
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

-- | Specify the domain of a formula interpretation, and how to
-- interpret its functions and predicates.
data Interp function predicate d
    = Interp { domain :: [d]
             , funcApply :: function -> [d] -> d
             , predApply :: predicate -> [d] -> Bool }

-- | Semantics, implemented of course for finite domains only.
termval :: Interp function predicate a -> Map V a -> Term function -> a
termval m v tm =
  case tm of
    Var x -> fromMaybe (error ("Undefined variable: " ++ show x)) (Map.lookup x v)
    FApply f args -> funcApply m f (map (termval m v) args)

holds :: IsString predicate => Interp function predicate d -> Map V d -> Formula (FOL predicate function) -> Bool
holds m v fm =
  case fm of
    F -> False
    T -> True
    Atom (R r args) -> predApply m r (map (termval m v) args)
    Not p -> not  (holds m v p)
    And p q -> (holds m v p) && (holds m v q)
    Or p q -> (holds m v p) || (holds m v q)
    Imp p q -> (not (holds m v p)) || (holds m v q)
    Iff p q -> (holds m v p) == (holds m v q)
    Forall x p -> and (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- >>= return . any (== True)
    Exists x p -> or (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- return . all (== True)?

-- | Examples of particular interpretations.
bool_interp :: (Eq function, Show function, IsString function, Eq predicate, Show predicate, IsString predicate, HasEquality predicate) =>
               Interp function predicate Bool
bool_interp =
    Interp [False, True] func pred
    where
      func f [] | f == fromString "False" = False
      func f [] | f == fromString "True" = True
      func f [x,y] | f == fromString "+" = not(x == y)
      func f [x,y] | f == fromString "*" = x && y
      func f _ = error ("bool_interp - uninterpreted function: " ++ show f)
      pred p [x,y] | p == equals = x == y
      pred p _ = error ("bool_interp - uninterpreted predicate: " ++ show p)

mod_interp :: (Eq function, Show function, IsString function, Eq predicate, Show predicate, IsString predicate, HasEquality predicate) =>
              Int -> Interp function predicate Int
mod_interp n =
    Interp [0..(n-1)] func pred
    where
      func f [] | f == fromString "0" = 0
      func f [] | f == fromString "1" = 1 `mod` n
      func f [x,y] | f == fromString "+" = (x + y) `mod` n
      func f [x,y] | f == fromString "*" = (x * y) `mod` n
      func f _ = error ("mod_interp - uninterpreted function: " ++ show f)
      pred p [x,y] | p == equals = x == y
      pred p _ = error ("mod_interp - uninterpreted predicate: " ++ show p)

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
    where input = holds bool_interp Map.empty (for_all  "x" (vt "x" .=. fApp "False" [] .|. vt "x" .=. fApp "True" []) :: Formula (FOL Predicate FName))
          expected = True
test02 :: Test
test02 = TestCase $ assertEqual "holds mod test 1 (p. 126)" expected input
    where input =  holds (mod_interp 2) Map.empty (for_all "x" (vt "x" .=. (fApp "0" []) .|. vt "x" .=. (fApp "1" [])) :: Formula (FOL Predicate FName))
          expected = True
test03 :: Test
test03 = TestCase $ assertEqual "holds mod test 2 (p. 126)" expected input
    where input =  holds (mod_interp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .|. vt "x" .=. fApp "1" []) :: Formula (FOL Predicate FName))
          expected = False

test04 :: Test
test04 = TestCase $ assertEqual "holds mod test 3 (p. 126)" expected input
    where input = filter (\ n -> holds (mod_interp n) Map.empty fm) [1..45]
                  where fm = for_all "x" ((.~.) (vt "x" .=. fApp "0" []) .=>. exists "y" (fApp "*" [vt "x", vt "y"] .=. fApp "1" [])) :: Formula (FOL Predicate FName)
          expected = [1,2,3,5,7,11,13,17,19,23,29,31,37,41,43]

test05 :: Test
test05 = TestCase $ assertEqual "holds mod test 4 (p. 129)" expected input
    where input = holds (mod_interp 3) Map.empty ((for_all "x" (vt "x" .=. fApp "0" [])) .=>. fApp "1" [] .=. fApp "0" [] :: Formula (FOL Predicate FName))
          expected = True
test06 :: Test
test06 = TestCase $ assertEqual "holds mod test 5 (p. 129)" expected input
    where input = holds (mod_interp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .=>. fApp "1" [] .=. fApp "0" []) :: Formula (FOL Predicate FName))
          expected = False

-- Free variables in terms and formulas.

-- | Find the variables in a 'Term'.
fvt :: Term function -> Set V
fvt tm =
  case tm of
    Var x -> singleton x
    FApply _f args -> unions (map fvt args)

-- | Find the variables in a formula.
var :: Formula (FOL predicate function) -> Set V
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

-- | Find the free variables in a formula.
fv :: (atom ~ FOL predicate formula) => Formula atom -> Set V
fv fm =
  case fm of
    F -> Set.empty
    T -> Set.empty
    Atom (R _p args) -> unions (map fvt args)
    Not p -> fv p
    And p q -> union (fv p) (fv q)
    Or p q -> union (fv p) (fv q)
    Imp p q -> union (fv p) (fv q)
    Iff p q -> union (fv p) (fv q)
    Forall x p -> difference (fv p) (singleton x)
    Exists x p -> difference (fv p) (singleton x)

-- | Universal closure of a formula.
generalize :: Formula (FOL predicate function) -> Formula (FOL predicate function)
generalize fm = Set.fold Forall fm (fv fm)

-- | Substitution within terms.
tsubst :: Map V (Term function) -> Term function -> Term function
tsubst sfn tm =
  case tm of
    Var x -> fromMaybe tm (Map.lookup x sfn)
    FApply f args -> FApply f (map (tsubst sfn) args)

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
subst :: (atom ~ FOL predicate function) => Map V (Term function) -> Formula atom -> Formula atom
subst subfn fm =
  case fm of
    F -> F
    T -> T
    Atom (R p args) -> Atom (R p (map (tsubst subfn) args))
    Not(p) -> Not (subst subfn p)
    And p q -> And (subst subfn p) (subst subfn q)
    Or p q -> Or (subst subfn p) (subst subfn q)
    Imp p q -> Imp (subst subfn p) (subst subfn q)
    Iff p q -> Iff (subst subfn p) (subst subfn q)
    Forall x p -> substq subfn Forall x p
    Exists x p -> substq subfn Exists x p

substq :: (atom ~ FOL predicate function) => 
          Map V (Term function)
       -> (V -> Formula atom -> Formula atom)
       -> V
       -> Formula atom
       -> Formula atom
substq subfn quant x p =
  let x' = if setAny (\y -> Set.member x (fvt(tryApplyD subfn y (Var y))))
                     (difference (fv p) (singleton x))
           then variant x (fv (subst (undefine x subfn) p)) else x in
  quant x' (subst ((x |-> Var x') subfn) p)


-- Examples.

test10 :: Test
test10 =
    let [x, x', y] = [vt "x", vt "x'", vt "y"] in
    TestCase $ assertEqual "subst (\"y\" |=> Var \"x\") <<forall x. x = y>>;;"
                           (for_all "x'" (x' .=. x) :: Formula (FOL Predicate FName))
                           (subst (Map.fromList [("y", x)])
                                  (for_all "x" ((x .=. y))))

test11 :: Test
test11 =
    let [x, x', x'', y] = [vt "x", vt "x'", vt "x''", vt "y"] in
    TestCase $ assertEqual "subst (\"y\" |=> Var \"x\") <<forall x x'. x = y ==> x = x'>>;;"
                           (for_all "x'" (for_all "x''" ((x' .=. x) .=>. ((x' .=. x'')))) :: Formula (FOL Predicate FName))
                           (subst (Map.fromList [("y", x)])
                                  (for_all "x" (for_all "x'" ((x .=. y) .=>. (x .=. x')))))

tests :: Test
tests = TestLabel "FOL" $
        TestList [test00, test01, test02, test03, test04,
                  test05, test06, test07, test08, test09,
                  test10, test11]
