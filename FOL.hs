-- | Basic stuff for first order logic.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module FOL
    ( -- * Terms
      Terms(vt, fApp, foldTerm, zipTerms)
    , HasEquality(equals)
    -- * Instance
    , Term(Var, FApply)
    , FName(FName)
    , Predicate(NamedPredicate, Equals)
    , FOL(R)
    , MyFormula
    -- First Order Formulae
    , Atoms(appAtom, foldAtom), pApp , (.=.)
    , FirstOrderFormula(quant, foldFirstOrder), for_all, exists
    , convertFirstOrder
    , onformula
    -- * Semantics
    , Interp
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
import Lib.Pretty (HasFixity(fixity))
import Data.List (intersperse)
import Data.Map as Map (empty, fromList, insert, lookup, Map)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Set as Set (difference, empty, fold, fromList, insert, member, Set, singleton, union, unions)
import Data.String (IsString(fromString))
import Language.Haskell.TH.Syntax as TH (Fixity(Fixity), FixityDirection(InfixN))
import Prop (PropositionalFormula(foldPropositional))
import Prelude hiding (pred)
import Test.HUnit
import Text.PrettyPrint.HughesPJClass (Pretty(pPrint), prettyShow, text)

class (Ord term,  -- For implementing Ord in Literal
       Variable v,
       Eq function
      ) => Terms term v function | term -> v function where
    vt :: v -> term
    -- ^ Build a term which is a variable reference.
    fApp :: function -> [term] -> term
    -- ^ Build a term by applying terms to an atomic function.  @f@
    -- (atomic function) is one of the type parameters, this package
    -- is mostly indifferent to its internal structure.
    foldTerm :: (v -> r) -> (function -> [term] -> r) -> term -> r
    -- ^ A fold for the term data type, which understands terms built
    -- from a variable and a term built from the application of a
    -- primitive function to other terms.
    zipTerms :: (v -> v -> Maybe r) -> (function -> [term] -> function -> [term] -> Maybe r) -> term -> term -> Maybe r
    -- ^ Combine two terms if they are similar (i.e. two variables or
    -- two function applications.)

instance (Ord function, Variable v) => Terms (Term function v) v function where
    vt = Var
    fApp = FApply
    foldTerm vf fn t =
        case t of
          Var v -> vf v
          FApply f ts -> fn f ts
    zipTerms v f t1 t2 =
        case (t1, t2) of
          (Var v1, Var v2) -> v v1 v2
          (FApply f1 ts1, FApply f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing

-- | Terms are combined by predicates to build the atoms of a formula.
data Term function v
    = Var v
    | FApply function [Term function v]
    deriving (Eq, Ord, Show)

instance (Pretty function, Pretty v) => Pretty (Term function v) where
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

-- Example.
test00 :: Test
test00 = TestCase $ assertEqual "print an expression"
                                "sqrt [- [1, cos [power [+ [x, y], 2]]]]"
                                (prettyShow (fApp "sqrt" [fApp "-" [fApp "1" [],
                                                                     fApp "cos" [fApp "power" [fApp "+" [Var "x", Var "y"],
                                                                                               fApp "2" []]]]] :: Term FName V))

-- | Class of predicates that have an equality predicate.
class HasEquality predicate where
    equals :: predicate

-- | Predicates with a 'HasEquality' instance are needed whenever the
-- '.=.' combiner is used.
instance HasEquality Predicate where
    equals = Equals

class Atoms atom predicate term | atom -> predicate term where
    appAtom :: predicate -> [term] -> atom
    foldAtom :: (predicate -> [term] -> r) -> atom -> r

-- | First order logic formula atom type.
data FOL predicate term = R predicate [term] deriving (Eq, Ord, Show)

instance Atoms (FOL predicate term) predicate term where
    appAtom = R
    foldAtom f (R p ts) = f p ts

-- | This Predicate type includes an distinct Equals constructor, so
-- that we can build a HasEquality instance for it.
data Predicate
    = NamedPredicate String
    | Equals
    deriving (Eq, Ord, Show)

instance IsString Predicate where
    fromString = NamedPredicate

instance Pretty Predicate where
    pPrint Equals = text "="
    pPrint (NamedPredicate "=") = error "Use of = as a predicate name is prohibited"
    pPrint (NamedPredicate s) = text s

instance HasFixity (FOL predicate term) where
    fixity _ = Fixity 6 InfixN

-- | The type of the predicate determines how this atom is pretty
-- printed - specifically, whether it is an instance of HasEquality.
-- So we need to do some gymnastics to make this happen.
instance (Pretty predicate, Pretty term) => Pretty (FOL predicate term) where
    pPrint = foldAtom (\ p ts -> if pPrint p == text "="
                                 then error "illegal pretty printer for predicate"
                                 else pPrint p <> text "[" <> mconcat (intersperse (text ", ") (map pPrint ts)) <> text "]")

-- | Use a predicate to combine some terms into a formula.
pApp :: (Formulae formula atom, Atoms atom predicate term) => predicate -> [term] -> formula
pApp p args = atomic $ appAtom p args

-- | Apply the equals predicate to two terms and build a formula.
(.=.) :: (Formulae formula atom, Atoms atom predicate term, HasEquality predicate) => term -> term -> formula
a .=. b = atomic (appAtom equals [a, b])

infix 5 .=. -- , .!=., ≡, ≢

class (PropositionalFormula formula atom, Variable v) => FirstOrderFormula formula atom v | formula -> atom, formula -> v where
    quant :: Quant -> v -> formula -> formula
    foldFirstOrder :: (Quant -> v -> formula -> r)
                   -> (Combination formula -> r)
                   -> (Bool -> r)
                   -> (atom -> r)
                   -> formula -> r

-- | Use foldPropositional to convert any instance of
-- PropositionalFormula to any other by specifying the result type.
convertFirstOrder :: forall f1 a1 v1 f2 a2 v2.
                     (FirstOrderFormula f1 a1 v1, FirstOrderFormula f2 a2 v2) =>
                     (a1 -> a2) -> (v1 -> v2) -> f1 -> f2
convertFirstOrder ca cv f1 =
    foldFirstOrder qu co tf at f1
    where
      qu :: Quant -> v1 -> f1 -> f2
      qu (:!:) x p = for_all (cv x) (convertFirstOrder ca cv p :: f2)
      qu (:?:) x p = exists (cv x) (convertFirstOrder ca cv p :: f2)
      co :: Combination f1 -> f2
      co ((:~:) p) = (.~.) (convertFirstOrder ca cv p)
      co (BinOp p (:&:) q) = convertFirstOrder ca cv p .&. convertFirstOrder ca cv q
      co (BinOp p (:|:) q) = convertFirstOrder ca cv p .|. convertFirstOrder ca cv q
      co (BinOp p (:=>:) q) = convertFirstOrder ca cv p .=>. convertFirstOrder ca cv q
      co (BinOp p (:<=>:) q) = convertFirstOrder ca cv p .<=>. convertFirstOrder ca cv q
      tf :: Bool -> f2
      tf = fromBool
      at :: a1 -> f2
      at = atomic . ca

for_all :: FirstOrderFormula formula atom v => v -> formula -> formula
for_all = quant (:!:)
exists :: FirstOrderFormula formula atom v => v -> formula -> formula
exists = quant (:?:)

instance Ord atom => FirstOrderFormula (Formula atom) atom V where
    quant (:!:) = Forall
    quant (:?:) = Exists
    foldFirstOrder qu co tf at fm =
        case fm of
          Forall v p -> qu (:!:) v p
          Exists v p -> qu (:?:) v p
          _ -> foldPropositional co tf at fm

-- | Special case of applying a subfunction to the top *terms*.
onformula :: (Formulae formula r, Atoms r predicate term) => (term -> term) -> formula -> formula
onformula f = onatoms (foldAtom (\p a -> atomic $ appAtom p (map f a)))

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
termval :: (Show v, Terms term v function) => Interp function predicate r -> Map v r -> term -> r
termval m v tm =
    foldTerm (\x -> fromMaybe (error ("Undefined variable: " ++ show x)) (Map.lookup x v))
             (\f args -> funcApply m f (map (termval m v) args)) tm

holds :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function, Show v) =>
         Interp function predicate dom -> Map v dom -> formula -> Bool
holds m v fm =
    foldFirstOrder qu co tf at fm
    where
      qu (:!:) x p = and (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- >>= return . any (== True)
      qu (:?:) x p = or (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- return . all (== True)?
      co ((:~:) p) = not (holds m v p)
      co (BinOp p (:&:) q) = (holds m v p) && (holds m v q)
      co (BinOp p (:|:) q) = (holds m v p) || (holds m v q)
      co (BinOp p (:=>:) q) = not (holds m v p) || (holds m v q)
      co (BinOp p (:<=>:) q) = (holds m v p) == (holds m v q)
      tf x = x
      at = foldAtom (\r args -> predApply m r (map (termval m v) args))

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

type MyFormula = Formula (FOL Predicate (Term FName V))

test01 :: Test
test01 = TestCase $ assertEqual "holds bool test (p. 126)" expected input
    where input = holds bool_interp Map.empty (for_all  "x" (vt "x" .=. fApp "False" [] .|. vt "x" .=. fApp "True" []) :: MyFormula)
          expected = True
test02 :: Test
test02 = TestCase $ assertEqual "holds mod test 1 (p. 126)" expected input
    where input =  holds (mod_interp 2) Map.empty (for_all "x" (vt "x" .=. (fApp "0" []) .|. vt "x" .=. (fApp "1" [])) :: MyFormula)
          expected = True
test03 :: Test
test03 = TestCase $ assertEqual "holds mod test 2 (p. 126)" expected input
    where input =  holds (mod_interp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .|. vt "x" .=. fApp "1" []) :: MyFormula)
          expected = False

test04 :: Test
test04 = TestCase $ assertEqual "holds mod test 3 (p. 126)" expected input
    where input = filter (\ n -> holds (mod_interp n) Map.empty fm) [1..45]
                  where fm = for_all "x" ((.~.) (vt "x" .=. fApp "0" []) .=>. exists "y" (fApp "*" [vt "x", vt "y"] .=. fApp "1" [])) :: MyFormula
          expected = [1,2,3,5,7,11,13,17,19,23,29,31,37,41,43]

test05 :: Test
test05 = TestCase $ assertEqual "holds mod test 4 (p. 129)" expected input
    where input = holds (mod_interp 3) Map.empty ((for_all "x" (vt "x" .=. fApp "0" [])) .=>. fApp "1" [] .=. fApp "0" [] :: MyFormula)
          expected = True
test06 :: Test
test06 = TestCase $ assertEqual "holds mod test 5 (p. 129)" expected input
    where input = holds (mod_interp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .=>. fApp "1" [] .=. fApp "0" []) :: MyFormula)
          expected = False

-- Free variables in terms and formulas.

-- | Find the variables in a 'Term'.
fvt :: Terms term v function => term -> Set v
fvt tm = foldTerm singleton (\_ args -> unions (map fvt args)) tm

-- | Find the variables in a formula.
var :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) => formula -> Set v
var fm =
    foldFirstOrder qu co tf at fm
    where
      qu _ x p = Set.insert x (var p)
      co ((:~:) p) = var p
      co (BinOp p _ q) = union (var p) (var q)
      tf _ = Set.empty
      at = foldAtom (\_ args -> unions (map fvt args))

-- | Find the free variables in a formula.
fv :: (FirstOrderFormula formula atom v, Atoms atom predicate term,  Terms term v function) =>
      formula -> Set v
fv fm =
    foldFirstOrder qu co tf at fm
    where
      qu _ x p = difference (fv p) (singleton x)
      co ((:~:) p) = fv p
      co (BinOp p _ q) = union (fv p) (fv q)
      tf _ = Set.empty
      at = foldAtom (\_ args -> unions (map fvt args))

-- | Universal closure of a formula.
generalize :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) =>
              formula -> formula
generalize fm = Set.fold for_all fm (fv fm)

-- | Substitution within terms.
tsubst :: Terms term v function => Map v term -> term -> term
tsubst sfn tm =
    foldTerm (\x -> fromMaybe tm (Map.lookup x sfn))
             (\f args -> fApp f (map (tsubst sfn) args))
             tm

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
subst :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) =>
         Map v term -> formula -> formula
subst subfn fm =
    foldFirstOrder qu co tf at fm
    where
      qu (:!:) x p = substq subfn for_all x p
      qu (:?:) x p = substq subfn exists x p
      co ((:~:) p) = (.~.) (subst subfn p)
      co (BinOp p (:&:) q) = (subst subfn p) .&. (subst subfn q)
      co (BinOp p (:|:) q) = (subst subfn p) .|. (subst subfn q)
      co (BinOp p (:=>:) q) = (subst subfn p) .=>. (subst subfn q)
      co (BinOp p (:<=>:) q) = (subst subfn p) .<=>. (subst subfn q)
      tf False = false
      tf True = true
      at = foldAtom (\p args -> atomic (appAtom p (map (tsubst subfn) args)))

substq :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) =>
          Map v term
       -> (v -> formula -> formula)
       -> v
       -> formula
       -> formula
substq subfn qu x p =
  let x' = if setAny (\y -> Set.member x (fvt(tryApplyD subfn y (vt y))))
                     (difference (fv p) (singleton x))
           then variant x (fv (subst (undefine x subfn) p)) else x in
  qu x' (subst ((x |-> vt x') subfn) p)


-- Examples.

test10 :: Test
test10 =
    let [x, x', y] = [vt "x", vt "x'", vt "y"] in
    TestCase $ assertEqual "subst (\"y\" |=> Var \"x\") <<forall x. x = y>>;;"
                           (for_all "x'" (x' .=. x) :: MyFormula)
                           (subst (Map.fromList [("y", x)])
                                  (for_all "x" ((x .=. y))))

test11 :: Test
test11 =
    let [x, x', x'', y] = [vt "x", vt "x'", vt "x''", vt "y"] in
    TestCase $ assertEqual "subst (\"y\" |=> Var \"x\") <<forall x x'. x = y ==> x = x'>>;;"
                           (for_all "x'" (for_all "x''" ((x' .=. x) .=>. ((x' .=. x'')))) :: MyFormula)
                           (subst (Map.fromList [("y", x)])
                                  (for_all "x" (for_all "x'" ((x .=. y) .=>. (x .=. x')))))

tests :: Test
tests = TestLabel "FOL" $
        TestList [test00, test01, test02, test03, test04,
                  test05, test06, test07, test08, test09,
                  test10, test11]
