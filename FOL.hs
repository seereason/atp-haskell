-- | Basic stuff for first order logic.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module FOL
    ( -- * Variables
      Variable(variant, prefix, prettyVariable), variants, showVariable, V(V)
    -- * Functions and Terms
    , Terms(vt, fApp, foldTerm, zipTerms), FName(FName), Term(Var, FApply)
    -- * Predicates
    , HasEquality(equals), Predicate(NamedPredicate, Equals)
    -- * Atoms
    , Atoms(appAtom, foldAtom), pApp , (.=.), FOL(R)
    -- * Quantifiers
    , Quant((:!:), (:?:))
    -- Formula
    , FirstOrderFormula(quant, foldFirstOrder), for_all, exists
    , Formula(F, T, Atom, Not, And, Or, Imp, Iff, Forall, Exists)
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

import Data.Bool (bool)
import Data.Data (Data)
import Data.List (intercalate, intersperse)
import Data.Map as Map (empty, fromList, insert, lookup, Map)
import Data.Maybe (fromMaybe)
import Data.Set as Set (difference, empty, fold, fromList, insert, member, Set, singleton, union, unions)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Formulas (BinOp(..), Combination(..), Constants(..), Negatable(..), (.~.), true, false, Combinable(..), Formulae(..), onatoms)
import Lib (setAny, tryApplyD, undefine, (|->))
import Prop (PropositionalFormula(foldPropositional))
import Prelude hiding (pred)
import Pretty (Doc, FixityDirection(InfixN, InfixL, InfixR), HasFixity(fixity), Fixity(Fixity), parens, Pretty(pPrint), prettyShow, text, topFixity, (<>))
import Test.HUnit

---------------
-- VARIABLES --
---------------

class (Ord v, IsString v, Data v, Pretty v) => Variable v where
    variant :: v -> Set.Set v -> v
    -- ^ Return a variable based on v but different from any set
    -- element.  The result may be v itself if v is not a member of
    -- the set.
    prefix :: String -> v -> v
    -- ^ Modify a variable by adding a prefix.  This unfortunately
    -- assumes that v is "string-like" but at least one algorithm in
    -- Harrison currently requires this.
    prettyVariable :: v -> Doc
    -- ^ Pretty print a variable

-- | Return an infinite list of variations on v
variants :: Variable v => v -> [v]
variants v0 =
    iter' Set.empty v0
    where iter' s v = let v' = variant v s in v' : iter' (Set.insert v s) v'

showVariable :: Variable v => v -> String
showVariable v = "(fromString (" ++ show (show (prettyVariable v)) ++ "))"

newtype V = V String deriving (Eq, Ord, Read, Data, Typeable)

instance Variable V where
    variant v@(V s) vs = if Set.member v vs then variant (V (s ++ "'")) vs else v
    prefix pre (V s) = V (pre ++ s)
    prettyVariable (V s) = text s

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

instance Pretty V where
    pPrint (V s) = text s

---------------
-- FUNCTIONS --
---------------

-- | A simple type to use as the function parameter of Term, FOL, etc.
-- The only reason to use this instead of String is to get nicer
-- pretty printing.
newtype FName = FName String deriving (Eq, Ord)

instance IsString FName where fromString = FName

instance Show FName where show (FName s) = s

instance Pretty FName where pPrint (FName s) = text s

-----------
-- TERMS --
-----------

-- | Terms are built from variables and combined by functions to build the atoms of a formula.
class (Ord term, Variable v, Eq function) => Terms term v function | term -> v function where
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

data Term function v
    = Var v
    | FApply function [Term function v]
    deriving (Eq, Ord)

instance (Ord function, Show function, Variable v, Show v) => Show (Term function v) where
    show = showTerm

showTerm :: (Terms term function v, Show function, Show v) => term -> String
showTerm = foldTerm (\v -> "vt " ++ show v) (\ fn ts -> "fApp " ++ show fn ++ "[" ++ intercalate ", " (map showTerm ts) ++ "]")

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

instance (Pretty function, Pretty v) => Pretty (Term function v) where
    pPrint (Var v) = pPrint v
    pPrint (FApply fn []) = pPrint fn
    pPrint (FApply fn args) = pPrint fn <> text " [" <> mconcat (intersperse (text ", ") (map pPrint args)) <> "]"

-- Example.
test00 :: Test
test00 = TestCase $ assertEqual "print an expression"
                                "sqrt [- [1, cos [power [+ [x, y], 2]]]]"
                                (prettyShow (fApp "sqrt" [fApp "-" [fApp "1" [],
                                                                     fApp "cos" [fApp "power" [fApp "+" [Var "x", Var "y"],
                                                                                               fApp "2" []]]]] :: Term FName V))

---------------
-- PREDICATE --
----------------

-- | Class of predicates that have an equality predicate.
class HasEquality predicate where
    equals :: predicate

-- | This Predicate type includes an distinct Equals constructor, so
-- that we can build a HasEquality instance for it.
data Predicate
    = NamedPredicate String
    | Equals
    deriving (Eq, Ord, Show)

-- | Predicates with a 'HasEquality' instance are needed whenever the
-- '.=.' combiner is used.
instance HasEquality Predicate where
    equals = Equals

instance IsString Predicate where
    fromString = NamedPredicate

instance Pretty Predicate where
    pPrint Equals = text "="
    pPrint (NamedPredicate "=") = error "Use of = as a predicate name is prohibited"
    pPrint (NamedPredicate s) = text s

----------
-- ATOM --
----------

class Atoms atom predicate term | atom -> predicate term where
    appAtom :: predicate -> [term] -> atom
    foldAtom :: (predicate -> [term] -> r) -> atom -> r

-- | First order logic formula atom type.
data FOL predicate term = R predicate [term] deriving (Eq, Ord)

instance (Pretty predicate, Show predicate, Show term) => Show (FOL predicate term) where
    show (R p ts) = "appAtom " ++ show p ++ " [" ++ intercalate ", " (map show ts) ++ "]"
{-
showAtom :: (Pretty predicate, Show predicate, Show term) => Atoms atom predicate term => atom -> String
showAtom = foldAtom showPApp
    where
      showPApp p [a, b] | pPrint p == text "=" = "(" ++ show a ++ ") .=. (" ++ show b ++ ")"
      showPApp p ts = "pApp (" ++ show p ++ ") [" ++ intercalate ", " (map show ts) ++ "]"
-}
instance Atoms (FOL predicate term) predicate term where
    appAtom = R
    foldAtom f (R p ts) = f p ts

-- | The type of the predicate determines how this atom is pretty
-- printed - specifically, whether it is an instance of HasEquality.
-- So we need to do some gymnastics to make this happen.
instance (Pretty predicate, Pretty term) => Pretty (FOL predicate term) where
    pPrint = foldAtom (\ p ts -> if pPrint p == text "="
                                 then error "illegal pretty printer for predicate"
                                 else pPrint p <> text "[" <> mconcat (intersperse (text ", ") (map pPrint ts)) <> text "]")

instance HasFixity (FOL predicate term) where
    fixity _ = Fixity 6 InfixN

----------------
-- QUANTIFIER --
----------------

data Quant
    = (:!:) -- ^ for_all
    | (:?:) -- ^ exists
    deriving (Eq, Ord, Data, Typeable)

--------------
-- FORMULAE --
--------------

data Formula atom
    = F
    | T
    | Atom atom
    | Not (Formula atom)
    | And (Formula atom) (Formula atom)
    | Or (Formula atom) (Formula atom)
    | Imp (Formula atom) (Formula atom)
    | Iff (Formula atom) (Formula atom)
    | Forall V (Formula atom)
    | Exists V (Formula atom)
    deriving (Eq, Ord, Read)

instance Constants (Formula atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance Negatable (Formula atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance Combinable (Formula atom) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff

-- Display formulas using infix notation
instance Show atom => Show (Formula atom) where
    show F = "false"
    show T = "true"
    show (Atom atom) = show atom
    show (Not f) = "(.~.) (" ++ show f ++ ")"
    show (And f g) = "(" ++ show f ++ ") .&. (" ++ show g ++ ")"
    show (Or f g) = "(" ++ show f ++ ") .|. (" ++ show g ++ ")"
    show (Imp f g) = "(" ++ show f ++ ") .=>. (" ++ show g ++ ")"
    show (Iff f g) = "(" ++ show f ++ ") .<=>. (" ++ show g ++ ")"
    show (Forall v f) = "(for_all " ++ show v ++ " " ++ show f ++ ")"
    show (Exists v f) = "(exists " ++ show v ++ " " ++ show f ++ ")"

instance HasFixity atom => HasFixity (Formula atom) where
    fixity T = Fixity 10 InfixN
    fixity F = Fixity 10 InfixN
    fixity (Atom a) = fixity a
    fixity (Not _) = Fixity 5 InfixN
    fixity (And _ _) = Fixity 4 InfixL
    fixity (Or _ _) = Fixity 3 InfixL
    fixity (Imp _ _) = Fixity 2 InfixR
    fixity (Iff _ _) = Fixity 1 InfixL
    fixity (Forall _ _) = Fixity 9 InfixN
    fixity (Exists _ _) = Fixity 9 InfixN

-- | Use a predicate to combine some terms into a formula.
pApp :: (Formulae formula atom, Atoms atom predicate term) => predicate -> [term] -> formula
pApp p args = atomic $ appAtom p args

-- | Apply the equals predicate to two terms and build a formula.
(.=.) :: (Formulae formula atom, Atoms atom predicate term, HasEquality predicate) => term -> term -> formula
a .=. b = atomic (appAtom equals [a, b])

infix 5 .=. -- , .!=., ≡, ≢

--instance (Ord atom, HasFixity atom, Pretty atom) => Pretty (Formula atom) where
--    pPrint fm = prettyFirstOrder pPrint topFixity fm

instance Formulae (Formula atom) atom where
    atomic = Atom
    foldAtoms f fm b =
      case fm of
        Atom a -> f a b
        Not p -> foldAtoms f p b
        And p q -> foldAtoms f p (foldAtoms f q b)
        Or p q -> foldAtoms f p (foldAtoms f q b)
        Imp p q -> foldAtoms f p (foldAtoms f q b)
        Iff p q -> foldAtoms f p (foldAtoms f q b)
        Forall _x p -> foldAtoms f p b
        Exists _x p -> foldAtoms f p b
        _ -> b
    mapAtoms f fm =
      case fm of
        Atom a -> f a
        Not p -> Not (mapAtoms f p)
        And p q -> And (mapAtoms f p) (mapAtoms f q)
        Or p q -> Or (mapAtoms f p) (mapAtoms f q)
        Imp p q -> Imp (mapAtoms f p) (mapAtoms f q)
        Iff p q -> Iff (mapAtoms f p) (mapAtoms f q)
        Forall x p -> Forall x (mapAtoms f p)
        Exists x p -> Exists x (mapAtoms f p)
        _ -> fm

instance Ord atom => PropositionalFormula (Formula atom) atom where
    foldPropositional co tf at fm =
        case fm of
          T -> tf True
          F -> tf False
          Atom a -> at a
          Not p -> co ((:~:) p)
          And p q -> co (BinOp p (:&:) q)
          Or p q -> co (BinOp p (:|:) q)
          Imp p q -> co (BinOp p (:=>:) q)
          Iff p q -> co (BinOp p (:<=>:) q)
          -- Although every instance of FirstOrderFormula is also an
          -- instance of PropositionalFormula, we see here that it is
          -- an error to use foldPropositional (PropositionalFormula's
          -- only method) on a Formula that has quantifiers.
          Forall _ _ -> error $ "foldPropositional used on Formula with a quantifier"
          Exists _ _ -> error $ "foldPropositional used on Formula with a quantifier"

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

instance (Ord atom, HasFixity atom, Pretty atom) => Pretty (Formula atom) where
    pPrint fm = prettyFirstOrder topFixity fm

prettyFirstOrder :: (FirstOrderFormula formula atom v, Pretty atom, HasFixity formula) => Fixity -> formula -> Doc
prettyFirstOrder pfix fm =
    bool id parens (pfix > fix) $ foldFirstOrder qu co tf at fm
        where
          fix = fixity fm
          qu (:!:) x p = text ("∀" ++ prettyShow x ++ ". ") <> prettyFirstOrder fix p
          qu (:?:) x p = text ("∃" ++ prettyShow x ++ ". ") <> prettyFirstOrder fix p
          co ((:~:) f) = text "¬" <> prettyFirstOrder fix f
          co (BinOp f (:&:) g) = prettyFirstOrder fix f <> text "∧" <> prettyFirstOrder fix g
          co (BinOp f (:|:) g) = prettyFirstOrder fix f <> text "∨" <> prettyFirstOrder fix g
          co (BinOp f (:=>:) g) = prettyFirstOrder fix f <> text "⇒" <> prettyFirstOrder fix g
          co (BinOp f (:<=>:) g) = prettyFirstOrder fix f <> text "⇔" <> prettyFirstOrder fix g
          tf = pPrint
          at = pPrint

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

type MyAtom = FOL Predicate (Term FName V)
type MyFormula = Formula MyAtom

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
