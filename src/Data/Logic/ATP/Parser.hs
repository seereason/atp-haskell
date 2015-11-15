{-# LANGUAGE CPP, NoMonomorphismRestriction, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, TypeFamilies #-}
module Data.Logic.ATP.Parser where

-- Parsing expressions and statements
-- https://wiki.haskell.org/Parsing_expressions_and_statements

import Control.Monad.Identity
import Data.Char (isSpace)
import Data.List (nub)
import Data.String (fromString)
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Text.Parsec
import Text.Parsec.Error
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import Text.PrettyPrint.HughesPJClass (Pretty(pPrint), text)

import Data.Logic.ATP.Apply
import Data.Logic.ATP.Equate
import Data.Logic.ATP.Formulas
import Data.Logic.ATP.Lit
import Data.Logic.ATP.Prop
import Data.Logic.ATP.Quantified
import Data.Logic.ATP.Skolem
import Data.Logic.ATP.Term

instance Pretty ParseError where
    pPrint = text . show

instance Pretty Message where
    pPrint (SysUnExpect s) = text ("SysUnExpect " ++ show s)
    pPrint (UnExpect s) = text ("UnExpect " ++ show s)
    pPrint (Expect s) = text ("Expect " ++ show s)
    pPrint (Message s) = text ("Message " ++ show s)

-- | QuasiQuote for a first order formula.  Loading this symbol into the interpreter
-- and setting -XQuasiQuotes lets you type expressions like [fof| ∃ x. p(x) |]
fof :: QuasiQuoter
fof = QuasiQuoter
    { quoteExp = \str -> [| (either (error . show) id . parseFOL) str :: Formula |]
    , quoteType = error "fof does not implement quoteType"
    , quotePat  = error "fof does not implement quotePat"
    , quoteDec  = error "fof does not implement quoteDec"
    }

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
pf :: QuasiQuoter
pf = QuasiQuoter
    { quoteExp = \str -> [| (either (error . show) id . parsePL) str :: PFormula EqAtom |]
    , quoteType = error "pf does not implement quoteType"
    , quotePat  = error "pf does not implement quotePat"
    , quoteDec  = error "pf does not implement quoteDec"
    }

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
lit :: QuasiQuoter
lit = QuasiQuoter
    { quoteExp = \str -> [| (either (error . show) id . parseLit) str :: LFormula EqAtom |]
    , quoteType = error "pf does not implement quoteType"
    , quotePat  = error "pf does not implement quotePat"
    , quoteDec  = error "pf does not implement quoteDec"
    }

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
term :: QuasiQuoter
term = QuasiQuoter
    { quoteExp = \str -> [| (either (error . show) id . parseFOLTerm) str :: FTerm |]
    , quoteType = error "term does not implement quoteType"
    , quotePat  = error "term does not implement quotePat"
    , quoteDec  = error "term does not implement quoteDec"
    }

#if 0
instance Read PrologRule where
   readsPrec _n str = [(parseProlog str,"")]

instance Read Formula where
   readsPrec _n str = [(parseFOL str,"")]

instance Read (PFormula EqAtom) where
   readsPrec _n str = [(parsePL str,"")]

parseProlog :: forall s. Stream s Identity Char => s -> PrologRule
parseProlog str = either (error . show) id $ parse prologparser "" str
#endif
parseFOL :: Stream String Identity Char => String -> Either ParseError Formula
parseFOL str = parse folparser "" (dropWhile isSpace str)
parsePL :: Stream String Identity Char => String -> Either ParseError (PFormula EqAtom)
parsePL str = parse propparser "" (dropWhile isSpace str)
parseLit :: Stream String Identity Char => String -> Either ParseError (LFormula EqAtom)
parseLit str = parse litparser "" (dropWhile isSpace str)
parseFOLTerm :: Stream String Identity Char => String -> Either ParseError FTerm
parseFOLTerm str = parse folsubterm "" (dropWhile isSpace str)

def :: forall s u m. Stream s m Char => GenLanguageDef s u m
def = emptyDef{ identStart = letter
              , identLetter = alphaNum <|> oneOf "'"
              , opStart = oneOf (nub (map head allOps))
              , opLetter = oneOf (nub (concat (map tail allOps)))
              , reservedOpNames = allOps
              , reservedNames = allIds
              }

m_parens :: forall t t1 t2. Stream t t2 Char => forall a. ParsecT t t1 t2 a -> ParsecT t t1 t2 a
m_angles :: forall t t1 t2. Stream t t2 Char => forall a. ParsecT t t1 t2 a -> ParsecT t t1 t2 a
m_symbol :: forall t t1 t2. Stream t t2 Char => String -> ParsecT t t1 t2 String
m_integer :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 Integer
m_identifier :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 String
m_reservedOp :: forall t t1 t2. Stream t t2 Char => String -> ParsecT t t1 t2 ()
m_reserved :: forall t t1 t2. Stream t t2 Char => String -> ParsecT t t1 t2 ()
m_whiteSpace :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 ()
TokenParser{ parens = m_parens
           , angles = m_angles
--           , brackets = m_brackets
           , symbol = m_symbol
           , integer = m_integer
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
--           , semiSep1 = m_semiSep1
           , whiteSpace = m_whiteSpace } = makeTokenParser def

#if 0
prologparser :: forall s u m. Stream s m Char => ParsecT s u m PrologRule
prologparser = try (do
   left <- folparser
   m_symbol ":-"
   right <- sepBy folparser (m_symbol ",")
   return (Prolog right left))
   <|> (do
   left <- folparser
   return (Prolog [] left))
   <?> "prolog expression"
#endif

litparser :: forall formula s u m. (JustLiteral formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
litparser = litexprparser litterm
propparser :: forall formula s u m. (JustPropositional formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
propparser = propexprparser propterm
folparser :: forall formula s u m. (IsQuantified formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
folparser = propexprparser folterm

litexprparser :: forall formula s u m. (IsLiteral formula, Stream s m Char) => ParsecT s u m formula -> ParsecT s u m formula
litexprparser trm = buildExpressionParser table trm <?> "lit"
 where
  table = [ [Prefix (m_reservedOp "~" >> return (.~.))]
          ]

propexprparser :: forall formula s u m. (IsPropositional formula, Stream s m Char) => ParsecT s u m formula -> ParsecT s u m formula
propexprparser trm = buildExpressionParser table trm <?> "prop"
 where
  table = [ map (\op -> Prefix (m_reservedOp op >> return (.~.))) notOps
          , map (\op -> Infix (m_reservedOp op >> return (.&.)) AssocRight) andOps -- should these be assocLeft?
          , map (\op -> Infix (m_reservedOp op >> return (.|.)) AssocRight) orOps
          , map (\op -> Infix (m_reservedOp op >> return (.=>.)) AssocRight) impOps
          , map (\op -> Infix (m_reservedOp op >> return (.<=>.)) AssocRight) iffOps
          ]

litterm :: forall formula s u m. (JustLiteral formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
litterm = try (m_parens litparser)
       <|> try folpredicate_infix
       <|> folpredicate
       <|> foldr1 (<|>) (map (\s -> m_reserved s >> return true) trueIds ++ map (\s -> m_reservedOp s >> return true) trueOps)
       <|> foldr1 (<|>) (map (\s -> m_reserved s >> return false) falseIds ++ map (\s -> m_reservedOp s >> return false) falseOps)

propterm :: forall formula s u m. (JustPropositional formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
propterm = try (m_parens propparser)
       <|> try folpredicate_infix
       <|> folpredicate
       <|> foldr1 (<|>) (map (\s -> m_reserved s >> return true) trueIds ++ map (\s -> m_reservedOp s >> return true) trueOps)
       <|> foldr1 (<|>) (map (\s -> m_reserved s >> return false) falseIds ++ map (\s -> m_reservedOp s >> return false) falseOps)

folterm :: forall formula s u m. (IsQuantified formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
folterm = try (m_parens folparser)
       <|> try folpredicate_infix
       <|> folpredicate
       <|> existentialQuantifier
       <|> forallQuantifier
       <|> foldr1 (<|>) (map (\s -> m_reserved s >> return true) trueIds ++ map (\s -> m_reservedOp s >> return true) trueOps)
       <|> foldr1 (<|>) (map (\s -> m_reserved s >> return false) falseIds ++ map (\s -> m_reservedOp s >> return false) falseOps)

existentialQuantifier :: forall formula s u m. (IsQuantified formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
existentialQuantifier = foldr1 (<|>) (map (\ s -> quantifierId s (exists . fromString)) existsIds ++ map (\ s -> quantifierOp s (exists . fromString)) existsOps)
forallQuantifier :: forall formula s u m. (IsQuantified formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
forallQuantifier = foldr1 (<|>) (map (\ s -> quantifierId s (for_all . fromString)) forallIds ++ map (\ s -> quantifierOp s (for_all . fromString)) forallOps)

quantifierId :: forall formula s u m. (IsQuantified formula, HasEquate (AtomOf formula), Stream s m Char) =>
              String -> (String -> formula -> formula) -> ParsecT s u m formula
quantifierId name op = do
   m_reserved name
   is <- many1 m_identifier
   _ <- m_symbol "."
   fm <- folparser
   return (foldr op fm is)

quantifierOp :: forall formula s u m. (IsQuantified formula, HasEquate (AtomOf formula), Stream s m Char) =>
              String -> (String -> formula -> formula) -> ParsecT s u m formula
quantifierOp name op = do
   m_reservedOp name
   is <- many1 m_identifier
   _ <- m_symbol "."
   fm <- folparser
   return (foldr op fm is)

folpredicate_infix :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
folpredicate_infix = choice (map (try . app) predicate_infix_symbols)
 where
  app op = do
   x <- folsubterm
   m_reservedOp op
   y <- folsubterm
   return (if elem op equateOps then x .=. y else pApp (fromString op) [x, y])

folpredicate :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
folpredicate = do
   p <- m_identifier <|> m_symbol "|--"
   xs <- option [] (m_parens (sepBy1 folsubterm (m_symbol ",")))
   return (pApp (fromString p) xs)

folfunction :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folfunction = do
   fname <- m_identifier
   xs <- m_parens (sepBy1 folsubterm (m_symbol ","))
   return (fApp (fromString fname) xs)

folconstant_numeric :: forall term t t1 t2. (IsTerm term, Stream t t2 Char) => ParsecT t t1 t2 term
folconstant_numeric = do
   i <- m_integer
   return (fApp (fromString . show $ i) [])

folconstant_reserved :: forall term t t1 t2. (IsTerm term, Stream t t2 Char) => String -> ParsecT t t1 t2 term
folconstant_reserved str = do
   m_reserved str
   return (fApp (fromString str) [])

folconstant :: forall term t t1 t2. (IsTerm term, Stream t t2 Char) => ParsecT t t1 t2 term
folconstant = do
   name <- m_angles m_identifier
   return (fApp (fromString name) [])

folsubterm :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folsubterm = folfunction_infix <|> folsubterm_prefix

folsubterm_prefix :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folsubterm_prefix =
   m_parens folfunction_infix
   <|> try folfunction
   <|> choice (map folconstant_reserved constants)
   <|> folconstant_numeric
   <|> folconstant
   <|> (fmap (vt . fromString) m_identifier)

folfunction_infix :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folfunction_infix = buildExpressionParser table folsubterm_prefix <?> "fof"
 where
  table = [ [Infix (m_reservedOp "::" >> return (\x y -> fApp (fromString "::") [x,y])) AssocRight]
          , [Infix (m_reservedOp "*" >> return (\x y -> fApp (fromString "*") [x,y])) AssocLeft, Infix (m_reservedOp "/" >> return (\x y -> fApp (fromString "/") [x,y])) AssocLeft]
          , [Infix (m_reservedOp "+" >> return (\x y -> fApp (fromString "+") [x,y])) AssocLeft, Infix (m_reservedOp "-" >> return (\x y -> fApp (fromString "-") [x,y])) AssocLeft]
          ]

allOps :: [String]
allOps = notOps ++ trueOps ++ falseOps ++ andOps ++ orOps ++ impOps ++ iffOps ++
         forallOps ++ existsOps ++ equateOps ++ provesOps ++ entailsOps ++ predicate_infix_symbols

allIds :: [String]
allIds = trueIds ++ falseIds ++ existsIds ++ forallIds ++ constants

predicate_infix_symbols :: [String]
predicate_infix_symbols = equateOps ++ ["<",">","<=",">="]

constants :: [[Char]]
constants = ["nil"]

equateOps = ["=", ".=."]
provesOps = ["⊢", "|--"]
entailsOps = ["⊨", "|=="]

notOps :: [String]
notOps = ["¬", "~", ".~."]

trueOps, trueIds, falseOps, falseIds, provesOps, entailsOps, equateOps :: [String]
trueOps = ["⊤"]
trueIds = ["True", "true"]
falseOps = ["⊥"]
falseIds = ["False", "false"]

andOps, orOps, impOps, iffOps :: [String]
andOps = [".&.", "&", "∧", "⋀", "/\\", "·"]
orOps = ["|", "∨", "⋁", "+", ".|.", "\\/"]
impOps = ["==>", "⇒", "⟹", ".=>.", "→", "⊃"]
iffOps = ["<==>", "⇔", ".<=>.", "↔"]

forallIds, forallOps, existsIds, existsOps :: [String]
forallIds = ["forall", "for_all"]
forallOps= ["∀"]
existsIds = ["exists"]
existsOps = ["∃"]
