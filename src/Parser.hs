-- | Formula parser.  This should be the inverse of the formula pretty printer.

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Parser
    ( fof, parseFOL
    , pf, parsePF
    , lit, parseLit
    , term, parseFOLTerm
    ) where

-- Parsing expressions and statements
-- https://wiki.haskell.org/Parsing_expressions_and_statements

import Control.Monad.Identity
import Data.Char (isSpace)
import Data.String (fromString)
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Text.Parsec
--import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

import Term (fApp, FTerm, IsTerm(FunOf, vt), IsVariable)

#if 1
import Apply (pApp, HasApply(PredOf))
import Equate ((.=.), EqAtom, HasEquate)
import Formulas (IsFormula(AtomOf), true, false)

#if 1
import Lit ((.~.), IsLiteral, JustLiteral, LFormula)

#if 1
import Prop ((.&.), (.|.), (.=>.), (.<=>.), IsPropositional, JustPropositional, PFormula)

#if 1
import FOL (IsFirstOrder)
import Quantified (exists, for_all, IsQuantified)
import Skolem (Formula)

-- | QuasiQuote for a first order formula.  Loading this symbol into the interpreter
-- and setting -XQuasiQuotes lets you type expressions like [fof| ∃ x. p(x) |]
fof :: QuasiQuoter
fof = QuasiQuoter
    { quoteExp = \str -> [| parseFOL (dropWhile isSpace str) :: Formula |]
    , quoteType = error "fofQQ does not implement quoteType"
    , quotePat  = error "fofQQ does not implement quotePat"
    , quoteDec  = error "fofQQ does not implement quoteDec"
    }

-- parseProlog :: forall s lit. Stream s Identity Char => s -> PrologRule lit
-- parseProlog str = either (error . show) id $ parse prologparser "" str
parseFOL :: (IsFirstOrder formula, HasEquate (AtomOf formula), Stream String Identity Char) => String -> formula
parseFOL str = either (error . show) id $ parse (exprparser folexprtable) "" str

-- prologparser :: forall s u m lit. Stream s m Char => ParsecT s u m (PrologRule lit)
-- prologparser = try (do
--    left <- folparser
--    m_symbol ":-"
--    right <- map markLiteral <$> sepBy folparser (m_symbol ",")
--    return (Prolog (fromList right) left))
--    <|> (do
--    left <- markLiteral <$> folparser
--    return (Prolog mempty left))
--    <?> "prolog expression"

folexprtable :: (IsQuantified formula, Stream s m Char) => [[Operator s u m formula]]
folexprtable =
    -- ∀x. ∃y. x=y becomes ∀x. (∃y. (x=y))
    -- ∃x. ∀y. x=y is a parse error
    propexprtable ++ [ [Prefix existentialPrefix]
                     , [Prefix forallPrefix] ]
    where
      existentialPrefix :: forall formula s u m. (IsQuantified formula, Stream s m Char) => ParsecT s u m (formula -> formula)
      existentialPrefix = quantifierPrefix "∃" exists <|> quantifierPrefix "exists" exists
      forallPrefix :: forall formula s u m. (IsQuantified formula, Stream s m Char) => ParsecT s u m (formula -> formula)
      forallPrefix = quantifierPrefix "∀" for_all <|> quantifierPrefix "for_all" for_all <|> quantifierPrefix "forall" for_all

      quantifierPrefix :: forall formula v s u m. (IsVariable v, Stream s m Char) => String -> (v -> formula -> formula) -> ParsecT s u m (formula -> formula)
      quantifierPrefix name op = do
        m_reservedOp name
        is <- map fromString <$> many1 m_identifier
        _ <- m_symbol "."
        return (\fm -> foldr op fm is)
#endif

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
pf :: QuasiQuoter
pf = QuasiQuoter
    { quoteExp = \str -> [| parsePF (dropWhile isSpace str) :: PFormula EqAtom |]
    , quoteType = error "pfQQ does not implement quoteType"
    , quotePat  = error "pfQQ does not implement quotePat"
    , quoteDec  = error "pfQQ does not implement quoteDec"
    }

parsePF :: (JustPropositional formula, HasEquate (AtomOf formula), Stream String Identity Char) => String -> formula
parsePF str = either (error . show) id $ parse (exprparser propexprtable) "" str

propexprtable :: (IsPropositional a, Stream s m Char) => [[Operator s u m a]]
propexprtable =
          litexprtable ++
          [ [Infix (m_reservedOp ".&." >> return (.&.)) AssocRight,
             Infix (m_reservedOp "&" >> return (.&.)) AssocRight,
             Infix (m_reservedOp "∧" >> return (.&.)) AssocRight,
             Infix (m_reservedOp "⋀" >> return (.&.)) AssocRight,
             Infix (m_reservedOp "/\\" >> return (.&.)) AssocRight,
             Infix (m_reservedOp "·" >> return (.&.)) AssocRight]

          , [Infix (m_reservedOp ".|." >> return (.|.)) AssocRight,
             Infix (m_reservedOp "|" >> return (.|.)) AssocRight,
             Infix (m_reservedOp "∨" >> return (.|.)) AssocRight,
             Infix (m_reservedOp "⋁" >> return (.|.)) AssocRight,
             Infix (m_reservedOp "\\/" >> return (.|.)) AssocRight,
             Infix (m_reservedOp "+" >> return (.|.)) AssocRight]

          , [Infix (m_reservedOp ".=>." >> return (.=>.)) AssocRight,
             Infix (m_reservedOp "==>" >> return (.=>.)) AssocRight,
             Infix (m_reservedOp "⇒" >> return (.=>.)) AssocRight,
             Infix (m_reservedOp "⟹" >> return (.=>.)) AssocRight,
             Infix (m_reservedOp "→" >> return (.=>.)) AssocRight,
             Infix (m_reservedOp "⊃" >> return (.=>.)) AssocRight]

          , [Infix (m_reservedOp ".<=>." >> return (.<=>.)) AssocRight,
             Infix (m_reservedOp "<==>" >> return (.<=>.)) AssocRight,
             Infix (m_reservedOp "⇔" >> return (.<=>.)) AssocRight,
             Infix (m_reservedOp "↔" >> return (.<=>.)) AssocRight,
             Infix (m_reservedOp "≡" >> return (.<=>.)) AssocRight]
          ]
#endif

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
lit :: QuasiQuoter
lit = QuasiQuoter
    { quoteExp = \str -> [| parseLit (dropWhile isSpace str) :: LFormula EqAtom |]
    , quoteType = error "pfQQ does not implement quoteType"
    , quotePat  = error "pfQQ does not implement quotePat"
    , quoteDec  = error "pfQQ does not implement quoteDec"
    }

parseLit :: (JustLiteral formula, HasEquate (AtomOf formula), Stream String Identity Char) => String -> formula
parseLit str = either (error . show) id $ parse (exprparser litexprtable) "" str

litexprtable :: (IsLiteral a, Stream s m Char) => [[Operator s u m a]]
litexprtable =
           [ [Prefix (m_reservedOp ".~." >> return (.~.)),
              Prefix (m_reservedOp "~" >> return (.~.)),
              Prefix (m_reservedOp "¬" >> return (.~.))] ]
#endif

parseTerm :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) =>
              [[Operator s u m formula]] -> ParsecT s u m formula
parseTerm exprtable =
    try (m_parens (exprparser exprtable))
       <|> try folpredicate_infix
       <|> folpredicate
       <|> (m_reserved "true" >> return true)
       <|> (m_reserved "false" >> return false)

exprparser :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) =>
              [[Operator s u m formula]] -> ParsecT s u m formula
exprparser exprtable = buildExpressionParser exprtable (parseTerm exprtable) <?> "expression"

folpredicate_infix :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
folpredicate_infix = choice (map (try . app) predicate_infix_symbols)
 where
  app op@"=" = do
   x <- folsubterm
   m_reservedOp op
   y <- folsubterm
   return (x .=. y)
  app op = do
   x <- folsubterm
   m_reservedOp op
   y <- folsubterm
   return (pApp (fromString op :: PredOf (AtomOf formula)) [x,y])

folpredicate :: forall formula s u m. (IsFormula formula, HasApply (AtomOf formula), Stream s m Char) => ParsecT s u m formula
folpredicate = do
   p <- m_identifier <|> m_symbol "|--"
   xs <- option [] (m_parens (sepBy1 folsubterm (m_symbol ",")))
   return (pApp (fromString p :: PredOf (AtomOf formula)) xs)
#endif

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
term :: QuasiQuoter
term = QuasiQuoter
    { quoteExp = \str -> [| parseFOLTerm (dropWhile isSpace str) :: FTerm |]
    , quoteType = error "pfQQ does not implement quoteType"
    , quotePat  = error "pfQQ does not implement quotePat"
    , quoteDec  = error "pfQQ does not implement quoteDec"
    }

parseFOLTerm :: forall term s. (IsTerm term, Stream s Identity Char) => s -> term
parseFOLTerm str = either (error . show) id $ parse folsubterm "" str

def :: forall s u m. Stream s m Char => GenLanguageDef s u m
def = emptyDef{ identStart = letter
              , identLetter = alphaNum <|> char '\'' <|> char '_'
              , opStart = oneOf "~&|=<:*/+->"
              , opLetter = oneOf "~&|=><:-"
              , reservedOpNames = ["~", "¬", "&", "∧", "⋀", "·", "|", "∨", "⋁", "+", "<==>", "⇔", "==>", "⇒", "⟹", ":-", "::", "*", "/", "+", "-", "∃", "∀"] ++ predicate_infix_symbols
              , reservedNames = ["true", "false", "exists", "forall", "for_all"] ++ constants
              }

-- ~(((p v q) ⊃ (r v s)) ⊃ ((p · ~r) ⊃ s))

m_parens :: forall t t1 t2. Stream t t2 Char => forall a. ParsecT t t1 t2 a -> ParsecT t t1 t2 a
m_angles :: forall t t1 t2. Stream t t2 Char => forall a. ParsecT t t1 t2 a -> ParsecT t t1 t2 a
m_symbol :: forall t t1 t2. Stream t t2 Char => String -> ParsecT t t1 t2 String
m_integer :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 Integer
m_identifier :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 String
m_reservedOp :: forall t t1 t2. Stream t t2 Char => String -> ParsecT t t1 t2 ()
m_reserved :: forall t t1 t2. Stream t t2 Char => String -> ParsecT t t1 t2 ()
--m_whiteSpace :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 ()
TokenParser{ parens = m_parens
           , angles = m_angles
--           , brackets = m_brackets
           , symbol = m_symbol
           , integer = m_integer
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
--           , semiSep1 = m_semiSep1
--           , whiteSpace = m_whiteSpace
           } = makeTokenParser def

predicate_infix_symbols :: [[Char]]
predicate_infix_symbols = ["=","<",">","<=",">="]

folfunction :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folfunction = do
   fname <- m_identifier
   xs <- m_parens (sepBy1 folsubterm (m_symbol ","))
   return (fApp (fromString fname :: FunOf term) xs)

folconstant_numeric :: forall term t t1 t2. (IsTerm term, Stream t t2 Char) => ParsecT t t1 t2 term
folconstant_numeric = do
   i <- m_integer
   return (fApp (fromString (show i) :: FunOf term) [])

folconstant_reserved :: forall term t t1 t2. (IsTerm term, Stream t t2 Char) => String -> ParsecT t t1 t2 term
folconstant_reserved str = do
   m_reserved str
   return (fApp (fromString str :: FunOf term) [])

folconstant :: forall term t t1 t2. (IsTerm term, Stream t t2 Char) => ParsecT t t1 t2 term
folconstant = do
   name <- m_angles m_identifier
   return (fApp (fromString name :: FunOf term) [])

folsubterm :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folsubterm = folfunction_infix <|> folsubterm_prefix

constants :: [[Char]]
constants = ["nil"]

folsubterm_prefix :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folsubterm_prefix =
   m_parens folfunction_infix
   <|> try folfunction
   <|> choice (map folconstant_reserved constants)
   <|> folconstant_numeric
   <|> folconstant
   <|> (fmap (vt . fromString) m_identifier)

folfunction_infix :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folfunction_infix = buildExpressionParser table folsubterm_prefix <?> "expression"
 where
  table = [ [Infix (m_reservedOp "::" >> return (\x y -> fApp (fromString "::" :: FunOf term) [x,y])) AssocRight]
          , [Infix (m_reservedOp "*" >> return (\x y -> fApp (fromString "*" :: FunOf term) [x,y])) AssocLeft,
             Infix (m_reservedOp "/" >> return (\x y -> fApp (fromString "/" :: FunOf term) [x,y])) AssocLeft]
          , [Infix (m_reservedOp "+" >> return (\x y -> fApp (fromString "+" :: FunOf term) [x,y])) AssocLeft,
             Infix (m_reservedOp "-" >> return (\x y -> fApp (fromString "-" :: FunOf term) [x,y])) AssocLeft]
          ]
