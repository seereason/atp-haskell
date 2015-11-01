{-# LANGUAGE CPP, NoMonomorphismRestriction, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, TypeFamilies #-}
module Parser where

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

import FOL
import Formulas
--import Lit
--import Prop
--import Prolog (PrologRule(Prolog))
import Skolem

-- | QuasiQuote for a first order formula.  Loading this symbol into the interpreter
-- and setting -XQuasiQuotes lets you type expressions like [fof| ∃ x. p(x) |]
fof :: QuasiQuoter
fof = QuasiQuoter
    { quoteExp = \str -> [| parseFOL (dropWhile isSpace str) |]
    , quoteType = error "abtQQ does not implement quoteType"
    , quotePat  = error "abtQQ does not implement quotePat"
    , quoteDec  = error "abtQQ does not implement quoteDec"
    }

-- parseProlog :: forall s lit. Stream s Identity Char => s -> PrologRule lit
-- parseProlog str = either (error . show) id $ parse prologparser "" str
parseFOL :: Stream String Identity Char => String -> MyFormula
parseFOL str = either (error . show) id $ parse folparser "" str
-- parsePL :: forall s. Stream s Identity Char => s -> PFormula Prop
-- parsePL str = either (error . show) id $ parse propparser "" str
parseFOLTerm :: forall s. Stream s Identity Char => s -> MyTerm
parseFOLTerm str = either (error . show) id $ parse folsubterm "" str

def :: forall s u m. Stream s m Char => GenLanguageDef s u m
def = emptyDef{ identStart = letter
              , identLetter = alphaNum <|> char '\'' <|> char '_'
              , opStart = oneOf "~&|=<:*/+->"
              , opLetter = oneOf "~&|=><:-"
              , reservedOpNames = ["~", "¬", "&", "∧", "|", "∨", "<==>", "⇔", "==>", "⇒", ":-", "::", "*", "/", "+", "-", "∃", "∀"] ++ predicate_infix_symbols
              , reservedNames = ["true", "false", "exists", "forall", "for_all"] ++ constants
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

-- propparser :: forall s u m. Stream s m Char => ParsecT s u m (PFormula Prop)
-- propparser = exprparser propterm
folparser :: forall s u m. Stream s m Char => ParsecT s u m MyFormula
folparser = exprparser folterm

exprparser :: forall s u m. Stream s m Char => ParsecT s u m MyFormula -> ParsecT s u m MyFormula
exprparser term = buildExpressionParser table term <?> "expression"
 where
  table = [ [Prefix (m_reservedOp "~" >> return (.~.)), Prefix (m_reservedOp "¬" >> return (.~.))]
          , [Infix (m_reservedOp "&" >> return (.&.)) AssocRight, Infix (m_reservedOp "∧" >> return (.&.)) AssocRight]
          , [Infix (m_reservedOp "|" >> return (.|.)) AssocRight, Infix (m_reservedOp "∨" >> return (.|.)) AssocRight]
          , [Infix (m_reservedOp "<==>" >> return (.<=>.)) AssocRight, Infix (m_reservedOp "⇔" >> return (.<=>.)) AssocRight]
          , [Infix (m_reservedOp "==>" >> return (.=>.)) AssocRight, Infix (m_reservedOp "⇒" >> return (.=>.)) AssocRight]
          ]

-- propterm :: forall s u m. Stream s m Char => ParsecT s u m (PFormula Prop)
-- propterm = m_parens propparser
--        <|> fmap pApp m_identifier
--        <|> (m_reserved "true" >> return true)
--        <|> (m_reserved "false" >> return false)

folterm :: forall s u m. Stream s m Char => ParsecT s u m MyFormula
folterm = try (m_parens folparser)
       <|> try folpredicate_infix
       <|> folpredicate
       <|> existentialQuantifier
       <|> forallQuantifier
       <|> (m_reserved "true" >> return true)
       <|> (m_reserved "false" >> return false)

existentialQuantifier :: forall s u m. Stream s m Char => ParsecT s u m MyFormula
existentialQuantifier = quantifier "∃" Exists <|> quantifier "exists" Exists
forallQuantifier :: forall s u m. Stream s m Char => ParsecT s u m MyFormula
forallQuantifier = quantifier "∀" Forall <|> quantifier "for_all" Forall

quantifier :: forall s u m. Stream s m Char => [Char] -> (V -> MyFormula -> MyFormula) -> ParsecT s u m MyFormula
quantifier name op = do
   m_reservedOp name
   is <- map V <$> many1 m_identifier
   _ <- m_symbol "."
   fm <- folparser
   return (foldr op fm is)

predicate_infix_symbols :: [[Char]]
predicate_infix_symbols = ["=","<",">","<=",">="]

folpredicate_infix :: forall s u m. Stream s m Char => ParsecT s u m MyFormula
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
   return (pApp (fromString op :: Predicate) [x,y])

folpredicate :: forall s u m. Stream s m Char => ParsecT s u m MyFormula
folpredicate = do
   p <- m_identifier <|> m_symbol "|--"
   xs <- option [] (m_parens (sepBy1 folsubterm (m_symbol ",")))
   return (pApp (fromString p :: Predicate) xs)

folfunction :: forall s u m. Stream s m Char => ParsecT s u m MyTerm
folfunction = do
   fname <- m_identifier
   xs <- m_parens (sepBy1 folsubterm (m_symbol ","))
   return (fApp (fromString fname :: Function) xs)

folconstant_numeric :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 MyTerm
folconstant_numeric = do
   i <- m_integer
   return (fApp (fromString (show i) :: Function) [])

folconstant_reserved :: forall t t1 t2. Stream t t2 Char => String -> ParsecT t t1 t2 MyTerm
folconstant_reserved str = do
   m_reserved str
   return (fApp (fromString str :: Function) [])

folconstant :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 MyTerm
folconstant = do
   name <- m_angles m_identifier
   return (fApp (fromString name :: Function) [])

folsubterm :: forall s u m. Stream s m Char => ParsecT s u m MyTerm
folsubterm = folfunction_infix <|> folsubterm_prefix

constants :: [[Char]]
constants = ["nil"]

folsubterm_prefix :: forall s u m. Stream s m Char => ParsecT s u m MyTerm
folsubterm_prefix =
   m_parens folfunction_infix
   <|> try folfunction
   <|> choice (map folconstant_reserved constants)
   <|> folconstant_numeric
   <|> folconstant
   <|> (fmap (Var . V) m_identifier)

folfunction_infix :: forall s u m. Stream s m Char => ParsecT s u m MyTerm
folfunction_infix = buildExpressionParser table folsubterm_prefix <?> "expression"
 where
  table = [ [Infix (m_reservedOp "::" >> return (\x y -> fApp (fromString "::" :: Function) [x,y])) AssocRight]
          , [Infix (m_reservedOp "*" >> return (\x y -> fApp (fromString "*" :: Function) [x,y])) AssocLeft,
             Infix (m_reservedOp "/" >> return (\x y -> fApp (fromString "/" :: Function) [x,y])) AssocLeft]
          , [Infix (m_reservedOp "+" >> return (\x y -> fApp (fromString "+" :: Function) [x,y])) AssocLeft,
             Infix (m_reservedOp "-" >> return (\x y -> fApp (fromString "-" :: Function) [x,y])) AssocLeft]
          ]
