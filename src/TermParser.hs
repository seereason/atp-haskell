-- | Formula parser.  This should be the inverse of the formula pretty printer.

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module TermParser
    ( term, parseFOLTerm
    , predicate_infix_symbols, folsubterm
    , m_parens, m_angles, m_symbol, m_integer
    , m_identifier, m_reservedOp, m_reserved
    ) where

-- Parsing expressions and statements
-- https://wiki.haskell.org/Parsing_expressions_and_statements

import Control.Monad.Identity
import Data.Char (isSpace)
import Data.String (fromString)
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Term (fApp, FTerm, IsTerm(FunOf, vt))
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

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
