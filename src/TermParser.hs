-- | Formula parser.  This should be the inverse of the formula pretty printer.

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module TermParser
    ( term, parseFOLTerm, termdef
    , folsubterm
    -- , m_parens, m_angles, m_symbol, m_integer
    -- , m_identifier, m_reservedOp, m_reserved
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
    { quoteExp = \str -> [| (either (error . show) id . parseFOLTerm . dropWhile isSpace) str :: FTerm |]
    , quoteType = error "pfQQ does not implement quoteType"
    , quotePat  = error "pfQQ does not implement quotePat"
    , quoteDec  = error "pfQQ does not implement quoteDec"
    }

parseFOLTerm :: forall term s. (IsTerm term, Stream s Identity Char) => s -> Either ParseError term
parseFOLTerm str = parse (folsubterm >>= \r ->  eof >> return r) "" str

folfunction :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folfunction = do
   fname <- identifier tok
   xs <- parens tok (sepBy1 folsubterm (symbol tok ","))
   return (fApp (fromString fname :: FunOf term) xs)

folconstant_numeric :: forall term t t1 t2. (IsTerm term, Stream t t2 Char) => ParsecT t t1 t2 term
folconstant_numeric = do
   i <- integer tok
   return (fApp (fromString (show i) :: FunOf term) [])

folconstant_reserved :: forall term t t1 t2. (IsTerm term, Stream t t2 Char) => String -> ParsecT t t1 t2 term
folconstant_reserved str = do
   reserved tok str
   return (fApp (fromString str :: FunOf term) [])

folconstant :: forall term t t1 t2. (IsTerm term, Stream t t2 Char) => ParsecT t t1 t2 term
folconstant = do
   name <- (angles tok (identifier tok))
   return (fApp (fromString name :: FunOf term) [])

folsubterm :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folsubterm = folfunction_infix <|> folsubterm_prefix

folsubterm_prefix :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folsubterm_prefix =
   parens tok folfunction_infix
   <|> try folfunction
   <|> choice (map folconstant_reserved constants)
   <|> folconstant_numeric
   <|> folconstant
   <|> (fmap (vt . fromString) (identifier tok))

folfunction_infix :: forall term s u m. (IsTerm term, Stream s m Char) => ParsecT s u m term
folfunction_infix = buildExpressionParser table folsubterm_prefix <?> "expression"
 where
  table = [ [Infix (reservedOp tok "::" >> return (\x y -> fApp (fromString "::" :: FunOf term) [x,y])) AssocRight]
          , [Infix (reservedOp tok "*" >> return (\x y -> fApp (fromString "*" :: FunOf term) [x,y])) AssocLeft,
             Infix (reservedOp tok "/" >> return (\x y -> fApp (fromString "/" :: FunOf term) [x,y])) AssocLeft]
          , [Infix (reservedOp tok "+" >> return (\x y -> fApp (fromString "+" :: FunOf term) [x,y])) AssocLeft,
             Infix (reservedOp tok "-" >> return (\x y -> fApp (fromString "-" :: FunOf term) [x,y])) AssocLeft]
          ]

tok :: Stream s m Char => GenTokenParser s u m
tok = makeTokenParser termdef

termdef :: forall s u m. Stream s m Char => GenLanguageDef s u m
termdef = emptyDef
              { identStart = letter
              , identLetter = alphaNum <|> char '\'' <|> char '_'
              , opStart =  oneOf "~&|=<:->*/+"
              , opLetter = oneOf "~&|=<:->"
              , reservedOpNames = function_infix_symbols
              , reservedNames = constants
              }

function_infix_symbols :: [String]
function_infix_symbols =  ["*", "/", "+", "-"]

constants :: [String]
constants = ["nil"]
