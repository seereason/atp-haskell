-- | Formula parser.  This should be the inverse of the formula pretty printer.

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LitParser
    ( lit, parseLit
    , litdef
    , exprparser, litexprtable
    ) where

import Apply (pApp, HasApply(PredOf))
import Control.Monad.Identity
import Data.Char (isSpace)
import Data.String (fromString)
import Equate ((.=.), EqAtom, HasEquate)
import Formulas (IsFormula(AtomOf), true, false)
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Lit ((.~.), IsLiteral, JustLiteral, LFormula)
import TermParser (folsubterm, termdef)
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Token

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
lit :: QuasiQuoter
lit = QuasiQuoter
    { quoteExp = \str -> [| parseLit (dropWhile isSpace str) :: LFormula EqAtom |]
    , quoteType = error "pfQQ does not implement quoteType"
    , quotePat  = error "pfQQ does not implement quotePat"
    , quoteDec  = error "pfQQ does not implement quoteDec"
    }

parseLit :: (JustLiteral formula, HasEquate (AtomOf formula), Stream String Identity Char) => String -> formula
parseLit str = either (error . show) id $ parse (exprparser litexprtable >>= \r -> eof >> return r) "" str

nots :: [String]
nots = ["¬", "~", ".~."]

trues, trueIds, falses, falseIds :: [String]
trues = ["⊤"]
trueIds = ["True", "true"]
falses = ["⊥"]
falseIds = ["False", "false"]

litexprtable :: (IsLiteral a, Stream s m Char) => [[Operator s u m a]]
litexprtable = [map (\s -> Prefix (reservedOp tok s >> return (.~.))) nots]

parseTerm :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) =>
              [[Operator s u m formula]] -> ParsecT s u m formula
parseTerm exprtable =
    try (parens tok (exprparser exprtable))
       <|> foldr1 (<|>) (map (\s -> reserved tok s >> return true) (trues ++ trueIds))
       <|> foldr1 (<|>) (map (\s -> reserved tok s >> return false) (falses ++ falseIds))
       <|> try folpredicate_infix
       <|> folpredicate

exprparser :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) =>
              [[Operator s u m formula]] -> ParsecT s u m formula
exprparser exprtable = buildExpressionParser exprtable (parseTerm exprtable) <?> "expression"

folpredicate_infix :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
folpredicate_infix = choice (map (try . app) predicate_infix_symbols)
 where
  app op@"=" = do
   x <- folsubterm
   reservedOp tok op
   y <- folsubterm
   return (x .=. y)
  app op = do
   x <- folsubterm
   reservedOp tok op
   y <- folsubterm
   return (pApp (fromString op :: PredOf (AtomOf formula)) [x,y])

folpredicate :: forall formula s u m. (IsFormula formula, HasApply (AtomOf formula), Stream s m Char) => ParsecT s u m formula
folpredicate = do
   p <- identifier tok <|> symbol tok "|--"
   xs <- option [] (parens tok (sepBy1 folsubterm (symbol tok ",")))
   return (pApp (fromString p :: PredOf (AtomOf formula)) xs)

tok :: Stream s m Char => GenTokenParser s u m
tok = makeTokenParser termdef

litdef :: forall s u m. Stream s m Char => GenLanguageDef s u m
litdef =
    -- Make the type of termdef match litdef
    let def = termdef :: GenLanguageDef s u m in
    def { reservedOpNames = reservedOpNames def ++ nots ++ trues ++ falses ++ predicate_infix_symbols
        , reservedNames = reservedNames def ++ trueIds ++ falseIds
        }

predicate_infix_symbols :: [[Char]]
predicate_infix_symbols = ["=","<",">","<=",">="]
