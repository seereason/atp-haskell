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
import TermParser
import Text.Parsec
import Text.Parsec.Expr

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
