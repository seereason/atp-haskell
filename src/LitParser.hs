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
    , litdef, litOps, litIds
    , exprparser, litexprtable
    ) where

import Apply (pApp, HasApply(PredOf))
import Control.Monad.Identity
import Data.Char (isSpace)
import Data.List (nub)
import Data.String (fromString)
import Equate ((.=.), EqAtom, HasEquate)
import Formulas (IsFormula(AtomOf), true, false)
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Lit ((.~.), IsLiteral, JustLiteral, LFormula)
import TermParser (folsubterm, termdef, termIds, termOps)
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Token

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
lit :: QuasiQuoter
lit = QuasiQuoter
    { quoteExp = \str -> [| (either (error . show) id . parseLit . dropWhile isSpace) str :: LFormula EqAtom |]
    , quoteType = error "pfQQ does not implement quoteType"
    , quotePat  = error "pfQQ does not implement quotePat"
    , quoteDec  = error "pfQQ does not implement quoteDec"
    }

parseLit :: (JustLiteral formula, HasEquate (AtomOf formula), Stream String Identity Char) => String -> Either ParseError formula
parseLit str = parse (exprparser litexprtable >>= \r -> eof >> return r) "" str

notOps :: [String]
notOps = ["¬", "~", ".~."]

trueOps, trueIds, falseOps, falseIds, provesOps, entailsOps, equateOps :: [String]
trueOps = ["⊤"]
trueIds = ["True", "true"]
falseOps = ["⊥"]
falseIds = ["False", "false"]
provesOps = ["⊢", "|--"]
entailsOps = ["⊨", "|=="]
equateOps = [".=.", "="]

predicate_infix_symbols :: [String]
predicate_infix_symbols = equateOps ++ ["<",">","<=",">="]

litexprtable :: (IsLiteral a, Stream s m Char) => [[Operator s u m a]]
litexprtable = [map (\s -> Prefix (reservedOp tok s >> return (.~.))) notOps]

litIds, litOps :: [String]
litIds = termIds ++ trueIds ++ falseIds
litOps = termOps ++ notOps ++ trueOps ++ falseOps ++ provesOps ++ entailsOps ++ equateOps ++ predicate_infix_symbols

parseTerm :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) =>
              [[Operator s u m formula]] -> ParsecT s u m formula
parseTerm exprtable =
    try (parens tok (exprparser exprtable))
       <|> foldr1 (<|>) (map (\s -> reserved tok s >> return true) (trueOps ++ trueIds))
       <|> foldr1 (<|>) (map (\s -> reserved tok s >> return false) (falseOps ++ falseIds))
       <|> try folpredicate_infix
       <|> folpredicate

exprparser :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) =>
              [[Operator s u m formula]] -> ParsecT s u m formula
exprparser exprtable = buildExpressionParser exprtable (parseTerm exprtable) <?> "term"

folpredicate_infix :: forall formula s u m. (IsFormula formula, HasEquate (AtomOf formula), Stream s m Char) => ParsecT s u m formula
folpredicate_infix = choice (map (try . app) (equateOps ++ predicate_infix_symbols))
 where
  app op | elem op equateOps = do
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
   p <- foldr1 (<|>) (identifier tok : map (symbol tok) provesOps)
   xs <- option [] (parens tok (sepBy1 folsubterm (symbol tok ",")))
   return (pApp (fromString p :: PredOf (AtomOf formula)) xs)

tok :: Stream s m Char => GenTokenParser s u m
tok = makeTokenParser termdef

litdef :: forall s u m. Stream s m Char => GenLanguageDef s u m
litdef =
    -- Make the type of termdef match litdef
    let def = termdef :: GenLanguageDef s u m in
    def { reservedOpNames = reservedOpNames def ++ litOps
        , reservedNames = reservedNames def ++ litIds
        , opStart =  oneOf (nub (map head litOps))
        , opLetter = oneOf (nub (concat (map tail litOps)))
        }
