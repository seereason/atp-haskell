-- | Formula parser.  This should be the inverse of the formula pretty printer.

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module QuantifiedParser
    ( fof, parseFOL
    ) where

import Control.Monad.Identity
import Data.Char (isSpace)
import Data.List (nub)
import Data.String (fromString)
import Equate (HasEquate)
import Formulas (IsFormula(AtomOf))
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import LitParser (exprparser)
import PropParser (propexprtable, propdef, propIds, propOps)
import Quantified (exists, for_all, IsQuantified)
import Skolem (Formula)
import Term (IsVariable)
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Token

-- | QuasiQuote for a first order formula.  Loading this symbol into the interpreter
-- and setting -XQuasiQuotes lets you type expressions like [fof| ∃ x. p(x) |]
fof :: QuasiQuoter
fof = QuasiQuoter
    { quoteExp = \str -> [| (either (error . show) id . parseFOL . dropWhile isSpace) str :: Formula |]
    , quoteType = error "fofQQ does not implement quoteType"
    , quotePat  = error "fofQQ does not implement quotePat"
    , quoteDec  = error "fofQQ does not implement quoteDec"
    }

-- parseProlog :: forall s lit. Stream s Identity Char => s -> PrologRule lit
-- parseProlog str = either (error . show) id $ parse prologparser "" str
parseFOL :: (IsQuantified formula, HasEquate (AtomOf formula), Stream String Identity Char) => String -> Either ParseError formula
parseFOL str = parse (exprparser folexprtable >>= \r -> eof >> return r) "" str

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

forallIds, forallOps, existsIds, existsOps :: [String]
forallIds = ["forall", "for_all"]
forallOps= ["∀"]
existsIds = ["exists"]
existsOps = ["∃"]

quantOps , quantIds :: [String]
quantOps = propOps ++ forallOps ++ existsOps
quantIds = propIds ++ forallIds ++ existsIds

folexprtable :: (IsQuantified formula, Stream s m Char) => [[Operator s u m formula]]
folexprtable =
    -- ∀x. ∃y. x=y becomes ∀x. (∃y. (x=y))
    -- ∃x. ∀y. x=y is a parse error
    propexprtable ++
    [ [Prefix existentialPrefix]
    , [Prefix forallPrefix] ]
    where
      existentialPrefix :: forall formula s u m. (IsQuantified formula, Stream s m Char) => ParsecT s u m (formula -> formula)
      existentialPrefix = foldr1 (<|>) (map (\s -> quantifierPrefix s exists) (existsIds ++ existsOps))
      forallPrefix :: forall formula s u m. (IsQuantified formula, Stream s m Char) => ParsecT s u m (formula -> formula)
      forallPrefix = foldr1 (<|>) (map (\s -> quantifierPrefix s for_all) (forallIds ++ forallOps))

      quantifierPrefix :: forall formula v s u m. (IsVariable v, Stream s m Char) =>
                          String -> (v -> formula -> formula) -> ParsecT s u m (formula -> formula)
      quantifierPrefix name op = do
        reservedOp tok name
        is <- map fromString <$> many1 (identifier tok)
        _ <- symbol tok "."
        return (\fm -> foldr op fm is)

tok :: Stream t t2 Char => GenTokenParser t t1 t2
tok = makeTokenParser foldef

foldef :: forall s u m. Stream s m Char => GenLanguageDef s u m
foldef =
    -- Make the type of propdef match foldef
    let def = propdef :: GenLanguageDef s u m in
    def { reservedOpNames = quantOps
        , reservedNames = quantIds
        , opStart = oneOf (nub (map head quantOps))
        , opLetter = oneOf (nub (concat (map tail quantOps)))
        }
