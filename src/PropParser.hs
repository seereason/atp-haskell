-- | Formula parser.  This should be the inverse of the formula pretty printer.

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module PropParser
    ( pf, parsePF
    , propdef, propOps, propIds
    , propexprtable
    ) where

import Control.Monad.Identity
import Data.Char (isSpace)
import Data.List (nub)
import Equate (EqAtom, HasEquate)
import Formulas (IsFormula(AtomOf))
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import LitParser
import Prop ((.&.), (.|.), (.=>.), (.<=>.), IsPropositional, JustPropositional, PFormula)
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Token

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
pf :: QuasiQuoter
pf = QuasiQuoter
    { quoteExp = \str -> [| (either (error . show) id . parsePF . dropWhile isSpace) str :: PFormula EqAtom |]
    , quoteType = error "pfQQ does not implement quoteType"
    , quotePat  = error "pfQQ does not implement quotePat"
    , quoteDec  = error "pfQQ does not implement quoteDec"
    }

parsePF :: (JustPropositional formula, HasEquate (AtomOf formula), Stream String Identity Char) => String -> Either ParseError formula
parsePF str = parse (exprparser propexprtable >>= \r -> eof >> return r) "" str

andOps, orOps, impOps, iffOps :: [String]
andOps = [".&.", "&", "∧", "⋀", "/\\", "·"]
orOps = ["|", "∨", "⋁", "+", ".|.", "\\/"]
impOps = ["==>", "⇒", "⟹", ".=>.", "→", "⊃"]
iffOps = ["<==>", "⇔", ".<=>.", "↔"]

propOps, propIds :: [String]
propOps = litOps ++ andOps ++ orOps ++ impOps ++ iffOps
propIds = litIds

propexprtable :: (IsPropositional a, Stream s m Char) => [[Operator s u m a]]
propexprtable =
          litexprtable ++
          [ map (\s -> Infix (reservedOp tok s >> return (.&.)) AssocLeft) andOps
          , map (\s -> Infix (reservedOp tok s >> return (.|.)) AssocLeft) orOps
          , map (\s -> Infix (reservedOp tok s >> return (.=>.)) AssocRight) impOps
          , map (\s -> Infix (reservedOp tok s >> return (.<=>.)) AssocLeft) iffOps]

tok :: Stream t t2 Char => GenTokenParser t t1 t2
tok = makeTokenParser propdef

propdef :: forall s u m. Stream s m Char => GenLanguageDef s u m
propdef =
    -- Make the type of litdef match propdef
    let def = litdef :: GenLanguageDef s u m in
    def { reservedOpNames = propOps
        , reservedNames = propIds
        , opStart = oneOf (nub (map head propOps))
        , opLetter = oneOf (nub (concat (map tail propOps)))
        }
