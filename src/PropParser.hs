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
    , propexprtable
    ) where

import Control.Monad.Identity
import Data.Char (isSpace)
import Equate (EqAtom, HasEquate)
import Formulas (IsFormula(AtomOf))
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import LitParser
import Prop ((.&.), (.|.), (.=>.), (.<=>.), IsPropositional, JustPropositional, PFormula)
import TermParser
import Text.Parsec
import Text.Parsec.Expr

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
