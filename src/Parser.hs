{-# LANGUAGE NoMonomorphismRestriction, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, TypeFamilies #-}
module Parser where

-- Parsing expressions and statements
-- https://wiki.haskell.org/Parsing_expressions_and_statements

import Control.Monad.Identity
import Data.Char (isSpace)
import Data.String (fromString)
import Equate ((.=.))
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Text.Parsec
--import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

import Apply (pApp, Predicate)
import Formulas (true, false)
import Lit ((.~.), LFormula)
import Prop ((.&.), (.|.), (.=>.), (.<=>.), PFormula)
import Quantified (convertQuantified, exists, for_all)
import Skolem (Formula, Function, SkAtom, SkTerm)
import Term (fApp, Term(Var), V(V))

-- | QuasiQuote for a first order formula.  Loading this symbol into the interpreter
-- and setting -XQuasiQuotes lets you type expressions like [fof| ∃ x. p(x) |]
fof :: QuasiQuoter
fof = QuasiQuoter
    { quoteExp = \str -> [| parseFOL (dropWhile isSpace str) |]
    , quoteType = error "fofQQ does not implement quoteType"
    , quotePat  = error "fofQQ does not implement quotePat"
    , quoteDec  = error "fofQQ does not implement quoteDec"
    }

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
pf :: QuasiQuoter
pf = QuasiQuoter
    { quoteExp = \str -> [| convertQuantified id id (parseFOL (dropWhile isSpace str)) :: PFormula SkAtom |]
    , quoteType = error "pfQQ does not implement quoteType"
    , quotePat  = error "pfQQ does not implement quotePat"
    , quoteDec  = error "pfQQ does not implement quoteDec"
    }

-- | QuasiQuote for a propositional formula.  Exactly like fof, but no quantifiers.
lit :: QuasiQuoter
lit = QuasiQuoter
    { quoteExp = \str -> [| convertQuantified id id (parseFOL (dropWhile isSpace str)) :: LFormula SkAtom |]
    , quoteType = error "pfQQ does not implement quoteType"
    , quotePat  = error "pfQQ does not implement quotePat"
    , quoteDec  = error "pfQQ does not implement quoteDec"
    }

-- parseProlog :: forall s lit. Stream s Identity Char => s -> PrologRule lit
-- parseProlog str = either (error . show) id $ parse prologparser "" str
parseFOL :: Stream String Identity Char => String -> Formula
parseFOL str = either (error . show) id $ parse folparser "" str
parseFOLTerm :: forall s. Stream s Identity Char => s -> SkTerm
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

folparser :: forall s u m. Stream s m Char => ParsecT s u m Formula
folparser = folexprparser folterm

folexprparser :: forall s u m. Stream s m Char => ParsecT s u m Formula -> ParsecT s u m Formula
folexprparser term = buildExpressionParser folexprtable term <?> "expression"

folexprtable =
          -- ∀x. ∃y. x=y becomes ∀x. (∃y. (x=y))
          -- ∃x. ∀y. x=y is a parse error
          propexprtable ++
          [ [Prefix existentialPrefix]
          , [Prefix forallPrefix] ]

propexprtable =
           [ [Prefix (m_reservedOp ".~." >> return (.~.)),
             Prefix (m_reservedOp "~" >> return (.~.)),
             Prefix (m_reservedOp "¬" >> return (.~.))]

          , [Infix (m_reservedOp ".&." >> return (.&.)) AssocRight,
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

folterm :: forall s u m. Stream s m Char => ParsecT s u m Formula
folterm = try (m_parens folparser)
       <|> try folpredicate_infix
       <|> folpredicate
       <|> (m_reserved "true" >> return true)
       <|> (m_reserved "false" >> return false)

existentialPrefix :: forall s u m. Stream s m Char => ParsecT s u m (Formula -> Formula)
existentialPrefix = quantifierPrefix "∃" exists <|> quantifierPrefix "exists" exists
forallPrefix :: forall s u m. Stream s m Char => ParsecT s u m (Formula -> Formula)
forallPrefix = quantifierPrefix "∀" for_all <|> quantifierPrefix "for_all" for_all <|> quantifierPrefix "forall" for_all

quantifierPrefix :: forall s u m. Stream s m Char => [Char] -> (V -> Formula -> Formula) -> ParsecT s u m (Formula -> Formula)
quantifierPrefix name op = do
   m_reservedOp name
   is <- map V <$> many1 m_identifier
   _ <- m_symbol "."
   return (\fm -> foldr op fm is)

predicate_infix_symbols :: [[Char]]
predicate_infix_symbols = ["=","<",">","<=",">="]

folpredicate_infix :: forall s u m. Stream s m Char => ParsecT s u m Formula
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

folpredicate :: forall s u m. Stream s m Char => ParsecT s u m Formula
folpredicate = do
   p <- m_identifier <|> m_symbol "|--"
   xs <- option [] (m_parens (sepBy1 folsubterm (m_symbol ",")))
   return (pApp (fromString p :: Predicate) xs)

folfunction :: forall s u m. Stream s m Char => ParsecT s u m SkTerm
folfunction = do
   fname <- m_identifier
   xs <- m_parens (sepBy1 folsubterm (m_symbol ","))
   return (fApp (fromString fname :: Function) xs)

folconstant_numeric :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 SkTerm
folconstant_numeric = do
   i <- m_integer
   return (fApp (fromString (show i) :: Function) [])

folconstant_reserved :: forall t t1 t2. Stream t t2 Char => String -> ParsecT t t1 t2 SkTerm
folconstant_reserved str = do
   m_reserved str
   return (fApp (fromString str :: Function) [])

folconstant :: forall t t1 t2. Stream t t2 Char => ParsecT t t1 t2 SkTerm
folconstant = do
   name <- m_angles m_identifier
   return (fApp (fromString name :: Function) [])

folsubterm :: forall s u m. Stream s m Char => ParsecT s u m SkTerm
folsubterm = folfunction_infix <|> folsubterm_prefix

constants :: [[Char]]
constants = ["nil"]

folsubterm_prefix :: forall s u m. Stream s m Char => ParsecT s u m SkTerm
folsubterm_prefix =
   m_parens folfunction_infix
   <|> try folfunction
   <|> choice (map folconstant_reserved constants)
   <|> folconstant_numeric
   <|> folconstant
   <|> (fmap (Var . V) m_identifier)

folfunction_infix :: forall s u m. Stream s m Char => ParsecT s u m SkTerm
folfunction_infix = buildExpressionParser table folsubterm_prefix <?> "expression"
 where
  table = [ [Infix (m_reservedOp "::" >> return (\x y -> fApp (fromString "::" :: Function) [x,y])) AssocRight]
          , [Infix (m_reservedOp "*" >> return (\x y -> fApp (fromString "*" :: Function) [x,y])) AssocLeft,
             Infix (m_reservedOp "/" >> return (\x y -> fApp (fromString "/" :: Function) [x,y])) AssocLeft]
          , [Infix (m_reservedOp "+" >> return (\x y -> fApp (fromString "+" :: Function) [x,y])) AssocLeft,
             Infix (m_reservedOp "-" >> return (\x y -> fApp (fromString "-" :: Function) [x,y])) AssocLeft]
          ]
