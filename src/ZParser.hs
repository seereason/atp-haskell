{-# OPTIONS_GHC -fwarn-unused-binds #-}
{-# LANGUAGE RankNTypes, KindSignatures #-}
{-# LANGUAGE NoMonomorphismRestriction, FlexibleContexts, FlexibleInstances #-}
module ZParser (parseFOL) where

-- Parsing expressions and statements
-- https://wiki.haskell.org/Parsing_expressions_and_statements

import Data.Functor.Identity (Identity)
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

import ZTypes hiding (try)
import ZInstances ()

instance Read PrologRule where
   readsPrec n str = [(parseProlog str,"")]

instance Read (Formula FOL) where
   readsPrec n str = [(parseFOL str,"")]

instance Read (Formula Prop) where
   readsPrec n str = [(parsePL str,"")]

parseProlog :: forall s.
                     Stream s Identity Char =>
                     s -> PrologRule
parseProlog str = either (error . show) id $ parse prologparser "" str
parseFOL :: forall s.
                  Stream s Identity Char =>
                  s -> Formula FOL
parseFOL str = either (error . show) id $ parse folparser "" str
parsePL str = either (error . show) id $ parse propparser "" str
-- parseFOLTerm str = either (error . show) id $ parse folsubterm "" str

def = emptyDef{ identStart = letter
              , identLetter = alphaNum
              , opStart = oneOf "~&|=<:*/+->"
              , opLetter = oneOf "~&|=><:-"
              , reservedOpNames = ["~", "&", "|", "<==>", "==>", ":-", "::", "*", "/", "+", "-"] ++ predicate_infix_symbols
              , reservedNames = ["true", "false", "exists", "forall"] ++ constants
              }

TokenParser{ parens = m_parens
           , angles = m_angles
--           , brackets = m_brackets
           , symbol = m_symbol
           , integer = m_integer
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
--           , semiSep1 = m_semiSep1
           , whiteSpace = _m_whiteSpace } = makeTokenParser def

prologparser :: forall s u (m :: * -> *).
                      Stream s m Char =>
                      ParsecT s u m PrologRule
prologparser = try (do
   left <- folparser
   m_symbol ":-"
   right <- sepBy folparser (m_symbol ",")
   return (Prolog right left))
   <|> (do
   left <- folparser
   return (Prolog [] left))
   <?> "prolog expression"

propparser :: forall s u (m :: * -> *).
                    Stream s m Char =>
                    ParsecT s u m (Formula Prop)
propparser = exprparser propterm
folparser :: forall s u (m :: * -> *).
                   Stream s m Char =>
                   ParsecT s u m (Formula FOL)
folparser = exprparser folterm

exprparser :: forall s u (m :: * -> *) a.
                    Stream s m Char =>
                    ParsecT s u m (Formula a) -> ParsecT s u m (Formula a)
exprparser term = buildExpressionParser table term <?> "expression"
 where
  table = [ [Prefix (m_reservedOp "~" >> return Not)]
          , [Infix (m_reservedOp "&" >> return And) AssocRight]
          , [Infix (m_reservedOp "|" >> return Or) AssocRight]
          , [Infix (m_reservedOp "<==>" >> return Iff) AssocRight]
          , [Infix (m_reservedOp "==>" >> return Imp) AssocRight]
          ]

propterm :: forall s u (m :: * -> *).
                  Stream s m Char =>
                  ParsecT s u m (Formula Prop)
propterm = m_parens propparser
       <|> fmap (Atom . P) m_identifier
       <|> (m_reserved "true" >> return TT)
       <|> (m_reserved "false" >> return FF)

folterm :: forall s u (m :: * -> *).
                 Stream s m Char =>
                 ParsecT s u m (Formula FOL)
folterm = try (m_parens folparser)
       <|> try folpredicate_infix
       <|> folpredicate
       <|> existentialQuantifier
       <|> forallQuantifier
       <|> (m_reserved "true" >> return TT)
       <|> (m_reserved "false" >> return FF)

existentialQuantifier :: forall s u (m :: * -> *).
                               Stream s m Char =>
                               ParsecT s u m (Formula FOL)
existentialQuantifier = quantifier "exists" Exists
forallQuantifier :: forall s u (m :: * -> *).
                          Stream s m Char =>
                          ParsecT s u m (Formula FOL)
forallQuantifier = quantifier "forall" Forall

quantifier :: forall s u (m :: * -> *).
                    Stream s m Char =>
                    [Char]
                    -> (String -> Formula FOL -> Formula FOL)
                    -> ParsecT s u m (Formula FOL)
quantifier name op = do
   m_reserved name
   is <- many1 m_identifier
   m_symbol "."
   fm <- folparser
   return (foldr op fm is)

predicate_infix_symbols :: [[Char]]
predicate_infix_symbols = ["=","<",">","<=",">="]

folpredicate_infix :: forall s u (m :: * -> *).
                            Stream s m Char =>
                            ParsecT s u m (Formula FOL)
folpredicate_infix = choice (map (try.app) predicate_infix_symbols)
 where
  app op = do
   x <- folsubterm
   m_reservedOp op
   y <- folsubterm
   return (Atom (R op [x,y]))

folpredicate :: forall s u (m :: * -> *).
                      Stream s m Char =>
                      ParsecT s u m (Formula FOL)
folpredicate = do
   p <- m_identifier <|> m_symbol "|--"
   xs <- option [] (m_parens (sepBy1 folsubterm (m_symbol ",")))
   return (Atom (R p xs))

folfunction :: forall s u (m :: * -> *).
                     Stream s m Char =>
                     ParsecT s u m Term
folfunction = do
   fname <- m_identifier
   xs <- m_parens (sepBy1 folsubterm (m_symbol ","))
   return (Fn fname xs)

folconstant_numeric :: forall t t1 (t2 :: * -> *).
                             Stream t t2 Char =>
                             ParsecT t t1 t2 Term
folconstant_numeric = do
   i <- m_integer
   return (Fn (show i) [])

folconstant_reserved :: forall t t1 (t2 :: * -> *).
                              Stream t t2 Char =>
                              String -> ParsecT t t1 t2 Term
folconstant_reserved str = do
   m_reserved str
   return (Fn str [])

folconstant :: forall t t1 (t2 :: * -> *).
                     Stream t t2 Char =>
                     ParsecT t t1 t2 Term
folconstant = do
   name <- m_angles m_identifier
   return (Fn name [])

folsubterm :: forall s u (m :: * -> *).
                    Stream s m Char =>
                    ParsecT s u m Term
folsubterm = folfunction_infix <|> folsubterm_prefix

constants :: [String]
constants = ["nil"]

folsubterm_prefix :: forall s u (m :: * -> *).
                           Stream s m Char =>
                           ParsecT s u m Term
folsubterm_prefix =
   m_parens folfunction_infix
   <|> try folfunction
   <|> choice (map folconstant_reserved constants)
   <|> folconstant_numeric
   <|> folconstant
   <|> (fmap Var m_identifier)

folfunction_infix :: forall s u (m :: * -> *).
                           Stream s m Char =>
                           ParsecT s u m Term
folfunction_infix = buildExpressionParser table folsubterm_prefix <?> "expression"
 where
  table = [ [Infix (m_reservedOp "::" >> return (\x y -> Fn "::" [x,y])) AssocRight]
            , [Infix (m_reservedOp "*" >> return (\x y -> Fn "*" [x,y])) AssocLeft, Infix (m_reservedOp "/" >> return (\x y -> Fn "/" [x,y])) AssocLeft]
            , [Infix (m_reservedOp "+" >> return (\x y -> Fn "+" [x,y])) AssocLeft, Infix (m_reservedOp "-" >> return (\x y -> Fn "-" [x,y])) AssocLeft]
          ]
