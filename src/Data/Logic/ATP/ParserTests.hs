{-# LANGUAGE OverloadedStrings, QuasiQuotes, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}
module Data.Logic.ATP.ParserTests where

import Data.Logic.ATP.Equate ((.=.))
import Data.Logic.ATP.Pretty (assertEqual', Pretty(..), prettyShow, testEquals)
import Data.Logic.ATP.Prop ((.&.), (.=>.))
import Data.Logic.ATP.Parser (fof, parseFOL)
import Data.Logic.ATP.Skolem (Formula)
import Test.HUnit

t :: (Eq a, Pretty a) => String -> a -> a -> Test
t label expected actual = TestLabel label (TestCase (assertEqual' label expected actual))

parseFOL' :: String -> Either String Formula
parseFOL' = either (Left . show) Right . parseFOL

testParser :: Test
testParser =
    -- I would like these Lefts to work
    TestLabel "ParserTests"
      (TestList [ $(testEquals "precedence 1a") (Right [fof| (∃x. ⊤∧(∃y. ⊤)) |])
                       (parseFOL' " ∃x. (true & (∃y. true)) ")
                , $(testEquals "precedence 1b") (Right [fof| ∃x. (true & (∃y. true)) |])
                       (parseFOL " ∃x. (true & (∃y. true)) ")
                , $(testEquals "precedence 1c") (Right [fof|(∃x. ⊤∧(∃y. ⊤))|])
                       (parseFOL' " ∃x. true & ∃y. true ")
                , $(testEquals "precedence 2") [fof| (true & false) | true |]
                       [fof| true & false | true |]
                , $(testEquals "precedence 3") [fof| (true | false) <==> true |]
                       [fof| true | false <==> true |]
                , $(testEquals "precedence 4") [fof| true <==> (false ==> true) |]
                       [fof| true <==> false ==> true |]
                , $(testEquals "precedence 5") [fof| (~ true) & false |]
                       [fof| ~ true & false |]
                -- repeated prefix operator with same precedences fails:
                , $(testEquals "precedence 6") (Right [fof|(∃x y. (x=y))|])
                       (parseFOL' " ∃x. ∃y. x=y ")
                , $(testEquals "precedence 6b") [fof|(∃x. (∃y. (x=y)))|]
                       [fof| ∃x. (∃y. x=y) |]
                , $(testEquals "precedence 7") [fof| ∃x. (∃y. (x=y)) |]
                       [fof| ∃x y. x=y |]
                , $(testEquals "precedence 8") [fof| ∀x. (∃y. (x=y)) |]
                       [fof| ∀x. ∃y. x=y |]
                , $(testEquals "precedence 9") [fof| ∃y. (∀x. (x=y)) |]
                       [fof| ∃y. (∀x. x=y) |]
                , $(testEquals "precedence 10") [fof| (~P) & Q |]
                       [fof| ~P & Q |] -- ~ vs &
                -- repeated prefix operator with same precedences fails:
                , $(testEquals "precedence 10a") (Left "(line 1, column 3):\nunexpected '~'\nexpecting prop")
                       (parseFOL' " ~~P ")
                , $(testEquals "precedence 11") [fof| (P & Q) | R |]
                       [fof| P & Q | R |] -- & vs |
                , $(testEquals "precedence 12") [fof| (P | Q) ==> R |]
                       [fof| P | Q ==> R |] -- or vs imp
                , $(testEquals "precedence 13")  [fof| (P ==> Q) <==> R |]
                       [fof| P ==> Q <==> R |] -- imp vs iff
             -- , TestCase "precedence 14" [fof| ∃x. (∀y. x=y) |] [fof| ∃x.  ∀y. x=y |]
                , $(testEquals "precedence 14a") [fof| ((x = y) ∧ (x = z)) ⇒ (y = z) |]
                       ("x" .=. "y" .&. "x" .=. "z" .=>. "y" .=. "z")
                , $(testEquals "pretty 1") "∃x y. (∀z. (F(x,y)⇒F(y,z)∧F(z,z))∧(F(x,y)∧G(x,y)⇒G(x,z)∧G(z,z)))"
                       (prettyShow [fof| ∃ x y. (∀ z. ((F(x,y)⇒F(y,z)∧F(z,z))∧(F(x,y)∧G(x,y)⇒G(x,z)∧G(z,z)))) |])
                , $(testEquals "pretty 2") [fof| (∃x. (x=(f((g(x)))))∧(∀x'. x'=(f((g(x'))))⇒x=x'))⇔(∃y. y=(g((f(y))))∧(∀y'. y'=(g(f(y')))⇒y=y')) |]
                       [fof| (exists x. x = f(g(x)) /\ (forall x'. (x' = f(g(x'))) ==> (x = x'))) .<=>. (exists y. y = g(f(y)) /\ (forall y'. (y' = g(f(y'))) ==> (y = y'))) |]
                -- We could use haskell-src-meta to perform the third
                -- step of the round trip, roughly
                --
                --   1. formula string to parsed formula expression (Parser.parseExp)
                --   2. formula expression to parsed haskell-src-exts expression (show and th-lift?)
                --   3. haskell-src-exts to template-haskell expression (the toExp method of haskell-src-meta)
                --   4. template haskell back to haskell expression (template-haskell unquote)
{-
                , $(testEquals "read 1") (show (ParseOk (InfixApp (App
                                                                                                  (App (Var (UnQual (Ident "for_all"))) (Lit (String "x")))
                                                                                                  (Paren (Lit (String "x")))) (QVarOp (UnQual (Symbol ".=."))) (Paren (Lit (String "x"))))))
                       (show (parseExp (show [fof| ∀x. (x=x) |])))
                , $(testEquals "read 2") (show (ParseOk (InfixApp (App (App (App (App (Var (UnQual (Ident "for_all"))) (Lit (String "x")))
                                                                                                            (Var (UnQual (Ident "pApp"))))
                                                                                                       (Paren (App (Var (UnQual (Ident "fromString"))) (Lit (String "P")))))
                                                                                                  (List [Lit (String "x")]))
                                                                                        (QVarOp (UnQual (Symbol ".&.")))
                                                                                        (App (App (Var (UnQual (Ident "pApp")))
                                                                                              (Paren (App (Var (UnQual (Ident "fromString")))
                                                                                                      (Lit (String "Q")))))
                                                                                         (List [Lit (String "x")])))))
                       (show (parseExp (show [fof| ∀x. P(x) ∧ Q(x) |])))
-}
                , $(testEquals "parse 1") [fof| (forall x. i(x) * x = 1) ==> (forall x. i(x) * x = 1) |]
                       [fof| (forall x. i(x) * x = 1) ==> forall x. i(x) * x = 1 |]
                , $(testEquals "parse 2") "(*(i(x), x))=(1)" -- "i(x) * x = 1"
                       (prettyShow [fof| (i(x) * x = 1) |])
                , $(testEquals "parse 3") [fof| ⊤⇒(∀x. ⊤) |]
                       [fof| true ==> forall x. true |]
                , $(testEquals "parse 4") "⊤"
                       (prettyShow [fof| true |])
                , $(testEquals "parse 5") "⊥"
                       (prettyShow [fof| false |])
                ])
