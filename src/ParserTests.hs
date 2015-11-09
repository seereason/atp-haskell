{-# LANGUAGE OverloadedStrings, QuasiQuotes, RankNTypes, ScopedTypeVariables #-}
module ParserTests where

import Equate ((.=.))
import Language.Haskell.Exts hiding (Pretty)
import Pretty (assertEqual', Pretty(..), prettyShow)
import Prop ((.&.), (.=>.))
import QuantifiedParser (fof, parseFOL)
import Skolem (Formula)
import Test.HUnit
import Text.Parsec (ParseError)

t :: (Eq a, Pretty a) => String -> a -> a -> Test
t label expected actual = TestLabel label (TestCase (assertEqual' label expected actual))

testParser :: Test
testParser =
    TestLabel "Parser"
      (TestList [ TestLabel "precedence 1a" $ TestCase $ assertEqual' "precedence 1a"  (Right [fof| ∃x. (true & (∃y. true)) |])    (parseFOL " ∃x. (true & ∃y. true) ")
                , TestLabel "precedence 1b" $ TestCase $ assertEqual' "precedence 1b"  [fof| (∃x. true) & (∃y. true) |]      [fof| ∃x. true & ∃y. true |]
                , TestLabel "precedence 2" $ TestCase $ assertEqual' "precedence 2"    [fof| (true & false) | true |]      [fof| true & false | true |]
                , TestLabel "precedence 3" $ TestCase $ assertEqual' "precedence 3"    [fof| (true | false) <==> true |]   [fof| true | false <==> true |]
                , TestLabel "precedence 4" $ TestCase $ assertEqual' "precedence 4"    [fof| true <==> (false ==> true) |] [fof| true <==> false ==> true |]
                , TestLabel "precedence 5" $ TestCase $ assertEqual' "precedence 5"    [fof| (~ true) & false |]           [fof| ~ true & false |]
                -- repeated prefix operator with same precedences fails:
                , TestLabel "precedence 6" $ TestCase $ assertEqual "precedence 6"    (Right [fof| ∃ x. (∃ y. x=y) |])    (parseFOL " ∃x. ∃y. x=y " :: Either ParseError Formula)
                , TestLabel "precedence 7" $ TestCase $ assertEqual' "precedence 7"    [fof| ∃x. (∃y. (x=y)) |]            [fof| ∃x y. x=y |]
                , TestLabel "precedence 8" $ TestCase $ assertEqual' "precedence 8"    [fof| ∀x. (∃y. (x=y)) |]            [fof| ∀x. ∃y. x=y |]
                , TestLabel "precedence 9" $ TestCase $ assertEqual' "precedence 9"    [fof| ∃y. (∀x. (x=y)) |]            [fof| ∃y. (∀x. x=y) |]
                , TestLabel "precedence 10" $ TestCase $ assertEqual' "precedence 10"  [fof| (~P) & Q |]                   [fof| ~P & Q |] -- ~ vs &
                -- repeated prefix operator with same precedences fails:
                , TestLabel "precedence 10" $ TestCase $ assertEqual "precedence 10a" (Right [fof| ~(~P) |])              (parseFOL " ~~P " :: Either ParseError Formula)
                , TestLabel "precedence 11" $ TestCase $ assertEqual' "precedence 11"  [fof| (P & Q) | R |]                [fof| P & Q | R |] -- & vs |
                , TestLabel "precedence 12" $ TestCase $ assertEqual' "precedence 12"  [fof| (P | Q) ==> R |]              [fof| P | Q ==> R |] -- or vs imp
                , TestLabel "precedence 13" $ TestCase $ assertEqual' "precedence 13"  [fof| (P ==> Q) <==> R |]           [fof| P ==> Q <==> R |] -- imp vs iff
             -- , TestCase "precedence 14" [fof| ∃x. (∀y. x=y) |] [fof| ∃x.  ∀y. x=y |]
                , TestLabel "precedence 14a" $ TestCase $ assertEqual' "precedence 14a"  [fof| ((x = y) ∧ (x = z)) ⇒ (y = z) |] ("x" .=. "y" .&. "x" .=. "z" .=>. "y" .=. "z")
                , TestLabel "pretty 1" $ TestCase $ assertEqual' "pretty 1" "∃x y. (∀z. (F(x,y)⇒F(y,z)∧F(z,z))∧(F(x,y)∧G(x,y)⇒G(x,z)∧G(z,z)))"
                                                                            (prettyShow [fof| ∃ x y. (∀ z. ((F(x,y)⇒F(y,z)∧F(z,z))∧(F(x,y)∧G(x,y)⇒G(x,z)∧G(z,z)))) |])
                , TestLabel "pretty 2" $ TestCase $ assertEqual' "pretty 2" [fof| (∃x. ((x)=(f((g((x))))))∧(∀x'. (x')=(f((g((x')))))⇒(x)=(x')))⇔(∃y. (y)=(g((f((y)))))∧(∀y'. (y')=(g((f((y')))))⇒(y)=(y'))) |]
                                                                            [fof| (exists x. (x = f(g(x))) /\ forall x'. (x' = f(g(x'))) ==> (x = x')) .<=>.
                                                                                  (exists y. (y = g(f(y))) /\ forall y'. (y' = g(f(y'))) ==> (y = y')) |]
                -- We could use haskell-src-meta to perform the third
                -- step of the round trip, roughly
                --
                --   1. formula string to parsed formula expression (Parser.parseExp)
                --   2. formula expression to parsed haskell-src-exts expression (show and th-lift?)
                --   3. haskell-src-exts to template-haskell expression (the toExp method of haskell-src-meta)
                --   4. template haskell back to haskell expression (template-haskell unquote)
                , TestLabel "read 1" $ TestCase $ assertEqual' "read 1" (show (ParseOk (InfixApp (App
                                                                                                  (App (Var (UnQual (Ident "for_all"))) (Lit (String "x")))
                                                                                                  (Paren (Lit (String "x")))) (QVarOp (UnQual (Symbol ".=."))) (Paren (Lit (String "x"))))))
                             $(show (parseExp (show [fof| ∀x. (x=x) |])))
                , TestLabel "read 2" $ TestCase $ assertEqual' "read 2" (show (ParseOk (InfixApp (Paren (App (App (App (App (Var (UnQual (Ident "for_all"))) (Lit (String "x")))
                                                                                                                   (Var (UnQual (Ident "pApp"))))
                                                                                                              (Paren (App (Var (UnQual (Ident "fromString"))) (Lit (String "P")))))
                                                                                                         (List [Lit (String "x")])))
                                                                                        (QVarOp (UnQual (Symbol ".&.")))
                                                                                        (App (App (Var (UnQual (Ident "pApp")))
                                                                                              (Paren (App (Var (UnQual (Ident "fromString")))
                                                                                                      (Lit (String "Q")))))
                                                                                         (List [Lit (String "x")])))))
                             (show (parseExp (show [fof| ∀x. P(x) ∧ Q(x) |])))

                , TestLabel "parse 1" $ TestCase $ assertEqual' "parse 1" [fof| (forall x. i(x) * x = 1) ==> (forall x. i(x) * x = 1) |] [fof| (forall x. i(x) * x = 1) ==> forall x. i(x) * x = 1 |]
                , TestLabel "parse 2" $ TestCase $ assertEqual' "parse 2" "i(x) * x = 1" (prettyShow [fof| (i(x) * x = 1) |])
                , TestLabel "parse 3" $ TestCase $ assertEqual' "parse 3" [fof| ⊤⇒(∀x. ⊤) |] [fof| true ==> forall x. true |]
                , TestLabel "parse 4" $ TestCase $ assertEqual' "parse 4" "⊤" (prettyShow [fof| true |])
                , TestLabel "parse 5" $ TestCase $ assertEqual' "parse 5" "⊥" (prettyShow [fof| false |])
                ])
