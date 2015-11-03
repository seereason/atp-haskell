{-# LANGUAGE QuasiQuotes, RankNTypes, ScopedTypeVariables #-}
module ParserTests where

import Language.Haskell.Exts hiding (Pretty)
import Language.Haskell.Exts.Parser -- (parseExp)
import Parser (fof)
import Pretty (assertEqual', Pretty, prettyShow)
import Skolem (MyFormula)
import Test.HUnit

t :: (Eq a, Pretty a) => String -> a -> a -> Test
t label expected actual = TestLabel label (TestCase (assertEqual' label expected actual))

testParser :: Test
testParser =
    TestLabel "Parser"
      (TestList [ t "precedence 1" [fof| (exists x. true) & (exists y. true) |]
                                   [fof|  exists x. true  &  exists y. true |]

                , t "precedence 2" [fof| (true & false) | true |]
                                   [fof| true & false | true |]

                , t "precedence 3" [fof| (true | false) <==> true |]
                                   [fof| true | false <==> true |]

                , t "precedence 4" [fof| (true <==> false) ==> true |]
                                   [fof| true <==> false ==> true |]

                , t "precedence 5" [fof| (~ true) & false |]
                                   [fof| ~ true & false |]

                -- repeated prefix operator with same precedences fails:
                -- unexpected "∃"
                -- expecting "(", expression, identifier, "nil", integer, "<", "|--", "true" or "false"
                -- (Pretty printer needs to account for this.)
                -- , t "precedence 6" [fof| ∃ x. (∃ y. x=y) |]
                --                    [fof| ∃ x. ∃ y. x=y |]

                , t "precedence 7" [fof| ∃x. (∃y. x=y) |]
                                   [fof| ∃x y. x=y |]

                , t "precedence 8" [fof| ∀x. (∃y. (x=y)) |]
                                   [fof| ∀x. ∃y. x=y |]
                -- We can say ∀x. ∃y., but not ∃y. ∀x.
                -- , t "precedence 9" [fof| ∃x. (∀y. x=y) |]
                --                    [fof| ∃x.  ∀y. x=y |]
                , t "pretty 1" "∃x y. ∀z. (F(x,y)⇒F(y,z)∧F(z,z))∧(F(x,y)∧G(x,y)⇒G(x,z)∧G(z,z))"
                               (prettyShow [fof| ∃ x y. (∀ z. ((F(x,y)⇒F(y,z)∧F(z,z))∧(F(x,y)∧G(x,y)⇒G(x,z)∧G(z,z)))) |])
                , t "read 1" (show (ParseOk (Paren (App (App (Var (UnQual (Ident "for_all"))) (Lit (String "x")))
                                                    (Paren (InfixApp (Paren (Lit (String "x"))) (QVarOp (UnQual (Symbol ".=.")))
                                                            (Paren (Lit (String "x")))))))))
                             (show (parseExp (show [fof| ∀x. x=x |])))
                , t "read 2" (show (ParseOk (Paren (InfixApp
                                                    (Paren (App
                                                            (App (Var (UnQual (Ident "for_all"))) (Lit (String "x")))
                                                            (Paren (App (App
                                                                         (Var (UnQual (Ident "pApp")))
                                                                         (Paren (App
                                                                                 (Var (UnQual (Ident "fromString")))
                                                                                 (Lit (String "P")))))
                                                                    (List [Lit (String "x")])))))
                                                    (QVarOp (UnQual (Symbol ".&.")))
                                                    (Paren (App
                                                            (App
                                                             (Var (UnQual (Ident "pApp")))
                                                             (Paren (App (Var (UnQual (Ident "fromString"))) (Lit (String "Q")))))
                                                            (List [Lit (String "x")])))))))
                             (show (parseExp (show [fof| ∀x. P(x) ∧ Q(x) |])))
                , t "read 3" (show (ParseOk (Paren (InfixApp (Paren (App
                                                                     (App (Var (UnQual (Ident "for_all"))) (Lit (String "x")))
                                                                     (Paren (App (App
                                                                                  (Var (UnQual (Ident "pApp")))
                                                                                  (Paren (App
                                                                                          (Var (UnQual (Ident "fromString")))
                                                                                          (Lit (String "P")))))
                                                                             (List [Lit (String "x")])))))
                                                    (QVarOp (UnQual (Symbol ".&.")))
                                                    (Paren (App
                                                            (App
                                                             (Var (UnQual (Ident "pApp")))
                                                             (Paren (App (Var (UnQual (Ident "fromString"))) (Lit (String "Q")))))
                                                            (List [Lit (String "x")])))))))
                             (show (parseExp (show [fof| ∀x. P(x) ∧ Q(x) |])))
                ])
