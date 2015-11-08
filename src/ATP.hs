module ATP
    ( module Lib
    , module Pretty
    , module Formulas
    , module Lit
    , module LitParser
    , module Prop
    , module PropParser
    , module PropExamples
    , module DefCNF
    , module DP
    , module Term
    , module TermParser
    , module Apply
    , module Equate
    , module Quantified
    , module QuantifiedParser
    , module FOL
    , module Skolem
    , module Herbrand
    , module Unif
    , module Tableaux
    , module Resolution
    , module Prolog
    , module Meson
    , module Equal
    , module Text.PrettyPrint.HughesPJClass
    ) where

import Data.String ({-instances-})
import Text.PrettyPrint.HughesPJClass hiding ((<>))

import Lib
import Pretty
import Formulas
import Lit hiding (Atom, T, F, Not)
import LitParser
import Prop hiding (Atom, nnf, T, F, Not, And, Or, Imp, Iff)
import PropExamples hiding (K)
import PropParser
import DefCNF
import DP
import Term
import TermParser
import Apply
import Equate
import Quantified
import QuantifiedParser
import FOL
import Skolem
import Herbrand
import Unif
import Tableaux hiding (K)
import Resolution
import Prolog
import Meson
import Equal
