module ATP
    ( module Lib
    , module Pretty
    , module Formulas
    , module Lit
    , module Prop
    , module PropExamples
    , module DefCNF
    , module DP
    , module Term
    , module Apply
    , module Equate
    , module FOL
    , module Skolem
    , module Parser
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
import Prop hiding (Atom, nnf, T, F, Not, And, Or, Imp, Iff)
import PropExamples hiding (K)
import DefCNF
import DP
import Term
import Apply
import Equate
import FOL
import Skolem
import Parser
import Herbrand
import Unif
import Tableaux hiding (K)
import Resolution
import Prolog
import Meson
import Equal
