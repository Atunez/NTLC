module Lambda where

open import BasicLogic public
open import Lifting public
open import Terms public
open import Substitution public
open import Occurrences public
-- open import Reductions public

ω : ∀ {X} → Λ X
ω = abs (app (var o) (var o))
