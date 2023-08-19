module Factorization where

open import Lambda
open import Standarization

{-
Trying to prove the following fact.
Given: c [ f ] ⇒ u
Get: c ⇒ c' [ p ], p is applicative context, p : X → Λ X
  [so p x = x P1 .. Pk, but Pi might contain x or other vars in X]
u ≡ c' [ q ]
∀ x → p x [ f ] ⇒ q x
-}
-- p x = app (app x (p1)) p2 ...

record subred {X Y : Set} (C : Λ X) (f : X → Λ Y) (u : Λ Y) : Set where
  field
    Ctgt : Λ X
    Cred : C ⇒ Ctgt
    scope : X → Λ X
    gsub :  X → Λ Y
    gred : ∀ x → (scope x [ f ]) ⇒ gsub x
    -- gred : ∀ x → (scope x [ f ]) →s gsub x
    result : Ctgt [ gsub ] ≡ u

-- record subwred {X Y : Set} (C : Λ X) (f : X → Λ Y) (u : Λ Y) : Set where

-- FactWhed : ∀ {X Y : Set} (C : Λ X) (f : X → Λ Y) (u : Λ Y) → (C [ f ]) →w u
--            →

FactLemma : ∀ {X Y : Set} (C : Λ X) (f : X → Λ Y) (u : Λ Y) → (C [ f ]) →s u → subred C f u
FactLemma C f u ρ = {!    !}
