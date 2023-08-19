module RZT where

open import Lambda
open import Standarization

record Zero {X : Set} (s : Λ X) : Set where
  field
    nowhnfTerm  : ∀ (t : Λ X) → (_→w_ *) s t → Λ X
    nowhnfProof : ∀ (t : Λ X) (W : (_→w_ *) s t) → t →w nowhnfTerm t W

Ω↓=Ω : ∀ {X} (t : Λ X) → Ω ⇒ t → Ω ≡ t
Ω↓=Ω .Ω (ε* .Ω) = refl
Ω↓=Ω t (c* (redex .(app (var o) (var o)) .ω) r) = Ω↓=Ω t r
Ω↓=Ω t (c* (appL→ (abs→ (appL→ ()))) r)
Ω↓=Ω t (c* (appL→ (abs→ (appR→ ()))) r)
Ω↓=Ω t (c* (appR→ (abs→ (appL→ ()))) r)
Ω↓=Ω t (c* (appR→ (abs→ (appR→ ()))) r)

Ω∈Zero : ∀ {X} → Zero {X} Ω
Ω∈Zero = record {
  nowhnfTerm = λ _ _ → Ω ;
  nowhnfProof = λ t W → transp (λ s → s →w Ω) (Ω↓=Ω t (mono* _→w_ _⟶_ w2⟶ W ) ) ε→w }

Rec : ∀ {X : Set} → Λ X → Set
Rec r = ∀ {t} → r ⇒ t → t ⇒ r

Ω∈Rec : ∀ {X} → Rec {X} Ω
Ω∈Rec Ωt with (Ω↓=Ω _ Ωt)
... | refl = Ωt

RZ : ∀ {X : Set} → Λ X → Set
RZ r = Rec r × Zero r

trivial : ∀ {X : Set} → Λ (↑ X) → Set
trivial t = (∀ z → (t ⇒ z) → o ∈ z) → t ⇒ var o

record subred {X Y : Set} (C : Λ X) (f : X → Λ Y) (u : Λ Y) : Set where
  constructor SubRed
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

RZrec : ∀ {X} (C : Λ (↑ X)) {r : Λ X} (rz : RZ r) → C [ r ]ₒ ⇒ r → trivial C
-- RZrec C (rrec , rzer) ρ u hyp = {!   !}
RZrec C {r} (rrec , rzer) ρ hyp with FactLemma C (io var r) r (standarization ρ)
... | SubRed Ctgt Cred scope gsub gred result with hyp Ctgt Cred
... | here = Cred
... | left occ t = {!   !}
... | right s occ = {!   !}
... | down occ = {!   !}
