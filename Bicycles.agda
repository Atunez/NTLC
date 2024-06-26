module Bicycles where

open import Lambda public
-- open import BicyclesCase1 public
open import Length public
open import Cycles public
open import Decidability public

data InfiniteSolutions {X : Set} : Set where
  inf1 : ∀ {M : Λ X} → M ≡ app (app I I) M → InfiniteSolutions
  inf2 : ∀ {M Q : Λ X} → M ≡ app Q Q → Q ≡ app I (abs (app (var o) (Λ→i Q))) → InfiniteSolutions
  inf3 : ∀ {M P : Λ X} → M ≡ app (app I P) I → P ≡ abs (app (app (var o) (Λ→i P)) (var o)) → InfiniteSolutions -- check!!
  -- inf4 : ∀ {M : Λ X} {P12 : Λ (↑ X)} → M ≡ app (app I (P12 [ I ]ₒ)) I → P12 ≡ abs (app (app (var o) (Λ→ (io (i ∘ i) o) P12)) (var (i o))) → InfiniteSolutions -- check!
  -- inf4 : ∀ {M : Λ X} {P12 : Λ (↑ X)} → M ≡ app (app I (P12 [ I ]ₒ)) I → P12 ≡ abs (app (app (var o) (P12 [ lift (var ∘ i )])) (var (i o))) → InfiniteSolutions -- check!
  -- inf4 : ∀ {M : Λ X} {P12 : Λ (↑ X)} → M ≡ app (app I (P12 [ I ]ₒ)) I → P12 ≡ abs (app (app (var o) (P12 [ lift var ])) (var (i o))) -- check!
                                      -- P [ lift var ] should (?) keep o the same, rename i x to i (i x), weakening out (i o)
                                      -- the same thing as Λ↑ (Λ→i P) ?
                                      -- ANYWAY, THIS IS CASE IP12[I]I -> P12[I]I after equation (19)
                                      -- leave this be for now...?
  inf4 : ∀ {M P12 : Λ X} → M ≡ app (app I P12) I → P12 ≡ abs (app (app (var o) (Λ→i P12)) I) → InfiniteSolutions
  inf5 : ∀ {M P Q : Λ X} → M ≡ app P Q → P ≡ app (abs (abs (app (var (i o)) (var o)))) P → InfiniteSolutions
  inf6 : ∀ {M P Q : Λ X} → M ≡ app Q Q → Q ≡ app (abs ω) P → InfiniteSolutions
  inf10 : ∀ {M P : Λ (↑ X)} → M ≡ app P I → P ≡ abs (app (var o) (app (Λ→ (↑→ i) P) (var o) )) → InfiniteSolutions
  inf11 : ∀ {M P : Λ (↑ X)} → M ≡ app P I → P ≡ abs (app (var o) (app (Λ→ (↑→ i) P)  I     )) → InfiniteSolutions
  -- infinitary one-step solution, p26l6
  inf13 : ∀ {M P N : Λ (↑ X)} → M ≡ app P N → P ≡ abs (app (var o) (Λ→ (↑→ i) P)) → N ≡ abs (app (var o) (Λ→ (↑→ i) N)) → InfiniteSolutions
  inf21 : ∀ {M P Q : Λ X} → M ≡ P → P ≡ app (app (abs (abs (var (i o)))) P) Q → InfiniteSolutions
  inf22 : ∀ {M P Q : Λ X} → M ≡ Q → Q ≡ app (app (abs (abs (var o))) P) Q → InfiniteSolutions
λxy→yxy : ∀ {X} → Λ X
λxy→yxy = abs (abs (app (app (var o) (var (i o)) ) (var o)) )

yxy : ∀ {X} → Λ (↑ (↑ X))
yxy = abs (abs ((app (app (var o) (var (i o))) (var o))) )

data TwoCycleSolutionsNormalized {X : Set} : Set where
  pure0n : ∀ {M : Λ X} → M ≡ app ω ω → TwoCycleSolutionsNormalized
  -- pure
  -- yellow box between (28) and (29)
  pure1n : ∀ {M P Q : Λ X} → M ≡ app (app Q P) Q → Q ≡ abs (abs (app (app (var o) (var (i o))) (var o))) → pure M → TwoCycleSolutionsNormalized
  pure2n : ∀ {M P Q : Λ X} {L : Λ (↑ (↑ X))} → M ≡ app (app Q P) Q → Q ≡ abs (abs (app (app (var o) L) (var o))) → L [ io (io var P) Q ] ≡ P → pure M → TwoCycleSolutionsNormalized
  pure3n : ∀ {M P : Λ X} → M ≡ app (app P P) P → P ≡ abs (abs (app (app (var o) (var o)) (var (i o)))) → TwoCycleSolutionsNormalized
  pure4n : ∀ {M P : Λ X} → M ≡ app (app P P) P → P ≡ abs (abs (app (app (var o) (var (i o))) (var (i o)))) → TwoCycleSolutionsNormalized


data TwoCycleSolutions {X : Set} : Set where
  -- Omega, the one-cycle
  pure0 : ∀ {M : Λ X} → M ≡ app ω ω → TwoCycleSolutions
  -- pure
  -- yellow box between (28) and (29)
  pure1 : ∀ {M P Q : Λ X} → M ≡ app (app Q P) Q → Q ≡ abs (abs (app (app (var o) (var (i o))) (var o))) → pure M → TwoCycleSolutions
  pure2 : ∀ {M P Q : Λ X} {L : Λ (↑ (↑ X))} → M ≡ app (app Q P) Q → Q ≡ abs (abs (app (app (var o) L) (var o))) → L [ io (io var P) Q ] ≡ P → pure M → TwoCycleSolutions
  pure3 : ∀ {M P : Λ X} → M ≡ app (app P P) P → P ≡ abs (abs (app (app (var o) (var o)) (var (i o)))) → TwoCycleSolutions
  pure4 : ∀ {M P : Λ X} → M ≡ app (app P P) P → P ≡ abs (abs (app (app (var o) (var (i o))) (var (i o)))) → TwoCycleSolutions
  -- impure
  imp1 : ∀ {M : Λ X} → M ≡ app (app I ω) (app I ω) → TwoCycleSolutions
  imp2 : ∀ {M : Λ X} → M ≡ app ω (abs (app ω (var o))) → TwoCycleSolutions
  imp3 : ∀ {M P Q : Λ X} {L1 L2 : Λ (↑ (↑ X))} → M ≡ app (app P P) Q → P ≡ abs (abs (app (app (var (i o)) L1) L2)) → L1 [ io (io var P) Q ] ≡ P → L2 [ io (io var P) Q ] ≡ Q → TwoCycleSolutions
  imp4 : ∀ {M P Q : Λ X} {L : Λ (↑ (↑ X))} → M ≡ app Q Q → Q ≡ app (abs (abs (app (var o) L))) P → L [ io (io var P) Q ] ≡ Q → TwoCycleSolutions
  imp5 : ∀ {M P Q : Λ X} → M ≡ app (app P P) Q → P ≡ abs (abs (app (app (var (i o)) (var (i o))) (var o))) → TwoCycleSolutions
  imp6 : ∀ {M P Q : Λ X} {L : Λ (↑ (↑ X))} → M ≡ app (app P P) Q → P ≡ abs (abs (app (app (var (i o)) L) (var o))) → L [ io (io var P) Q ] ≡ P → TwoCycleSolutions
  -- imp7 : ∀ {M P : Λ X} → M ≡ app (app P P) P → P ≡ abs (abs (app (app (var o) (var (i o))) (var (i o)))) → TwoCycleSolutions
  -- infinite
  inf : InfiniteSolutions {X} → TwoCycleSolutions

-- noInfiniteSolutions : InfiniteSolutions → ⊥
-- noInfiniteSolutions = {!   !}

_[_,,_] : ∀ {X} (M : Λ (↑ (↑ X))) (P Q : Λ X) → Λ X
_[_,,_] {X} M P Q  = M [ io (io var P) Q ]

-- -- case1 : ∀ {X} (P : Λ (↑ X)) (Q t1 t2 : Λ X) → app (app I (abs P)) Q ⟶ t1 → t1 ≡ app (abs P) Q → app (abs P) Q ⟶ t2 → t2 ≡ app (app I (abs P)) Q → TwoCycleSolutions {X}
-- case1 : ∀ {X} (P : Λ (↑ X)) (Q : Λ X) → P [ Q ]ₒ ≡ app (app I (abs P)) Q → TwoCycleSolutions {X}
-- case1 {X} P Q e = {!   !}
--
-- case2 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → L [ Q ,, P ] ≡ app (app (abs (abs L)) P) Q → TwoCycleSolutions {X}
-- case2 L P Q = {!   !}


record pure2loop {X : Set} : Set where
  constructor p2l
  field
    -- Xd : dec X
    A : Λ (↑ X)
    B : Λ X
    red : A [ io var B ] ⟶ (app (abs A) B)
    pur : pure (A [ io var B ])

record pureMatch {X} (M : Λ X) : Set where
  field
    cxt : Λ (↑ X)
    ploop : pure2loop
    M=C[Δ] :  M ≡ (cxt [ io var (app (abs (pure2loop.A ploop)) (pure2loop.B ploop)) ]) -- where open pure2loop ploop
-- pureMatch (p2l A B red pur) C M = M ≡ (C [ io var (app (abs A) B) ])

-- wrapper : ∀ {X} (M N : Λ X) → pure M → pure N → M ⟶ N → N ⟶ M → pureMatch M ⊔ pureMatch N
-- wrapper M N pM pN rM rN = {!   !}
-- wrapper2 : ∀ {X} (M N : Λ X) (p : pure M) (q : pure N) → (r : M ⟶ N) → (l : N ⟶ M) → pureMatch (wrapper1 M N p q r l)
