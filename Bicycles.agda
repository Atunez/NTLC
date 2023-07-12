module Bicycles where

open import Lambda public
-- open import BicyclesCase1 public
open import Length public
open import Cycles public

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

  inf10 : ∀ {M P : Λ X} → M ≡ app P I → P ≡ abs (app (var o) (app (Λ→i P) (var o))) → InfiniteSolutions
  inf11 : ∀ {M P : Λ X} → M ≡ app P I → P ≡ abs (app (var o) (app (Λ→i P)  I     )) → InfiniteSolutions
  -- infinitary one-step solution, p26l6
  inf13 : ∀ {M P N : Λ X} → M ≡ app P N → P ≡ abs (app (var o) (Λ→i P)) → N ≡ abs (app (var o) (Λ→i N)) → InfiniteSolutions

λxy→yxy : ∀ {X} → Λ X
λxy→yxy = abs (abs (app (app (var o) (var (i o)) ) (var o)) )

yxy : ∀ {X} → Λ (↑ (↑ X))
yxy = abs (abs ((app (app (var o) (var (i o))) (var o))) )


data TwoCycleSolutions {X : Set} : Set where
  -- Omega, the one-cycle
  pure0 : ∀ {M : Λ X} → M ≡ app ω ω → TwoCycleSolutions
  -- pure
          -- yellow box between (28) and (29)
  pure1 : ∀ {M : Λ X} {P : Λ (↑ X)} → M ≡ app (app λxy→yxy (abs (app (app (var o) P) (var o)))) λxy→yxy → TwoCycleSolutions
  -- impure
  imp1 : ∀ {M : Λ X} → M ≡ app (app I ω) (app I ω) → TwoCycleSolutions
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

case3 : ∀ {X} (N P : Λ (↑ X)) → N [ (P [ abs N ]ₒ) ]ₒ ≡ app (abs (app (var o) P)) (abs N) → TwoCycleSolutions {X}
case3 (var o) (var (i x)) ()
case3 (var o) (var o) ()
case3 (var o) (app P1 P2) e with app≡inv e
... | (e1 , e2) with lercherEq3 P2 I e2
... | inl refl = inf (inf10 e {!   !} )
... | inr refl = {!   !}
case3 (app N1 N2) P e with app≡inv e
case3 (app (var o) .(var o)) (var o) e | refl , e2 = pure0 {! e  !}
case3 (app (var o) N2) (abs P) e | e1 , e2 = {!   !}
case3 (app (abs N1) N2) P e | e1 , e2 = {!   !}
