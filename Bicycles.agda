module Bicycles where

open import Lambda public
open import Cycles public
open import Length public

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

λxy→yxy : ∀ {X} → Λ X
λxy→yxy = abs (abs (app (app (var o) (var (i o)) ) (var o)) )

yxy : ∀ {X} → Λ (↑ (↑ X))
yxy = abs (abs ((app (app (var o) (var (i o))) (var o))) )


data TwoCycleSolutions {X : Set} : Set where
  -- pure
          -- yellow box between (28) and (29)
  pure1 : ∀ {M : Λ X} {P : Λ (↑ X)} → M ≡ app (app λxy→yxy (abs (app (app (var o) P) (var o)))) λxy→yxy → TwoCycleSolutions
  -- impure
  imp1 : ∀ {M : Λ X} → M ≡ app (app I ω) (app I ω) → TwoCycleSolutions
  -- infinite
  inf : InfiniteSolutions {X} → TwoCycleSolutions

-- noInfiniteSolutions : InfiniteSolutions → ⊥
-- noInfiniteSolutions = {!   !}
