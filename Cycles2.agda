module Cycles2 where

open import Lambda public


-- If you walk along the following path:
-- I(\x.P)Q → (\x.P)Q → I(\x.P)Q
-- Then P and Q can't be finite terms.
I : ∀ {X} → Λ X
I = abs (var o)

PA1 : ∀ {X} (P : Λ (↑ X)) (Q : Λ X) → app (app I (abs P)) Q ⟶ app (abs P) Q → P [ Q ]ₒ ≡ app (app I (abs P)) Q  → ⊥
PA1 (var (i x)) Q r1 ()
PA1 (var o) Q r1 ()
PA1 (app P1 P2) Q (appL→ (redex .(var o) .(abs (app P1 P2)))) r2 with app≡inv r2
PA1 (app (var x) P2) Q (appL→ (redex .(var o) .(abs (app (var x) P2)))) r2 | p1 , p2 = {!   !}
PA1 (app (app P1 P3) P2) Q (appL→ (redex .(var o) .(abs (app (app P1 P3) P2)))) r2 | p1 , p2 with app≡inv p1
... | (p11 , p12) = {!   !}

-- If you walk along the following path:
-- M≡(\x.\y.L[x,y])PQ → (\y.L[P,y])Q → L[P,Q]≡M
-- Then, Q ≡ \xy.yxy OR P ≡ Q × (P ≡ \xy.yxx OR \xy.yyx) OR Q ≡ \xy.y?y where ? doesn't contain b as the LHS of App
PA2 : ∀ (L : Λ (↑ (↑ ⊥))) (P Q : Λ ⊥) → app (app (abs (abs L)) P) Q ⟶ app (abs (L [ Λ→i P ]ₒ)) Q → app (abs (L [ Λ→i P ]ₒ)) Q ⟶ L [ Λ→i P ]ₒ [ Q ]ₒ → L [ Λ→i P ]ₒ [ Q ]ₒ ≡ app (app (abs (abs L)) P) Q → ⊥
PA2 (var (i (i ()))) P Q (appL→ r1) r2 p
PA2 (var (i o)) P Q (appL→ r1) r2 ()
PA2 (var o) P Q (appL→ r1) r2 p = {!   !}
PA2 (app (var (i o)) L₁) P Q (appL→ r1) r2 p = {!   !}
PA2 (app (var o) L₁) P Q (appL→ r1) r2 p = {!   !}
PA2 (app (app L L₂) L₁) P Q (appL→ r1) r2 p = {!   !}

PAError : ∀ (P : Λ (↑ ⊥)) (Q : Λ ⊥) → app (app I (abs P)) Q ⟶ app (abs P) Q → app (abs P) Q ⟶ app (app I (abs P)) Q  → ⊥
PAError P Q (appL→ r1) r2 = {!   !} -- Case r2 fails.
