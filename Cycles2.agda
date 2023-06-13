module Cycles2 where

open import Lambda public
open import Cycles


-- If you walk along the following path:
-- I(\x.P)Q → (\x.P)Q → I(\x.P)Q
-- Then P and Q can't be finite terms.
I : ∀ {X} → Λ X
I = abs (var o)

-- PA1 : ∀ {X} (P : Λ (↑ X)) (Q : Λ X) → app (app I (abs P)) Q ⟶ app (abs P) Q → P [ Q ]ₒ ≡ app (app I (abs P)) Q  → ⊥
-- PA1 (var (i x)) Q r1 ()
-- PA1 (var o) Q r1 ()
-- PA1 (app P1 P2) Q (appL→ (redex .(var o) .(abs (app P1 P2)))) r2 with app≡inv r2
-- PA1 (app (var x) P2) Q (appL→ (redex .(var o) .(abs (app (var x) P2)))) r2 | p1 , p2 = {!   !}
-- PA1 (app (app P1 P3) P2) Q (appL→ (redex .(var o) .(abs (app (app P1 P3) P2)))) r2 | p1 , p2 with app≡inv p1
-- ... | (p11 , p12) = {!   !}

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

eq1617 : ∀ {X} (P11 P12 P2 : Λ (↑ X)) (Q : Λ X) → P11 [ Q ]ₒ ≡ I → P12 [ Q ]ₒ ≡ abs (app (app P11 P12) P2) → ⊥
eq1617 P11 P12 P2 Q e16 e17 = {!   !}

eq9 : ∀ {X} (P : Λ (↑ X)) (Q : Λ X) → P [ Q ]ₒ ≡ app (app I (abs P)) Q → ⊥
eq9 (var (i x)) Q ()
eq9 (var o) Q ()
eq9 (app P1 P2) Q e with app≡inv e
... | (e1 , e2) with lercherEq3 P2 Q e2
... | inl refl = {!   !} -- First solution on page 16
eq9 (app (var o) .(Λ→ i Q)) Q e | e1 , e2 | inr refl with bind-rec (app (abs (var o)) (abs (app (var o) (var (i o))))) (io var Q) {o} (right (abs (var o)) (down (right (var o) here))) (~ e1 )
... | ()
eq9 (app (app P1 P2) .(Λ→ i Q)) Q e | e1 , e2 | inr refl = ? 

PA1 : ∀ {X} (P : Λ (↑ X)) (Q t1 t2 : Λ X) → app (app I (abs P)) Q ⟶ t1 → t1 ≡ app (abs P) Q → app (abs P) Q ⟶ t2 → t2 ≡ app (app I (abs P)) Q  → ⊥
PA1 P Q .(app _ Q) .(P [ Q ]ₒ) (appL→ r1) p1 (redex .P .Q) p2 = eq9 P Q p2
PA1 P Q .(app _ Q) .(app (abs _) Q) (appL→ r1) p1 (appL→ (abs→ r2)) p2 with app≡inv p2
... | ()
