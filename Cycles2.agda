
{-# OPTIONS --allow-unsolved-metas #-}

module Cycles2 where

open import Lambda public
open import Cycles public
open import Length public


-- If you walk along the following path:
-- I(\x.P)Q → (\x.P)Q → I(\x.P)Q
-- Then P and Q can't be finite terms.
I : ∀ {X} → Λ X
I = abs (var o)

eq21Helper : ∀ {X} (M : Λ (↑ (↑ X))) (N : Λ X) → bind (io var (Λ→ i N)) M ≡ var o → M ≡ var (i o)
eq21Helper (var (i o)) N p = refl
eq21Helper (var o) N p = exfalso ((o∉Λ→i N) (var∈≡ (Λ→ i N) o p))

bindOnNoVar : ∀ {X} (M : Λ (↑ X)) (N : Λ X) (f : ↑ X → Λ X) x → ¬ (x ∈ M) → (∀ (z : ↑ X) → z ∈ M → (z ≡ x × f x ≡ N) ⊔ len (f z) ≡ O) → len (bind f M) ≡ len M
bindOnNoVar M N f x nocc fn = {!   !}

eq21L3 : ∀ {X} (L3 L12 : Λ (↑ (↑ X))) (P Q : Λ X) → L3 ≡ var (i o) → bind (io var Q) (bind (io var (Λ→ i P)) L12) ≡ app (abs (abs (app L12 L3))) P → ⊥ 
eq21L3 .(var (i o)) (var (i o)) P Q refl p2 = {!    !} -- None Pure Bicycle (P20, First Blue)
eq21L3 .(var (i o)) (var o) P Q refl p2 =
  let noBind = bindOnNoVar (Λ→ i P) Q (io var Q) o (o∉Λ→i P) λ {(i x) → λ _ → inr refl
                                                              ; o → λ _ → inl (refl , refl)}
  in len≡≠ _ _ p2 (λ q → ¬S4 refl (~ (len→ i P) ! ~ noBind ! q))
eq21L3 .(var (i o)) (app L1 L2) P Q refl p2 = {!    !} -- LercherEq3?

eq21 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → (L [ Λ→i P ]ₒ) [ Q ]ₒ ≡ app (app (abs (abs L)) P) Q → ⊥
eq21 (var (i (i x))) P Q ()
eq21 (var (i o)) P Q ()
eq21 (var o) P Q e = {!  !} -- Impossible, RHS of e can't contain O since LHS doesn't
eq21 (app L12 L3) P Q e with app≡inv e
... | (e1 , e2) = case (λ {x → {! eq21Helper L3 _ x  !}}) (λ {x → {!   !}}) (lercherEq3 (bind (io var (Λ→ i P)) L3) Q e2)

-- If you walk along the following path:
-- M≡(\x.\y.L[x,y])PQ → (\y.L[P,y])Q → L[P,Q]≡M
-- Then, Q ≡ \xy.yxy OR P ≡ Q × (P ≡ \xy.yxx OR \xy.yyx) OR Q ≡ \xy.y?y where ? doesn't contain b as the LHS of App
PA2 : ∀ (L : Λ (↑ (↑ ⊥))) (P Q t1 t2 : Λ ⊥) → app (app (abs (abs L)) P) Q ⟶ t1 → t1 ≡ app (abs (L [ Λ→i P ]ₒ)) Q → app (abs (L [ Λ→i P ]ₒ)) Q ⟶ t2 → t2 ≡ L [ Λ→i P ]ₒ [ Q ]ₒ → ⊥
PA2 L P Q .(app (abs L [ P ]ₒ) Q) .((L [ Λ→i P ]ₒ) [ Q ]ₒ) (appL→ (redex .(abs L) .P)) p1 r2 refl = {!   !}

eq1617C1 : ∀ {X} (P12 : Λ (↑ X)) (Q : Λ X) → Q ≡ I → P12 [ Q ]ₒ ≡ abs (app (app (var o) P12) (var o)) → ⊥
eq1617C1 (var (i x)) .I refl ()
eq1617C1 (var o) .I refl ()
eq1617C1 (abs (var (i (i x)))) .I refl ()
eq1617C1 (abs (var (i o))) .I refl ()
eq1617C1 P@(abs (app P12 (var (i (i x))))) .I refl ()
eq1617C1 P@(abs (app P12 (var (i o)))) .I refl ()
eq1617C1 P@(abs (app (var (i (i x))) (var o))) .I refl ()
eq1617C1 P@(abs (app (var (i o)) (var o))) .I refl ()
eq1617C1 P@(abs (app (app (var (i (i x))) P13) (var o))) .I refl ()
eq1617C1 P@(abs (app (app (var (i o)) P13) (var o))) .I refl ()
-- Unsure how to approach this case?
eq1617C1 P@(abs (app (app (var o) P13) (var o))) .I refl p2 = {!   !}

eq1617 : ∀ {X} (P11 P12 P2 : Λ (↑ X)) (Q : Λ X) → P11 [ Q ]ₒ ≡ I → P12 [ Q ]ₒ ≡ abs (app (app P11 P12) P2) → P2 [ Q ]ₒ ≡ Q → ⊥
-- These are cases 1 and 2 on page 17
eq1617 (var o) P12 P2 Q p1 p2 p3 = case (λ {refl → {!   !}}) (λ {refl → {!   !}}) (lercherEq3 P2 Q p3)
eq1617 (abs (var (i o))) P12 P2 Q p1 p2 p3 with abs≡inv p1
... | p4 = (o∉Λ→i Q) (var∈≡ (Λ→ i Q) o p4)
-- These are cases 3 and 4 on page 18
eq1617 (abs (var o)) P12 P2 Q p1 p2 p3 = case (λ {refl → {!   !}}) (λ {refl → {!   !}}) (lercherEq3 P2 Q p3)

eq9Helper : ∀ {X} (P : Λ (↑ (↑ X))) (Q1 Q2 : Λ X) → bind (lift (io var (app Q1 Q2))) P ≡ var o → P ≡ var o 
eq9Helper (var (i (i x))) Q1 Q2 ()
eq9Helper (var (i o)) Q1 Q2 ()
eq9Helper (var o) Q1 Q2 p = refl

eq9 : ∀ {X} (P : Λ (↑ X)) (Q : Λ X) → P [ Q ]ₒ ≡ app (app I (abs P)) Q → ⊥
eq9 (var (i x)) Q ()
eq9 (var o) Q ()
eq9 (app (var o) P2) Q e with app≡inv e
-- Not Pure Reduction here... P16
... | (e1 , e2) = case (λ {refl → {!   !}}) (λ {refl → len≡≠ _ _ e1 (λ q → ¬S4 (~ len→ i Q) q)}) (lercherEq3 P2 Q e2)
eq9 (app (app P1 P3) P2) Q e with app≡inv e
... | e1 , e2 with app≡inv e1
... | (e3 , e4) = eq1617 P1 P3 P2 Q e3 e4 e2

PA1 : ∀ {X} (P : Λ (↑ X)) (Q t1 t2 : Λ X) → app (app I (abs P)) Q ⟶ t1 → t1 ≡ app (abs P) Q → app (abs P) Q ⟶ t2 → t2 ≡ app (app I (abs P)) Q  → ⊥
PA1 P Q .(app _ Q) .(P [ Q ]ₒ) (appL→ r1) p1 (redex .P .Q) p2 = eq9 P Q p2
PA1 P Q .(app _ Q) .(app (abs _) Q) (appL→ r1) p1 (appL→ (abs→ r2)) p2 with app≡inv p2
... | ()
       