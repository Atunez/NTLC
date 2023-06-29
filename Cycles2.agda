
{-# OPTIONS --allow-unsolved-metas #-}

module Cycles2 where

open import Lambda public
open import Cycles public
open import Length public

-- -- If a term contains x, and the result of binding any variable doesn't contain x,
-- -- then the term doesn't contain x after the bind.
-- x∈[f] : ∀ {X} {x : X} {s : Λ X} → x ∈ s → (f : X → Λ X) → (∀ z → z ∈ s → ¬ (x ∈ f z)) → ¬ (x ∈ (s [ f ]))
-- x∈[f] here f fn occ2 = fn _ here occ2
-- x∈[f] {x = x} (left occ t) f fn (left occ2 .(bind f t)) = x∈[f] occ f (λ q oc →  fn q (left oc t)) occ2
-- -- x is on the left of, but is on the right in the binding result, 
-- x∈[f] {x = x} (left {s} occ t) f fn (right .(bind f s) occ2) = {!   !}
-- x∈[f] (right s {t} occ) f fn (left occ2 .(bind f t)) = {!   !} -- x occurs on Right, but the result of binding contains it on the Left
-- x∈[f] (right s occ) f fn (right .(bind f s) occ2) = x∈[f] occ f (λ z z₁ → fn z (right s z₁)) occ2
-- x∈[f] (down occ) f fn (down occ2) = x∈[f] occ (lift f) (λ {(i y) → λ q oc → fn y (down q) (occInj i iInj _ (f y) oc)
--                                                          ; o → λ _ ()}) occ2 

-- x∈[Q] : ∀ {X} {x : X} {s : Λ (↑ (↑ X))} (Q : Λ (↑ X)) → o ∈ s → o ∈ s [ Q ]ₒ → o ∈ Q
-- x∈[Q] Q here occ2 = {!   !}
-- x∈[Q] Q (left occ t) occ2 = {!   !}
-- x∈[Q] Q (right s occ) occ2 = {!   !}
-- x∈[Q] Q (down occ) occ2 = {!   !}
-- If you walk along the following path:
-- I(\x.P)Q → (\x.P)Q → I(\x.P)Q
-- Then P and Q can't be finite terms.
I : ∀ {X} → Λ X
I = abs (var o)

appVar : ∀ {X} (P1 P2 : Λ X) x → app P1 P2 ≡ var x → ⊥
appVar P1 P2 x () 

absApp : ∀ {X} (P1 P2 : Λ X) P3 → abs P3 ≡ app P1 P2 → ⊥
absApp P1 P2 P3 ()


-- eq21Helper : ∀ {X} (M : Λ (↑ (↑ X))) (N : Λ X) → bind (io var (Λ→ i N)) M ≡ var o → M ≡ var (i o)
-- eq21Helper (var (i o)) N p = refl
-- eq21Helper (var o) N p = exfalso ((o∉Λ→i N) (var∈≡ (Λ→ i N) o p))

-- bindOnNoVar : ∀ {X} (M : Λ (↑ X)) (N : Λ X) (f : ↑ X → Λ X) x → ¬ (x ∈ M) → (∀ (z : ↑ X) → z ∈ M → (z ≡ x × f x ≡ N) ⊔ len (f z) ≡ O) → len (bind f M) ≡ len M
-- bindOnNoVar M N f x nocc fn = {!   !}

-- eq21P2Lemma : ∀ {X} (M : Λ (↑ (↑ X))) (Q : Λ (↑ X)) (f : ↑ (↑ X) → Λ (↑ X)) → (∀ x → (x ∈ f (i x)) ⊔ (f (i x) ≡ Q)) → M [ f ] ≡ Q → ¬ (i o ∈ M)
-- eq21P2Lemma (var .(i o)) Q f fn p here = {! 
--    !}
-- eq21P2Lemma (app M M₁) Q f fn p occ = {!   !}
-- eq21P2Lemma (abs M) Q f fn p occ = {!   !}

-- eq24 : ∀ {X} (L12 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (io var (Λ→ i P)) L12) ≡ app (abs (abs (app L12 (var (i o))))) P → pure (app (abs (abs (app L12 (var (i o))))) P) → ⊥
-- eq24 (var (i o)) P Q e p = {!    !}
-- eq24 (var o) P Q e p = {!   !}
-- eq24 (app L12 L13) P Q e p = {!   !}

-- -- If L3[Q, P] = Q, then either L3 is y or L3[y, x] = L3[x], ie y ∉ L3
-- eq21L3 : ∀ {X} (L3 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (io var (Λ→ i P)) L3) ≡ Q → L3 ≡ var (i o) ⊔ ¬ ((i o) ∈ L3) 
-- eq21L3 (var (i (i x))) P Q p = inr λ ()
-- eq21L3 (var (i o)) P Q p = inl refl
-- eq21L3 (var o) P Q p = inr λ ()
-- eq21L3 (app L3 L4) P Q p = inr λ {(left q .L4) → {!   !}
--                                 ; (right .L3 q) → {!   !}}
-- eq21L3 (abs L3) P (abs Q) p with abs≡inv p
-- ... | p2 = inr λ {(down q) → {!   !} (∈[f] L3 Q (io var (Λ→ i P)) o here q)}

-- eq21 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → (L [ Λ→i P ]ₒ) [ Q ]ₒ ≡ app (app (abs (abs L)) P) Q → pure (app (app (abs (abs L)) P) Q) → ⊥
-- -- L is a free var
-- eq21 (var (i (i x))) P Q () p
-- -- L is var y
-- eq21 (var (i o)) P Q () p
-- -- L is var x
-- eq21 (var o) P Q e p = -- Impossible, RHS of e can't contain O since LHS doesn't
--   let noBind = bindOnNoVar (Λ→ i P) Q (io var Q) o (o∉Λ→i P) λ {(i x) → λ _ → inr refl
--                                                               ; o → λ _ → inl (refl , refl)} 
      
--   in len≡≠ _ _ e (λ q → ¬S< (~ (len→ i P) ! ~ noBind ! q) (<Prf _ _)) where
--     <Prf : ∀ (m n : Nat) → m < S (S (S (S (m ++ n))))
--     <Prf O n = O< (S (S (S n)))
--     <Prf (S m) n = S< m (S (S (S (S (m ++ n))))) (<Prf m n)
-- -- L is L12[y, x]L3[y, x]
-- eq21 (app L12 L3) P Q e p with app≡inv e
-- -- e1 = L12[Q, P] = (\x\y.L12[y, x]L3[y, x])P
-- -- e2 = L3[Q, P] = Q
-- ... | (e1 , e2) with eq21L3 L3 P Q e2 
-- ... | inl refl = {!   !} 
-- ... | inr x = {!   !}

-- -- If you walk along the following path:
-- -- M≡(\x.\y.L[x,y])PQ → (\y.L[P,y])Q → L[P,Q]≡M
-- -- Then, Q ≡ \xy.yxy OR P ≡ Q × (P ≡ \xy.yxx OR \xy.yyx) OR Q ≡ \xy.y?y where ? doesn't contain b as the LHS of App
-- PA2 : ∀ (L : Λ (↑ (↑ ⊥))) (P Q t1 t2 : Λ ⊥) → app (app (abs (abs L)) P) Q ⟶ t1 → t1 ≡ app ((abs L) [ P ]ₒ) Q → app ((abs L) [ P ]ₒ) Q ⟶ t2 → t2 ≡ L [ Λ→i P ]ₒ [ Q ]ₒ → ⊥
-- PA2 L P Q t1 t2 r1 p1 r2 p2 = {!   !}
-- -- PA2 L P Q t1 .(bind (lift (io var P)) L [ Q ]ₒ) r1 p1 (redex .(bind (lift (io var P)) L) .Q) p2 = {!   !}
-- -- PA2 L P Q t1 .(app _ Q) r1 p1 (appL→ r2) p2 = {!   !}
-- -- PA2 L P Q t1 .(app (abs L [ P ]ₒ) _) r1 p1 (appR→ r2) p2 = {!   !}


-- CCGenG : ∀ {X} (P12 P22 Q : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → bind f P12 ≡ abs (app (app P22 P12) Q) → P12 ≡ var o
-- CCGenG (var (i x)) P22 Q f fn p with fn x (transp (λ t → x ∈ t) (~ p) (down (left (right P22 here) Q)))
-- ... | q with ~ q ! p
-- ... | ()
-- CCGenG (var o) P22 Q f fn p = refl
-- CCGenG (abs (var (i x))) P22 Q f fn p = {!   !}
-- CCGenG (abs (app (var (i x)) P13)) P22 Q f fn p with app≡inv (abs≡inv p)
-- ... | p1 , p2 = {!   !}
-- CCGenG (abs (app (app P12 P14) P13)) P22 Q f fn p with app≡inv (abs≡inv p)
-- ... | p1 , p2 with app≡inv p1
-- ... | p3 , p4 with CCGenG P14 P12 P13 (lift f) (λ {(i x) → λ q → ext (Λ→ i) (fn x (occInj i iInj x (f (i x)) q))
--                                             ; o → λ q → exfalso (o∉Λ→i (f o) q)}) p4
-- CCGenG (abs (app (app P12 .(var o)) P13)) P22 Q f fn p | p1 , p2 | p3 , () | refl

CCGen : ∀ {X} (P12 Q : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → bind f P12 ≡ abs (app (app (var o) P12) Q) → P12 ≡ var o
CCGen (var (i x)) Q f fn p with fn x (transp (λ t → x ∈ t) (~ p) (down (left (right (var o) here) Q)))
... | q with ~ q ! p
... | ()
CCGen (var o) Q f fn p = refl
CCGen (abs (var (i x))) Q f fn p with abs≡inv p
... | p1 = exfalso (o∉Λ→i (f x) (transp (λ t → o ∈ t) (~ p1) (left (left here (abs (var (i x)))) Q)))
CCGen (abs (app (var x) P13)) Q f fn p with app≡inv (abs≡inv p)
CCGen (abs (app (var (i x)) P13)) Q f fn p | p1 , p2 = exfalso (o∉Λ→i (f x) (transp (λ t → o ∈ t) (~ p1) (left here (abs (app (var (i x)) P13)))))
CCGen (abs (app (app (var (i x)) P14) P13)) Q f fn p with app≡inv (abs≡inv p)
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (o∉Λ→i (f x) (transp (λ t → o ∈ t) (~ p3) here))
CCGen (abs (app (app (var o) P14) P13)) Q f fn p with app≡inv (abs≡inv p)
... | p1 , p2 with app≡inv p1
... | p3 , p4 with CCGen P14 P13 (lift f) (λ {(i x) → λ q → ext (Λ→ i) (fn x (occInj i iInj x (f (i x)) q))
                                            ; o → λ q → exfalso (o∉Λ→i (f o) q)}) p4 
CCGen (abs (app (app (var o) .(var o)) P13)) Q f fn p | p1 , p2 | p3 , () | refl

eq1617C1 : ∀ {X} (P12 : Λ (↑ X)) (Q : Λ X) → Q ≡ I → P12 [ Q ]ₒ ≡ abs (app (app (var o) P12) (var o)) → ⊥
eq1617C1 P12 Q p1 p2 with CCGen P12 (var o) (io var Q) (λ x _ → refl) p2 -- C1Gen P12 Q (io var Q) (λ x _ → refl) p2
... | refl with ~ p1 ! p2
... | ()

eq1617C2 : ∀ {X} (P12 : Λ (↑ X)) (Q : Λ X) → Q ≡ I → P12 [ Q ]ₒ ≡ abs (app (app (var o) P12) (Λ→ i Q)) → bind (io var Q) (Λ→ i Q) ≡ Q → ⊥
eq1617C2 P12 .I refl p19 refl with CCGen P12 (abs (var o)) (io var I) (λ x _ → refl) p19
eq1617C2 .(var o) .I refl () refl | refl


CCGen2 : ∀ {X} (P12 Q : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → bind f P12 ≡ abs (app (app (abs (var o)) P12) Q) → P12 ≡ var o
CCGen2 (var (i x)) Q f fn p with fn x (transp (λ t → x ∈ t) (~ p) (down (left (right (abs (var o)) here) Q)))
... | q with ~ q ! p
... | ()
CCGen2 (var o) Q f fn p = refl
CCGen2 (abs (var (i x))) Q f fn p with abs≡inv p
CCGen2 (abs (var (i (i x)))) Q f fn p | p1 with f (i x) in p2
... | app t1 t2 with app≡inv p1
... | p3 , p4 = exfalso (x∉Λ→i t1 x (λ q → appVar _ _ _ (~ p2 ! fn x (transp (λ t → x ∈ t) (~ p2) (left q t2)))) (transp (λ t → (i x) ∈ t) (~ p3) (right (abs (var o)) (down here))))
CCGen2 (abs (var (i o))) Q f fn p | p1 = exfalso (o∉Λ→i (f o) (transp (λ t → o ∈ t) (~ p1) (left (right (abs (var o)) (down here)) Q)))
CCGen2 (abs (app (var x) P13)) Q f fn p with app≡inv (abs≡inv p)
CCGen2 (abs (app (var (i (i x))) P13)) Q f fn p | p1 , p2 with f (i x) in p5
... | app t1 t2 with app≡inv p1
... | p3 , p4 = exfalso (x∉Λ→i t2 x (λ q → appVar _ _ _ (~ p5 ! fn x (transp (λ t → x ∈ t) (~ p5) (right t1 q)))) (transp (λ t → (i x) ∈ t) (~ p4) (down (left here P13))))
CCGen2 (abs (app (var (i o)) P13)) Q f fn p | p1 , p2 = exfalso (o∉Λ→i (f o) (transp (λ t → o ∈ t) (~ p1) (right (abs (var o)) (down (left here P13)))))
CCGen2 (abs (app (app (var (i (i y))) P14) P13)) Q f fn p with app≡inv (abs≡inv p)
... | p1 , p2 with app≡inv p1
... | p3 , p4 = {! fn y   !}
-- This is P12[x] = \y.xP12[y]X where X is I or x or y
-- This leads to the cycle: IP12[I]I → P12[I] → IP12[I]I
CCGen2 (abs (app (app (var (i o)) P14) P13)) Q f fn p with app≡inv (abs≡inv p)
... | p1 , p2 with app≡inv p1
... | p3 , p4 = {!   !}
CCGen2 (abs (app (app (var o) P14) P13)) Q f fn p with app≡inv (abs≡inv p)
... | p1 , p2 with app≡inv p1
... | () , p4
CCGen2 (abs (app (app (abs (var (i (i x)))) P13) P12)) Q f fn p with app≡inv (abs≡inv p)
... | p1 , p2 with app≡inv p1
... | p3 , p4 with abs≡inv p3
... | p5 = exfalso (o∉Λ→i (Λ→ i (f x)) (transp (λ t → o ∈ t) (~ p5) here))
CCGen2 (abs (app (app (abs (var o)) P13) P12)) Q f fn p with app≡inv (abs≡inv p)
... | p1 , p2 with app≡inv p1
... | p3 , p4 with CCGen2 P13 P12 (lift f) (λ {(i x) → λ q → ext (Λ→ i) (fn x (occInj i iInj x (f (i x)) q))
                                            ; o → λ q → exfalso (o∉Λ→i (f o) q)}) p4
CCGen2 (abs (app (app (abs (var o)) .(var o)) P12)) Q f fn p | p1 , p2 | p3 , () | refl

-- Case 3:
-- P12[Q] = \x.IP12[x]x
eq1617C3 : ∀ {X} (P12 : Λ (↑ X)) (Q : Λ X) → P12 [ Q ]ₒ ≡ abs (app (app (abs (var o)) P12) (var o)) → pure (app (app (abs (var o)) (abs (app (app (abs (var o)) P12) (var o)))) Q) → ⊥
eq1617C3 P12 Q p1 p2 with CCGen2 P12 (var o) (io var Q) (λ x _ → refl) p1
... | refl with p2 (contr (app (abs (app (app (abs (var o)) (var o)) (var o))) Q) (appL→ (redex (var o) (abs (app (app (abs (var o)) (var o)) (var o)))))) 
                   (contr (app (app I (abs (app (var o) (var o)))) Q) (appL→ (appR→ (abs→ (appL→ (redex (var o) (var o)))))))
... | ()

-- Case 4:
-- P12[Q] = \x.IP12[x]Q
eq1617C4 : ∀ {X} (P12 : Λ (↑ X)) (Q : Λ X) → P12 [ Q ]ₒ ≡ abs (app (app (abs (var o)) P12) (Λ→ i Q)) → pure (app (app (abs (var o)) (abs (app (app (abs (var o)) P12) (Λ→ i Q)))) Q) → ⊥
eq1617C4 P12 Q p1 p2 with CCGen2 P12 (Λ→ i Q) (io var Q) (λ x _ → refl) p1
... | refl with p2 (contr (app (abs (app (app I (var o)) (Λ→ i Q))) Q) (appL→ (redex (var o) (abs (app (app (abs (var o)) (var o)) (Λ→ i Q)))))) 
                   (contr (app (app I (abs (app (var o) (Λ→ i Q)))) Q) (appL→ (appR→ (abs→ (appL→ (redex (var o) (var o)))))))
... | ()

eq1617 : ∀ {X} (P11 P12 P2 : Λ (↑ X)) (Q : Λ X) → P11 [ Q ]ₒ ≡ I → P12 [ Q ]ₒ ≡ abs (app (app P11 P12) P2) → P2 [ Q ]ₒ ≡ Q → ¬ (pure (app (app (abs (var o)) (abs (app (app P11 P12) P2))) Q))
-- These are cases 1 and 2 on page 17
eq1617 (var o) P12 P2 Q p1 p2 p3 np = case (λ {refl → eq1617C1 P12 Q p1 p2}) (λ {refl → eq1617C2 P12 Q p1 p2 p3}) (lercherEq3 P2 Q p3)
eq1617 (abs (var (i o))) P12 P2 Q p1 p2 p3 np with abs≡inv p1
... | p4 = (o∉Λ→i Q) (var∈≡ (Λ→ i Q) o p4)
-- These are cases 3 and 4 on page 18
eq1617 (abs (var o)) P12 P2 Q p1 p2 p3 np = case (λ {refl → eq1617C3 P12 Q p2 np}) (λ {refl → eq1617C4 P12 Q p2 np}) (lercherEq3 P2 Q p3)

eq9Helper : ∀ {X} (P : Λ (↑ (↑ X))) (Q1 Q2 : Λ X) → bind (lift (io var (app Q1 Q2))) P ≡ var o → P ≡ var o 
eq9Helper (var (i (i x))) Q1 Q2 ()
eq9Helper (var (i o)) Q1 Q2 ()
eq9Helper (var o) Q1 Q2 p = refl

impureSolution1 : ∀ {X : Set} (M : Λ X) {N : Λ X} → M ⟶ N → ¬ (pure (app M M))
impureSolution1 M {N} r np with np (contr (app M N) (appR→ r)) (contr (app N M) (appL→ r))
... | ()

eq9 : ∀ {X} (P : Λ (↑ X)) (Q : Λ X) → P [ Q ]ₒ ≡ app (app I (abs P)) Q → ¬ (pure (app (app I (abs P)) Q))
eq9 (var (i x)) Q () np
eq9 (var o) Q () np
eq9 (app (var o) P2) Q e np with app≡inv e
-- Not Pure Reduction here... P16
... | (e1 , e2) = case (λ {refl → impureSolution1 Q (transp (λ t → t ⟶ (abs (app (var o) (var o)))) (~ e1) (redex (var o) (abs (app (var o) (var o))))) (pure≡ (~ e) np)}) 
                       (λ {refl → len≡≠ _ _ e1 (λ q → ¬S4 (~ len→ i Q) q)}) (lercherEq3 P2 Q e2)
eq9 (app (app P1 P3) P2) Q e np with app≡inv e
... | e1 , e2 with app≡inv e1
... | (e3 , e4) = eq1617 P1 P3 P2 Q e3 e4 e2 np

PA1 : ∀ {X} (P : Λ (↑ X)) (Q t1 t2 : Λ X) → app (app I (abs P)) Q ⟶ t1 → t1 ≡ app (abs P) Q → app (abs P) Q ⟶ t2 → t2 ≡ app (app I (abs P)) Q  → ¬ (pure t2)
PA1 P Q .(app _ Q) .(P [ Q ]ₒ) (appL→ r1) p1 (redex .P .Q) p2 np = eq9 P Q p2 (transp (λ t → (pure t)) p2 np)
PA1 P Q .(app _ Q) .(app (abs _) Q) (appL→ r1) p1 (appL→ (abs→ r2)) p2 np with app≡inv p2
... | ()
                     