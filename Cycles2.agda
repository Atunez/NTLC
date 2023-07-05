
{-# OPTIONS --allow-unsolved-metas #-}

module Cycles2 where

open import Lambda public
open import Cycles public
open import Length public

I : ∀ {X} → Λ X
I = abs (var o)

bind-oo : ∀ {X Y} (f : X → Λ Y) (M : Λ X) {x} {y} → (∀ z → y ∈ f z → z ≡ x) → y ∈ (M [ f ]) → x ∈ M
bind-oo f (var v) {x} {y} h occ with h v occ
... | refl = here
bind-oo f (app M1 M2) h (left occ .(bind f M2)) = left (bind-oo f M1 h occ) M2
bind-oo f (app M1 M2) h (right .(bind f M1) occ) = right M1 (bind-oo f M2 h occ)
bind-oo f (abs M0) h (down occ) = down (bind-oo (lift f) M0 g occ)
  where g = λ {  o () ; (i x) oc → ext i (h x (occInj i iInj _ (f x) oc) ) }

bind-o : ∀ {X Y} (f : X → Λ Y) (M : Λ (↑ X)) → o ∈ bind (lift f) M → o ∈ M
bind-o f M occ = bind-oo (lift f) M g occ
  where g = λ { o oc → refl ; (i x) oc → exfalso (o∉Λ→i (f x) oc ) }

CCGenG : ∀ {X} (P12 P22 Q : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → o ∈ P12 → bind f P12 ≡ abs (app (app P22 P12) Q) → P12 ≡ var o
CCGenG (var (i x)) P22 Q f fn occ p with fn x (transp (λ t → x ∈ t) (~ p) (down (left (right P22 here) Q)))
... | q with ~ q ! p
... | ()
CCGenG (var o) P22 Q f fn occ p = refl
CCGenG (abs (var (i .o))) P22 Q f fn (down here) p with abs≡inv p 
... | m = exfalso (o∉Λ→i (f o) (transp (λ z → o ∈ z) (~ m) (left (right P22 (down here)) Q)))
CCGenG (abs (app (var (i x)) P13)) P22 Q f fn occ p with app≡inv (abs≡inv p)
CCGenG (abs (app (var (i .o)) P13)) P22 Q f fn (down (left here .P13)) p | p1 , p2 = exfalso (o∉Λ→i (f o) (transp (λ z → o ∈ z) (~ p1) (right P22 (down (left here P13)))))
CCGenG (abs (app (var (i (i x))) P13)) P22 Q f fn (down (right .(var (i (i x))) occ)) p | p1 , p2 = exfalso (o∉Λ→i (f (i x)) (transp (λ z → o ∈ z) (~ p1) (right P22 (down (right (var (i (i x))) occ)))))
CCGenG (abs (app (var (i o)) P13)) P22 Q f fn (down (right .(var (i o)) occ)) p | p1 , p2 = exfalso (o∉Λ→i (f o) (transp (λ z → o ∈ z) (~ p1) (right P22 (down (right (var (i o)) occ)))))
CCGenG (abs (app (app P12 P14) P13)) P22 Q f fn (down occ) p with app≡inv (abs≡inv p)
... | p1 , p2 with app≡inv p1
... | p3 , p4 with CCGenG P14 P12 P13 (lift f) (λ {(i x) → λ q → ext (Λ→ i) (fn x (occInj i iInj x (f (i x)) q))
                                            ; o → λ q → exfalso (o∉Λ→i (f o) q)}) (bind-o f P14 (transp (λ z → o ∈ z) (~ p4) (down occ))) p4
CCGenG (abs (app (app P12 .(var o)) P13)) P22 Q f fn occ p | p1 , p2 | p3 , () | refl

CCGenGNoO : ∀ {X} (P12 P22 : Λ (↑ X)) (Q : Λ X) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → o ∉ P12 → P12 [ Q ]ₒ ≡ abs (app (app P22 P12) (Λ→ i Q)) → ⊥
CCGenGNoO P12 P22 Q f fn nocc p = 
   let noSub = occurs-map _ _ _ p nocc
       eqLen = len→ (↑→ i) P12
       P12P22 = ++≤R (len (Λ→ (↑→ i) P22)) (len (Λ→ (↑→ i) P12))
       StartingEq = (~ eqLen) ≡≤ P12P22
   in len≡≠ _ _ noSub λ q → ¬S3≤ (++≤LN _ StartingEq) q

CCGenGN : ∀ {X} (P12 P22 P32 : Λ (↑ X)) (Q : Λ X) → P12 [ Q ]ₒ ≡ abs (app (app P22 P12) P32) → P12 ≡ var o
CCGenGN P12 P22 P32 Q p with decTop P12
... | inl yes = yes
... | inr no = 
   let ifNoO = occurs-map P12 _ Q p λ q → no (CCGenG P12 P22 P32 (io var Q) (λ x _ → refl) q p)
       eqLen = len→ (↑→ i) P12
       P12P22 = ++≤R (len (Λ→ (↑→ i) P22)) (len (Λ→ (↑→ i) P12))
       StartingEq = (~ eqLen) ≡≤ P12P22
   in exfalso (len≡≠ _ _ ifNoO (λ q → ¬S3≤ (++≤LN _ StartingEq) q))

eq1617C1 : ∀ {X} (P12 : Λ (↑ X)) (Q : Λ X) → Q ≡ I → P12 [ Q ]ₒ ≡ abs (app (app (var o) P12) (var o)) → ⊥
eq1617C1 P12 Q p1 p2 with CCGenGN P12 (var o) (var o) Q p2
... | refl with ~ p1 ! p2
... | ()

eq1617C2 : ∀ {X} (P12 : Λ (↑ X)) (Q : Λ X) → Q ≡ I → P12 [ Q ]ₒ ≡ abs (app (app (var o) P12) (Λ→ i Q)) → bind (io var Q) (Λ→ i Q) ≡ Q → ⊥
eq1617C2 P12 .I refl p19 refl with CCGenGN P12 (var o) (Λ→ i I) I p19
eq1617C2 .(var o) .I refl () refl | refl


-- Case 3:
-- P12[Q] = \x.IP12[x]x
eq1617C3 : ∀ {X} (P12 : Λ (↑ X)) (Q : Λ X) → P12 [ Q ]ₒ ≡ abs (app (app (abs (var o)) P12) (var o)) → pure (app (app (abs (var o)) (abs (app (app (abs (var o)) P12) (var o)))) Q) → ⊥
eq1617C3 P12 Q p1 p2 with CCGenGN P12 (abs (var o)) (var o) Q p1  
... | refl with p2 (contr (app (abs (app (app (abs (var o)) (var o)) (var o))) Q) (appL→ (redex (var o) (abs (app (app (abs (var o)) (var o)) (var o)))))) 
                   (contr (app (app I (abs (app (var o) (var o)))) Q) (appL→ (appR→ (abs→ (appL→ (redex (var o) (var o)))))))
... | ()

-- Case 4:
-- P12[Q] = \x.IP12[x]Q
eq1617C4 : ∀ {X} (P12 : Λ (↑ X)) (Q : Λ X) → P12 [ Q ]ₒ ≡ abs (app (app (abs (var o)) P12) (Λ→ i Q)) → pure (app (app (abs (var o)) (abs (app (app (abs (var o)) P12) (Λ→ i Q)))) Q) → ⊥
eq1617C4 P12 Q p1 p2 with CCGenGN P12 (abs (var o)) (Λ→ i Q) Q p1  
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
... | (e1 , e2) = case (λ {refl → impureSolution1 Q (transp (λ t → t ⟶ (abs (app (var o) (var o)))) (~ e1) (redex (var o) (abs (app (var o) (var o))))) (pure≡ (~ e) np)}) 
                       (λ {refl → len≡≠ _ _ e1 (λ q → ¬S4 (~ len→ i Q) q)}) (lercherEq3 P2 Q e2)
eq9 (app (app P1 P3) P2) Q e np with app≡inv e
... | e1 , e2 with app≡inv e1
... | (e3 , e4) = eq1617 P1 P3 P2 Q e3 e4 e2 np

PA1 : ∀ {X} (P : Λ (↑ X)) (Q t1 t2 : Λ X) → app (app I (abs P)) Q ⟶ t1 → t1 ≡ app (abs P) Q → app (abs P) Q ⟶ t2 → t2 ≡ app (app I (abs P)) Q  → ¬ (pure t2)
PA1 P Q .(app _ Q) .(P [ Q ]ₒ) (appL→ r1) p1 (redex .P .Q) p2 np = eq9 P Q p2 (transp (λ t → (pure t)) p2 np)
PA1 P Q .(app _ Q) .(app (abs _) Q) (appL→ r1) p1 (appL→ (abs→ r2)) p2 np with app≡inv p2
... | ()
                           