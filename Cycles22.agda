module Cycles22 where

open import Lambda public
open import Cycles public
open import Length public
open import Cycles2 public

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

dec : Set → Set
dec A = ∀ (x y : A) → x ≡ y ⊔ ¬ (x ≡ y)

dec⊥ : dec ⊥
dec⊥ () y

dec⊤ : dec ⊤
dec⊤ tt tt = inl refl

dec↑ : ∀ {X} → dec X → dec (↑ X)
dec↑ p (i x) (i y) with p x y
...                   | inl q = inl (ext i q)
...                   | inr q = inr (λ {refl → q refl } )
dec↑ p o (i y) = inr (λ {()})
dec↑ p (i x) o = inr (λ {()} )
dec↑ p o o = inl refl

decAt : ∀ (X : Set) → X → Set
decAt X x = ∀ y → x ≡ y ⊔ ¬ (x ≡ y)

decAto : ∀ {X} → decAt (↑ X) o
decAto (i x) = inr (λ {()})
decAto o = inl refl

decAti : ∀ {X} x → decAt X x → decAt (↑ X) (i x)
decAti x p (i y) with p y
...                 | inl e = inl (ext i e)
...                 | inr n = inr λ {(refl) → n refl }
decAti x p o = inr (λ {()})

decΛ : ∀ {X} {x} → (decAt X x) → ∀ t → x ∈ t ⊔ ¬ (x ∈ t)
decΛ {X} {x} d (var y) with d y
...                       | inl refl = inl here
...                       | inr n = inr (λ {here → n refl })
decΛ {X} {x} d (app t₁ t₂) with (decΛ d t₁ , decΛ d t₂)
...                           | (inl p , inl q) = inl (left p t₂)
...                           | (inl p , inr q) = inl (left p t₂)
...                           | (inr p , inl q) = inl (right t₁ q)
...                           | (inr p , inr q) = inr ((λ { (left s r) → p s ; (right r s) → q s }))
decΛ {X} {x} d (abs t) with decΛ {↑ X} {i x} (decAti x d) t
...                       | inl yes = inl (down yes)
...                       | inr no  = inr (λ {(down p) → no p } )

-- I : ∀ {X} → Λ X
-- I = abs (var o)

appVar : ∀ {X} (P1 P2 : Λ X) x → app P1 P2 ≡ var x → ⊥
appVar P1 P2 x () 

absApp : ∀ {X} (P1 P2 : Λ X) P3 → abs P3 ≡ app P1 P2 → ⊥
absApp P1 P2 P3 ()

eq21Helper : ∀ {X} (M : Λ (↑ (↑ X))) (N : Λ X) → bind (io var (Λ→ i N)) M ≡ var o → M ≡ var (i o)
eq21Helper (var (i o)) N p = refl
eq21Helper (var o) N p = exfalso ((o∉Λ→i N) (var∈≡ (Λ→ i N) o p))

NoBindOnNoO : ∀ {X} (M : Λ (↑ X)) (Q P : Λ X)  → ¬ (o ∈ M) → M [ Q ]ₒ ≡ P → M ≡ Λ→ i P
NoBindOnNoO M Q P nocc e = occurs-map M P Q e nocc

NBOWLemma : ∀ {X} (P Q : Λ X) (f : ↑ X → Λ X) (g : X → ↑ X) → (∀ x → x ∈ P → f (g x) ≡ var x) → (Λ→ g P) [ f ] ≡ P 
NBOWLemma (var x) Q f g fn = fn x here
NBOWLemma (app P P₁) Q f g fn = app≡ (NBOWLemma P Q f g (λ x z → fn x (left z P₁))) (NBOWLemma P₁ Q f g (λ x z → fn x (right P z)))
NBOWLemma (abs P) Q f g fn = abs≡ (NBOWLemma P (Λ→ i Q) (lift f) (↑→ g) λ {(i x) → λ q → ext (Λ→ i) (fn x (down q))
                                                                         ; o → λ _ → refl})

NoBindOnWeaking : ∀ {X} (P Q : Λ X) → (Λ→ i P) [ Q ]ₒ ≡ P
NoBindOnWeaking P Q = NBOWLemma P Q (io var Q) i (λ x _ → refl)

BindWithTerms : ∀ {X} (L : Λ (↑ (↑ X))) (P : Λ X) (Q : Λ X) → (L [ Λ→i P ]ₒ) [ Q ]ₒ ≡ L 
BindWithTerms (var (i (i x))) P Q = refl
BindWithTerms (var (i o)) P Q = refl
BindWithTerms (var o) P Q = NoBindOnWeaking P Q
BindWithTerms (app L L₁) P Q = {!   !}
BindWithTerms (abs L) P Q = {!   !} 

eq24Lemmafg : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) (g : ↑ (↑ X) → Λ X) → 
              (∀ x → x ∈ g (i (i x)) → g (i (i x)) ≡ var x) → g o ≡ P
              → L [ g ] ≡ P → o ∈ L → L ≡ var o
eq24Lemmafg L P Q g gn go p occ = {!  bind-rec (L [ g ]) f {x = o}  !}

-- decTopIo : 

-- eq24Lemma3 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) (f : ↑ (↑ X) → Λ X) → f o ≡ P → f (i o) ≡ Q → f (i (i x)) ≡ var x 
eq24Lemma3 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io (io var P) Q) L ≡ P → (i o) ∈ L → L ≡ var (i o)
eq24Lemma3 L P Q p occ = bind-rec L (io (io var P) Q) occ p

decTopIo : ∀ {X} (A : Λ (↑ (↑ X))) → A ≡ var (i o) ⊔ ¬ (A ≡ var (i o))
decTopIo A = {!   !}

eq24Lemma33 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (io var (Λ→ i P)) L) ≡ P → L ≡ var (i o) ⊔ (i o) ∉ L
eq24Lemma33 L P Q p with decTopIo L
... | inl yes = inl yes
... | inr no = 
  let noSub = occurs-map {!   !} {!   !} {!   !} {!   !} {!   !}
  in {!   !}

-- This may be improperly stated...
-- If L contains o, then it must be var o. 
  -- If it contains more than 1 o, then they cant be equal
  -- If o isn't at the top level, then LHS can't equal to just P...
-- If it doesn't, then we can do direct substitution.
eq24Lemma : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (io var (Λ→ i P)) L) ≡ P → L ≡ var o ⊔ o ∉ L
eq24Lemma L P Q p = {! bind-rec L (io var )  !}
-- eq24Lemma (app L L₁) P Q p = {!   !}
-- eq24Lemma (abs L) (abs P) Q p = {!    !}



eq28 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io (io var P) Q) L ≡ abs (abs (app (app L (var (i o))) (var o)))
    → pure (app (app (abs (abs (app (app L (var (i o))) (var o)))) P) Q) → L ≡ var o
--  bind (io var Q) (bind (io var (Λ→ i P)) L) ≡ abs (abs (app (app L (var o)) (var (i o)))) 
--   → pure (app (app (abs (abs (app (app L (var o)) (var (i o))))) P) Q) → ⊥ 
eq28 (var (i o)) P Q e p = {!   !} -- Not Pure
eq28 (var o) P Q e p = refl -- Real Answer
eq28 (abs L) P Q e p = {!   !} -- Lercher2 Situation?

-- eq24Lemma2 (abs (var (i (i o)))) P (abs (app Q (var (i x)))) () p
-- eq24Lemma2 (abs (var (i (i o)))) P (abs (app Q (var o))) () p 
-- eq24Lemma2 (abs (var (i o))) (abs (var (i x))) Q () p
-- eq24Lemma2 (abs (var (i o))) (abs (var o)) Q () p
-- eq24Lemma2 (abs (var (i o))) (abs (app P (var (i x)))) Q () p
-- eq24Lemma2 (abs (var (i o))) (abs (app P (var o))) Q () p
-- eq24Lemma2 (abs (abs (var (i (i (i o)))))) P (app Q (app Q₁ Q₂)) () p
-- eq24Lemma2 (abs (abs (var (i (i (i o)))))) P (app Q (abs Q₁)) () p
-- eq24Lemma2 (abs (abs (var (i (i o))))) (app P (app P₁ P₂)) Q () p
-- eq24Lemma2 (abs (abs (var (i (i o))))) (app P (abs P₁)) Q () p
-- eq24Lemma2 (abs (abs (app (var x) L₁))) P Q e p = {!   !}
-- eq24Lemma2 (abs (abs (app (app L (var x)) (var x₁)))) P Q e p = {!   !}

-- eq24Lemma3 : ∀ {X} (L2 : Λ (↑ (↑ X))) (Q : Λ X) → ¬ (o ∈ L2) → L2 [ Λ→ i Q ]ₒ ≡ abs (abs (app (app (var o) L2) (var (i o)))) → L2 ≡ var (i o)
-- eq24Lemma3 L2 Q p = ?


eq24 : ∀ {X} (L12 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (io var (Λ→ i P)) L12) ≡ app (abs (abs (app L12 (var (i o))))) P → pure (app (app (abs (abs (app L12 (var (i o))))) P) Q) → ⊥
eq24 (var (i o)) P .(app (abs (abs (app (var (i o)) (var (i o))))) P) refl p with p (contr _ (appL→ (redex _ P))) (contr _ (appR→ (redex _ P)))
... | ()
eq24 (var o) P Q e p = len≡≠ _ _ t λ q → ¬S4 refl q where t = ~ NoBindOnWeaking P Q ! e
eq24 (app L1 L2) P Q e p with app≡inv e
-- e2 = L122[Q, P] = P
-- e1 = L121[Q, P] = \x\y.L121[y, x]L122[y, x]y
... | (e1 , e2) with eq24Lemma L2 P Q e2
... | inl refl = {!   !} -- eq28 L1 P Q e1 p
eq24 (app (var (i o)) L2) P Q e p | e1 , e2 | inr x = {!   !} -- Real Solution 
eq24 (app (var o) L2) P Q e p | e1 , e2 | inr x with (~ NoBindOnWeaking P Q) ! e1 
... | refl = {!    !} -- Impossible Case, but Not sure how to prove it.
eq24 (app (abs L1) L2) P Q e p | e1 , e2 | inr x with p (contr ((app (app (abs (abs (app (L1 [ L2 ]ₒ) (var (i o))))) P) Q)) (appL→ (appL→ (abs→ (abs→ (appL→ (redex L1 L2))))))) 
                                                        (contr _ (appL→ (redex (abs (app (app (abs L1) L2) (var (i o)))) P)))
... | ()

eq21L3L : ∀ {X} (L3 : Λ (↑ (↑ X))) (Q : Λ (↑ X)) (f : ↑ (↑ X) → Λ (↑ X)) (x : ↑ X) → f (i x) ≡ var x → (i x) ∈ L3 → L3 [ f ] ≡ Q → x ∈ Q
eq21L3L (var (i y)) Q f .y e here p = transp (λ t → y ∈ t) (~ e ! p) here
eq21L3L (app L3 L4) (app Q Q₁) f x e (left occ .L4) p = left (eq21L3L L3 Q f x e occ (_×_.fst (app≡inv p))) Q₁ 
eq21L3L (app L3 L4) (app Q Q₁) f x e (right .L3 occ) p = right Q (eq21L3L L4 Q₁ f x e occ (_×_.snd (app≡inv p)))
eq21L3L (abs L3) (abs Q) f x e (down occ) p = down (eq21L3L L3 Q (lift f) (i x) (ext (Λ→i) e) occ (abs≡inv p))

-- If L3[Q, P] = Q, then either L3 is y or L3[y, x] = L3[x], ie y ∉ L3
eq21L3 : ∀ {X} (L3 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (io var (Λ→ i P)) L3) ≡ Q → L3 ≡ var (i o) ⊔ ¬ ((i o) ∈ L3) 
eq21L3 L3 P Q p with lercherEq3 (L3 [ Λ→ i P ]ₒ) _ p
eq21L3 (var (i o)) P Q p | inl x = inl refl
eq21L3 (var o) P Q p | inl x = exfalso (o∉Λ→i P (transp (λ t → o ∈ t) (~ x) here))
... | inr x = inr λ q → o∉Λ→i Q (eq21L3L L3 (Λ→ i Q) (io var (Λ→ i P)) o refl q x)
-- eq21L3 (var (i (i x))) P Q p = inr λ ()
-- eq21L3 (var (i o)) P Q p = inl refl
-- eq21L3 (var o) P Q p = inr λ ()
-- eq21L3 (app L3 L4) P Q p = inr λ {(left q .L4) → {!   !}
--                                 ; (right .L3 q) → {!   !}}
-- eq21L3 (abs L3) P (abs Q) p with abs≡inv p
-- ... | p2 = inr λ {(down q) → {!   !}}

eq38 : ∀ {X} (L2 : Λ (↑ (↑ X))) (P : Λ X) → P ≡ abs (abs (app (app (var (i o)) L2) (var o))) → bind (io var P) (bind (io var (Λ→ i P)) L2) ≡ P → ⊥
eq38 L2 P p1 p2 with lercherEq3 (L2 [ Λ→ i P ]ₒ) P p2
-- second goal of the three is impossible, rest are real goals.
... | inr x = case (λ {refl → {!   !}}) (λ {refl → {!   !}}) (lercherEq3 L2 _ x)
... | inl x with eq21Helper L2 _ x 
... | refl = {!   !}

Λ→iPQ : ∀ {X} (P Q : Λ X) → Λ→ i P ≡ Λ→ i Q → P ≡ Q
Λ→iPQ P Q p = Λ→Inj i iInj p

-- This is bad, remove later
bindExtTerm : ∀ {X} (P : Λ (↑ X)) (Q Q2 M : Λ X) → Q ≡ Q2 → P [ Q ]ₒ ≡ M → P [ Q2 ]ₒ ≡ M
bindExtTerm P Q Q2 M refl p = p

bindExtTerm2 : ∀ {X} (P : Λ (↑ X)) (Q Q2 M : Λ X) → Q ≡ Q2 → P [ io var Q ] ≡ M → P [ io var Q2 ] ≡ M
bindExtTerm2 P Q Q2 M refl p = p

eq32 : ∀ {X} (L12 L3 : Λ (↑ (↑ X))) (P Q : Λ X) → dec X → ¬ ((i o) ∈ L3) → L3 [ Λ→ i P ]ₒ ≡ Λ→ i Q → L12 [ Λ→ i P ]ₒ [ Q ]ₒ ≡ app (abs (abs (app L12 L3))) P → pure (app (app (abs (abs (app L12 L3))) P) Q) → ⊥
eq32 (var (i o)) L3 P .(app (abs (abs (app (var (i o)) L3))) P) d nocc e1 refl p with p (contr _ (appR→ (redex (abs (app (var (i o)) L3)) P))) 
                                                                                      (contr _ (appL→ (redex (abs (app (var (i o)) L3)) P)))
... | ()
eq32 (var o) L3 P Q d nocc e1 e2 p = len≡≠ _ _ t λ q → ¬S4≤ (++≤R (len L3) (len P)) q where t = ~ NoBindOnWeaking P Q ! e2 
eq32 (app (var (i o)) L2) L3 P Q d nocc e1 e2 p with decΛ ((dec↑ (dec↑ d)) o) L3
... | inl x = case (λ {refl → let PQ = Λ→iPQ P Q e1 in eq38 L2 P (PQ ! _×_.fst epp) (bindExtTerm (L2 [ Λ→ i P ]ₒ) _ _ _ (~ PQ) (_×_.snd epp))}) 
                    -- case 3 in page 23
                    -- Cases in order here: y ∈ L2[y, x] -- Should yield an infinite term 
                    -- L2[y, x] ≡ x and L2[y, x] = P
                    (λ {q → case {!   !} (case {!   !} {!   !} (decTop L2)) (decΛ ((dec↑ (dec↑ d)) (i o)) L2)}) (decTop L3) where epp = app≡inv e2
... | inr x with app≡inv e2
... | (e21 , e22) with NoBindOnNoO L3 _ _ x e1
... | refl = len≡≠ _ _ e21 λ q → ¬S4≤ (zero≤ ≤+≤ (≤refl (len Q) ≤≡ (~ len→ i Q ! ~ len→ i (Λ→ i Q)))) q
eq32 (app (var o) L2) L3 P Q d nocc e1 e2 p = {!   !} -- "Simple" to Finish
eq32 (app (abs L1) L2) L3 P Q d nocc e1 e2 p with p (contr _ (appL→ (redex (abs (app (app (abs L1) L2) L3)) P))) 
                                                  (contr _ (appL→ (appL→ (abs→ (abs→ (appL→ (redex L1 L2)))))))
... | ()

eq21 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → dec X → (L [ Λ→i P ]ₒ) [ Q ]ₒ ≡ app (app (abs (abs L)) P) Q → pure (app (app (abs (abs L)) P) Q) → ⊥
-- L is a free var
eq21 (var (i (i x))) P Q d () p
-- L is var y
eq21 (var (i o)) P Q d () p
-- L is var x
eq21 (var o) P Q d e p = -- Impossible, RHS of e can't contain O since LHS doesn't
  let noBind = len∉bind (Λ→ i P) Q (io var Q) o (o∉Λ→i P) λ {(i x) → λ _ → inr refl
                                                              ; o → λ _ → inl (refl , refl)} 
      
  in len≡≠ _ _ e (λ q → ¬S< (~ (len→  i P) ! ~ noBind ! q) (<Prf _ _)) where
    <Prf : ∀ (m n : Nat) → m < S (S (S (S (m ++ n))))
    <Prf O n = O< (S (S (S n)))
    <Prf (S m) n = S< m (S (S (S (S (m ++ n))))) (<Prf m n)
-- L is L12[y, x]L3[y, x]
eq21 (app L12 L3) P Q d e p with app≡inv e
-- e1 = L12[Q, P] = (\x\y.L12[y, x]L3[y, x])P
-- e2 = L3[Q, P] = Q
... | (e1 , e2) with eq21L3 L3 P Q e2 
... | inl refl = eq24 L12 P Q e1 p 
-- This is ugly...
... | inr x = eq32 L12 L3 P Q d x (NoBindOnNoO (bind (io var (Λ→ i P)) L3) Q Q (∉[∈] L3 x (io var (Λ→ i P)) (λ {(i (i x)) → λ _ ()
      ; (i o) → λ z _ → x z; o → λ p q → o∉Λ→i P q})) e2) e1 p

-- If you walk along the following path:
-- M≡(\x.\y.L[x,y])PQ → (\y.L[P,y])Q → L[P,Q]≡M
-- Then, Q ≡ \xy.yxy OR P ≡ Q × (P ≡ \xy.yxx OR \xy.yyx) OR Q ≡ \xy.y?y where ? doesn't contain b as the LHS of App
PA2 : ∀ (L : Λ (↑ (↑ ⊥))) (P Q t1 t2 : Λ ⊥) → app (app (abs (abs L)) P) Q ⟶ t1 → t1 ≡ app ((abs L) [ P ]ₒ) Q → app ((abs L) [ P ]ₒ) Q ⟶ t2 → t2 ≡ L [ Λ→i P ]ₒ [ Q ]ₒ → ⊥
PA2 L P Q t1 t2 r1 p1 r2 p2 = {!   !}
              