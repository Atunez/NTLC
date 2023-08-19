module BicyclesCase2 where

open import Lambda public
open import Cycles public
open import Length public
open import Decidability public
open import Bicycles public


NBOWLemma : ∀ {X} (P Q : Λ X) (f : ↑ X → Λ X) (g : X → ↑ X) → (∀ x → x ∈ P → f (g x) ≡ var x) → (Λ→ g P) [ f ] ≡ P
NBOWLemma (var x) Q f g fn = fn x here
NBOWLemma (app P P₁) Q f g fn = app≡ (NBOWLemma P Q f g (λ x z → fn x (left z P₁))) (NBOWLemma P₁ Q f g (λ x z → fn x (right P z)))
NBOWLemma (abs P) Q f g fn = abs≡ (NBOWLemma P (Λ→ i Q) (lift f) (↑→ g) λ {(i x) → λ q → ext (Λ→ i) (fn x (down q))
                                                                         ; o → λ _ → refl})

NoBindOnWeaking : ∀ {X} (P Q : Λ X) → (Λ→ i P) [ Q ]ₒ ≡ P
NoBindOnWeaking P Q = NBOWLemma P Q (io var Q) i (λ x _ → refl)


eqPf :  ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → L [ io (io var P) Q ] ≡ (L [ lift (io var P) ]) [ Q ]ₒ
eqPf L P Q =
    let bind-law-f1 = bind-law (lift (io var P)) (io var Q) L
    in bind-ext (λ {(i (i x)) → refl
                  ; (i o) → ~ NoBindOnWeaking P Q
                  ; o → refl}) L ! bind-law-f1

liftProof : ∀ {X} (f : ↑ (↑ X) → Λ X) → ((x : X) → x ∈ f (i (i x)) → f (i (i x)) ≡ var x) → ((x : ↑ (↑ X)) → x ∈ Λ→i (Λ→i (f x)) → Λ→i (Λ→i (f x)) ≡ var x)
liftProof f fn = (λ {(i (i x)) → λ q → ext (Λ→i ∘ Λ→i) (fn x (occIni _ (occIni _ q)))
                                                ; (i o) → λ q → exfalso (x∉Λ→i (Λ→ i (f (i o))) o (λ q2 → exfalso (o∉Λ→i (f (i o)) q2)) q)
                                                 ; o → λ q → exfalso (o∉Λ→i (Λ→ i (f o)) q)})


-- If L3[Q, P] = Q, then either L3 is y or L3[y, x] = L3[x], ie y ∉ L3
eq21L3 : ∀ {X} (L3 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (lift (io var P)) L3) ≡ Q → L3 ≡ var o ⊔ ¬ (o ∈ L3)
eq21L3 L3 P Q p with lercherEq3 (L3 [ lift (io var P) ]) _ p
eq21L3 (var (i o)) P Q p | inl x = exfalso (o∉Λ→i P (transp (λ t → o ∈ t) (~ x) here)) -- inl refl
eq21L3 (var o) P Q p | inl x = inl refl --  exfalso (o∉Λ→i P (transp (λ t → o ∈ t) (~ x) here))
... | inr x = inr λ q → o∉Λ→i Q (transp (λ z → o ∈ z) x (∈[∈]2 q (lift (io var P)) here)) -- o∉Λ→i Q (eq21L3L L3 (Λ→ i Q) ? o refl q x)

decTopIo : ∀ {X} (A : Λ (↑ (↑ X))) → A ≡ var (i o) ⊔ ¬ (A ≡ var (i o))
decTopIo (var (i (i x))) = inr (λ ())
decTopIo (var (i o)) = inl refl
decTopIo (var o) = inr (λ ())
decTopIo (app A A₁) = inr (λ ())
decTopIo (abs A) = inr (λ ())

eq24L2Lemma :  ∀ {X} (L2 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (bind (io var Q) ∘ (lift (io var P))) L2 ≡ P → (i o) ∈ L2 → L2 ≡ var (i o)
eq24L2Lemma L2 P Q p occ = bind-rec L2  (bind (io var Q) ∘ (lift (io var P))) occ (p !~ NoBindOnWeaking P Q )

eq24L2 : ∀ {X} (L2 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (lift (io var P)) L2) ≡ P → L2 ≡ var (i o) ⊔ ¬ ((i o) ∈ L2)
eq24L2 L2 P Q p with decTopIo L2
... | inl yes = inl yes
... | inr no = inr λ q → no (eq24L2Lemma L2 P Q (bind-law _ _ L2 ! p) q)


bindOWithLift : ∀ {X} (M : Λ (↑ (↑ X))) (f : ↑ X → Λ X) → bind (lift f) M ≡ var o → M ≡ var o
bindOWithLift (var (i (i x))) f p = exfalso (o∉Λ→i (f (i x)) (transp ((λ z → o ∈ z)) (~ p) here))
bindOWithLift (var (i o)) f p = exfalso (o∉Λ→i (f o) (transp ((λ z → o ∈ z)) (~ p) here))
bindOWithLift (var o) f p = refl

lercherEq3Io : ∀ {X} (L : Λ (↑ (↑ X))) (P : Λ X) → L [ lift (io var P) ] ≡ (Λ→ i P) → L ≡ var (i o) ⊔ L ≡ Λ→i (Λ→i P)
lercherEq3Io L P p with decTopIo L
... | inl yes = inl yes
... | inr no = inr (occurs-map-gen2 L P (lift (io var P)) (λ {(i x) → λ _ → here; o → λ q → exfalso (no (bind-rec L _ q p))})
                   (λ {(i x) → λ _ → refl; o → λ q → exfalso (o∉Λ→i P q)}) p (λ q → no (bind-rec L _ q p)) λ q → o∉Λ→i P (transp (λ z → o ∈ z) p (∈[∈]2 q (lift (io var P)) here)))

doubleSubSub : ∀ {X} (L : Λ (↑ (↑ X))) (P1 P2 Q1 Q2 : Λ X) → P1 ≡ P2 → Q1 ≡ Q2 → L [ io (io var P1) Q1 ] ≡ L [ io (io var P2) Q2 ]
doubleSubSub L P1 P2 Q1 Q2 refl refl = refl

doubleSubSub2 : ∀ {X} (L : Λ (↑ (↑ X))) (P1 P2 Q1 Q2 : Λ X) → P1 ≡ P2 → Q1 ≡ Q2 → (L [ lift (io var P1) ]) [ Q1 ]ₒ ≡ (L [ lift (io var P2) ]) [ Q2 ]ₒ
doubleSubSub2 L P1 P2 Q1 Q2 refl refl = refl

CCGen : ∀ {X} (L P Q : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) → (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x) → bind f L ≡ abs (abs (app (app L (var (i o))) (var o))) → L ≡ var o ⊔ L ≡ var (i o)
CCGen (var (i (i x))) P Q f fn p with ~ (fn x (transp (λ z → x ∈ z) (~ p) (down (down (left (left here (var (i o))) (var o)))))) ! p
... | ()
CCGen (var (i o)) P Q f fn p = inr refl
CCGen (var o) P Q f fn p = inl refl
CCGen (abs (var (i (i (i x))))) P Q f fn p with ~ ext (Λ→i) (fn x (occIni _ (transp (λ z → (i x) ∈ z) (~ (abs≡inv p)) (down (left (left (down here) (var (i o))) (var o)))))) ! (abs≡inv p)
... | ()
CCGen (abs (var (i (i o)))) P Q f fn p = exfalso (o∉Λ→i (f (i o)) (transp (λ z → o ∈ z) (~ (abs≡inv p)) (down (left (right (abs (var (i (i o)))) here) (var o)))))
CCGen (abs (var (i o))) P Q f fn p = exfalso (o∉Λ→i (f o) (transp (λ z → o ∈ z) (~ (abs≡inv p)) (down (left (right (abs (var (i o))) here) (var o)))))
CCGen (abs (abs (var (i (i x))))) P Q f fn p = exfalso (o∉Λ→i (Λ→ i (f x)) (transp (λ z → o ∈ z) (~ (abs≡inv (abs≡inv p))) (right (app (abs (abs (var (i (i x))))) (var (i o))) here)))
CCGen (abs (abs (app (var (i (i x))) L₁))) P Q f fn p with app≡inv (abs≡inv (abs≡inv p))
... | p1 , p2 = exfalso (x∉Λ→i (Λ→ i (f x)) o (λ q → o∉Λ→i (f x) q) (transp (λ z → (i o) ∈ z) (~ p1) (right (abs (abs (app (var (i (i x))) L₁))) here)))
CCGen (abs (abs (app (app L (var (i (i x)))) L₁))) P Q f fn p with app≡inv (abs≡inv (abs≡inv p))
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (x∉Λ→i (Λ→ i (f x)) o (λ q → o∉Λ→i (f x) q) (transp (λ z → (i o) ∈ z) (~ p4) here))
CCGen (abs (abs (app (app L L₂) (var (i (i x)))))) P Q f fn p with app≡inv (abs≡inv (abs≡inv p))
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (o∉Λ→i (Λ→i (f x)) (transp (λ z → o ∈ z) (~ p2) here)) --  exfalso (x∉Λ→i (Λ→ i (f x)) o (λ q → o∉Λ→i (f x) q) (transp (λ z → (i o) ∈ z) (~ p2) {!   !}))
CCGen (abs (abs (app (app L L₂@(var (i o))) L₁@(var o)))) P Q f fn p with app≡inv (abs≡inv (abs≡inv p))
... | (p1 , p2) with app≡inv p1
... | (p3 , p4) =
    let c1 = λ {refl → inl (~ p3)}
        c2 = λ {refl → inr (~ p3)}
    in case c1 c2 (CCGen L L L (lift (lift f)) (liftProof f fn) p3)


eq21HelperIo : ∀ {X} (M : Λ (↑ (↑ X))) (N : Λ (↑ X)) → M [ N ]ₒ ≡ var o → M ≡ var (i o) ⊔ N ≡ var o
eq21HelperIo (var (i o)) N p = inl refl
eq21HelperIo (var o) N p = inr p

eq21Helper : ∀ {X} (M : Λ (↑ (↑ X))) (N : Λ X) → bind (io var (Λ→ i N)) M ≡ var o → M ≡ var (i o)
eq21Helper (var (i o)) N p = refl
eq21Helper (var o) N p = exfalso ((o∉Λ→i N) (var∈≡ (Λ→ i N) o p))



liftLemma : ∀ {X} (M : Λ (↑ (↑ X))) (T : Λ X) (f : (↑ (↑ X)) → Λ X) x y → y ∈ f x → M [ f ] ≡ T → x ∈ M → y ∈ T
liftLemma .(var x) T f x y occ1 pf here = occ1 ∈≡ pf
liftLemma .(app _ t) (app T T₁) f x y occ1 pf (left occ2 t) = left (liftLemma _ T f x y occ1 (_×_.fst (app≡inv pf)) occ2) T₁
liftLemma .(app s _) (app T T₁) f x y occ1 pf (right s occ2) = right T (liftLemma _ T₁ f x y occ1 (_×_.snd (app≡inv pf)) occ2)
liftLemma .(abs _) (abs T) f x y occ1 pf (down occ2) = down (liftLemma _ T (lift f) (i x) (i y) (InjOcc i iInj y (f x) occ1) (abs≡inv pf) occ2)

eq40O : ∀ {X} (L3 T : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) (fn : (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x)) → L3 [ f ] ≡ abs (abs (app (app (var o) T) L3)) → o ∈ T ⊔ ((i o) ∈ T ⊔ (L3 ≡ var o ⊔ (L3 ≡ var (i o) ⊔ L3 ≡ abs (var (i o))))) 
eq40O (var (i (i x))) T f fn pf with ~ pf ! fn x (transp (λ z → x ∈ z) (~ pf) (down (down (right (app (var o) T) here))))
... | ()
eq40O (var (i o)) T f fn pf = inr (inr (inr (inl refl)))
eq40O (var o) T f fn pf = inr (inr (inl refl))
eq40O (abs (var (i (i (i x))))) T f fn pf with abs≡inv pf
... | p1 with ~ p1 ! ext Λ→i (fn x (occIni (f (i (i x))) (down (right (app (var o) T) (down here)) ∈≡ (~ p1))))
... | ()
eq40O (abs (var (i (i o)))) T f fn pf = exfalso (o∉Λ→i (f (i o)) (down (right (app (var o) T) (down here)) ∈≡ (~ (abs≡inv pf))))
eq40O (abs (var (i o))) T f fn pf = inr (inr (inr (inr refl)))
eq40O (abs (abs (var (i (i x))))) T f fn pf with abs≡inv (abs≡inv pf)
... | p1 = exfalso (o∉Λ→i (Λ→i (f x)) (left (left here T) (abs (abs (var (i (i x))))) ∈≡ (~ p1)))
eq40O (abs (abs (app (var (i (i x))) L4))) T f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 = exfalso (o∉Λ→i (Λ→i (f x)) (left here T ∈≡ (~ p1)))
eq40O (abs (abs (app (app (var (i (i x))) L5) L4))) T f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (o∉Λ→i (Λ→i (f x)) (here ∈≡ (~ p3)))
eq40O (abs (abs (app (app (var o) L5) L4))) T f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p12 , p2 with app≡inv p12
... | p3 , p4 with eq40O L4 L5 (lift (lift f)) (liftProof f fn) p2
... | inl x = inl (liftLemma L5 T (lift (lift f)) o o here p4 x)
... | inr (inl x) = inr (inl (liftLemma L5 T (lift (lift f)) (i o) (i o) here p4 x))
eq40O (abs (abs (app (app (var o) L5) .(var o)))) T f fn pf | p12 , () | p3 , p4 | inr (inr (inl refl))
eq40O (abs (abs (app (app (var o) L5) .(var (i o))))) T f fn pf | p12 , () | p3 , p4 | inr (inr (inr (inl refl)))
eq40O (abs (abs (app (app (var o) L5) .(abs (var (i o)))))) T f fn pf | p12 , () | p3 , p4 | inr (inr (inr (inr refl)))

eq40lemmaIO : ∀ {X} (L : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) (fn : (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x)) → L [ f ] ≡ abs (abs (app (app (var o) (var (i o))) L)) → L ≡ var (i o) ⊔ (L ≡ var o)
eq40lemmaIO (var (i (i x))) f fn pf with ~ pf ! fn x (transp (λ z → x ∈ z) (~ pf) (down (down (right (app (var o) (var (i o))) here))))
... | ()
eq40lemmaIO (var (i o)) f fn pf = inl refl
eq40lemmaIO (var o) f fn pf = inr refl
eq40lemmaIO (abs (var (i (i (i x))))) f fn pf with abs≡inv pf
... | p1 with ~ p1 ! ext Λ→i (fn x (occIni (f (i (i x))) (down (right (app (var o) (var (i o))) (down here)) ∈≡ (~ p1))))
... | ()
eq40lemmaIO (abs (var (i (i o)))) f fn pf with abs≡inv pf
... | p1 = exfalso (o∉Λ→i (f (i o)) (down (right (app (var o) (var (i o))) (down here)) ∈≡ (~ p1)))
eq40lemmaIO (abs (var (i o))) f fn pf with abs≡inv pf
... | p1 = exfalso (o∉Λ→i (f o) (down (left (right (var o) here) (abs (var (i o)))) ∈≡ (~ p1)))
eq40lemmaIO (abs (abs (var (i (i x))))) f fn pf with abs≡inv (abs≡inv pf)
... | p1 = exfalso (o∉Λ→i (Λ→ i (f x)) (left (left here (var (i o))) (abs (abs (var (i (i x))))) ∈≡ (~ p1)))
eq40lemmaIO (abs (abs (app (var (i (i x))) L₁))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 = exfalso (o∉Λ→i (Λ→ i (f x)) (left here (var (i o)) ∈≡ (~ p1)))
eq40lemmaIO (abs (abs (app (app (var (i (i x))) L₂) L₁))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (o∉Λ→i (Λ→ i (f x)) (here ∈≡ (~ p3)))
eq40lemmaIO (abs (abs (app (app (var o) (var (i (i x)))) L₁))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (x∉Λ→i (Λ→ i (f x)) o (λ q → o∉Λ→i (f x) q) (here ∈≡ (~ p4)))
eq40lemmaIO (abs (abs (app (app (var o) (var (i o))) L))) f fn pf with eq40lemmaIO L (lift (lift f)) (liftProof f fn) ((_×_.snd (app≡inv (abs≡inv (abs≡inv pf))))) 
... | inl x = inl (~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) x)
... | inr x = inr (~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) x) -- 

eqL1 : ∀ {X} (L2 : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) (fn : (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x)) → L2 [ f ] ≡ abs (abs (app (app (var o) L2) (var (i o)))) → L2 ≡ var o ⊔ (L2 ≡ var (i o) ⊔ L2 ≡ abs (var (i o)))
eqL1 (var (i (i x))) f fn pf with ~ pf ! fn x (transp (λ z → x ∈ z) (~ pf) (down (down (left (right (var o) here) (var (i o))))))
... | ()
eqL1 (var (i o)) f fn pf = inr (inl refl)
eqL1 (var o) f fn pf = inl refl
eqL1 (abs (var (i (i (i x))))) f fn pf with abs≡inv pf
... | p1 with ~ p1 ! ext Λ→i (fn x (occIni (f (i (i x))) (down (left (right (var o) (down here)) (var (i o))) ∈≡ (~ p1))))
... | ()
eqL1 (abs (var (i (i o)))) f fn pf = exfalso (o∉Λ→i (f (i o)) (down (right (app (var o) (abs (var (i (i o))))) here) ∈≡ (~ abs≡inv pf)))
eqL1 (abs (var (i o))) f fn pf = inr (inr refl)
eqL1 (abs (abs (var (i (i x))))) f fn pf with abs≡inv (abs≡inv pf)
... | p1 = exfalso (o∉Λ→i (Λ→ i (f x)) (left (left here (abs (abs (var (i (i x)))))) (var (i o)) ∈≡ (~ p1)))
eqL1 (abs (abs (app (var (i (i x))) L3))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 = exfalso (o∉Λ→i (Λ→ i (f x)) (left here (abs (abs (app (var (i (i x))) L3))) ∈≡ (~ p1)))
eqL1 (abs (abs (app (app (var (i (i x))) L4) L3))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (o∉Λ→i (Λ→ i (f x)) (here ∈≡ (~ p3)))
eqL1 (abs (abs (app (app (var o) L4) (var (i (i x)))))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 = exfalso (x∉Λ→i (Λ→ i (f x)) o (λ q → o∉Λ→i (f x) q) (here ∈≡ (~ p2)))
eqL1 (abs (abs (app (app (var o) L4) (var (i o))))) f fn pf with eqL1 L4 (lift (lift f)) (liftProof f fn) (_×_.snd (app≡inv (_×_.fst (app≡inv (abs≡inv (abs≡inv pf))))))
... | inl x = inl ((~ (_×_.snd (app≡inv (_×_.fst (app≡inv (abs≡inv (abs≡inv pf))))))) ! ext (bind (lift (lift f))) x)
... | inr (inl x) = inr (inl (((~ (_×_.snd (app≡inv (_×_.fst (app≡inv (abs≡inv (abs≡inv pf)))))))) ! ext (bind (lift (lift f))) x))
... | inr (inr x) = inr (inr (((~ (_×_.snd (app≡inv (_×_.fst (app≡inv (abs≡inv (abs≡inv pf)))))))) ! ext (bind (lift (lift f))) x))

exf1 : ∀ {X} → (i (o {X})) ∈ abs (var (i o)) → ⊥
exf1 (down ())

exf2 : ∀ {X} → (i (o {X})) ∈ var o → ⊥
exf2 ()

eq21 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → dec X → L [ io (io var P) Q ] ≡ app (app (abs (abs L)) P) Q → pure (app (app (abs (abs L)) P) Q) → TwoCycleSolutions {X}
eq21 (var (i (i x))) P Q d () np
eq21 (var (i o)) P Q d p np = inf (inf21 refl p)
eq21 (var o) P Q d p np = inf (inf22 refl p)
eq21 (app L12 L3) P Q d p np with app≡inv p
... | (p1 , p2) with eq21L3 L3 P Q (transp (λ z → z ≡ Q) (eqPf L3 P Q) p2)
-- This is EQ24
eq21 (app (var (i (i x))) .(var o)) P Q d p np | () , p2 | inl refl
eq21 (app (var (i o)) .(var o)) P Q d p np | p1 , p2 | inl refl = inf (inf5 (~ p) p1)
eq21 (app (var o) .(var o)) P Q d p np | p1 , p2 | inl refl = inf (inf6 (~ p) p1)
eq21 (app (app L1 L2) .(var o)) P Q d p np | p1 , p2 | inl refl with app≡inv p1
... | p3 , p4 with eq24L2 L2 P Q (transp (λ z → z ≡ P) (eqPf L2 P Q) p4)
eq21 (app (app L .(var (i o))) .(var o)) P Q d p np | p1 , p2 | inl refl | p3 , p4 | inl refl = case (λ {refl → pure1 (~ p) p3 np}) (λ {refl → imp5 (~ p) p3}) (CCGen L (var (i o)) (var o) _ (λ x _ → refl) p3)
eq21 (app (app (var (i o)) L2) .(var o)) P Q d p np | p1 , p2 | inl refl | p3 , p4 | inr x = imp6 (app≡ (app≡ (~ p3) p4) p2) p3 p4
eq21 (app (app (var o) L2) .(var o)) P Q d p np | p1 , p2 | inl refl | p3 , p4 | inr x = pure2 (app≡ (app≡ (~ p3) refl) p2) p3 p4 np
eq21 (app (app (abs L1) L2) .(var o)) P Q d p np | p1 , p2 | inl refl | p3 , p4 | inr x with np (contr ((app (app (abs (abs (app (L1 [ L2 ]ₒ) (var o)))) P) Q)) (appL→ (appL→ (abs→ (abs→ (appL→ (redex L1 L2)))))))
                                                                                                (contr _ (appL→ (redex (abs (app (app (abs L1) L2) (var o))) P)))
... | ()
-- This is EQ32
eq21 (app (var (i (i x))) L3) P Q d p np | () , p2 | inr L3hasnoY
-- Possible Infinite Cycles...
eq21 (app (var (i o)) L3) P Q d p np | () , p2 | inr L3hasnoY -- Infinite Term, Could be a solution
eq21 (app (var o) L3) P Q d p np | p1 , p2 | inr L3hasnoY = imp4 (app≡ (~ p1) p2) p1 p2 -- Impure Solution, Could be infinite
eq21 (app L12@(app L1 L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY with app≡inv p1
-- How to go about making all the infinite cases?
eq21 (app (app (var (i o)) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p3 , p4 = imp3 (app≡ (app≡ p4 p4) p2) p3 p4 p2
eq21 (app (app (var o) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p3 , p4 with decΛ ((dec↑ (dec↑ d)) (i o)) L3
... | inl ioInL3 with decTopIo L3
-- L3isX, use LercherEq3 twice...
eq21 {X} (app (app (var o) L2) .(var (i o))) P .P d p np | p1 , refl | inr L3hasnoY | p3 , p4 | inl ioInL3 | inl refl =
    let doubleSub = ~ eqPf L2 P P ! p4
        lercherEq3Call1 = lercherEq3 (L2 [ lift (io var P) ]) P doubleSub
        c11 : L2 ≡ var o → TwoCycleSolutions {X}
        c11 = λ {refl → pure3 (~ p) p3}
        c1 = λ {q → c11 (bindOWithLift L2 _ q)}
        c21 = λ {refl → pure4 (~ p) p3}
        c22 = λ {refl → exfalso (len≡≠ _ _ p3 λ ql → ¬S4≤ (++≤LN O (≡≤≡ (~ len→ i P ! ~ (len→ i (Λ→ i P))))) ql)}
        c2 = λ q → case c21 c22 (lercherEq3Io L2 P q)
    in case c1 c2 lercherEq3Call1
... | inr L3isntX with decTop L2
eq21 {X = X} (app (app (var o) .(var o)) L3) P .P d p np | p1 , p2 | inr L3hasnoY | p3 , refl | inl ioInL3 | inr L3isntX | inl refl = exfalso (L3isntX (bind-rec L3 (io (io var P) P) {x = i o} ioInL3 p2))
eq21 {X} (app (app (var o) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p3 , p4 | inl ioInL3 | inr L3isntX | inr L2isntVar = 
    let
        L4 = L2 [ (L3 [ Λ→i Q ]ₒ) ]ₒ
        oInL4isO : o ∈ L4 → L4 ≡ var o
        oInL4isO = λ {q → bind-rec L4 (io var P) {x = o} q (~ bind-law (io var (L3 [ Λ→i Q ]ₒ)) (io var P) L2 ! (bind-ext (λ {(i (i x)) → refl
                                                                                                                            ; (i o) → refl
                                                                                                                            ; o → ~ bind-law (io var (Λ→i Q)) (io var P) L3 ! bind-ext (λ {(i (i x)) → refl
                                                                                                                                                                                         ; (i o) → refl
                                                                                                                                                                                         ; o → NoBindOnWeaking Q P}) L3 ! p2}) L2 ! p4))}
        oL2oL4 : o ∈ L2 → L4 ≡ var o
        oL2oL4 = λ {q → oInL4isO (∈[∈]2 q _ (bind-io L3 (io var (Λ→ i Q)) o ioInL3 here))}
        L2IsntX : L2 ≡ var (i o) → TwoCycleSolutions {X}
        L2IsntX = λ {refl → case (λ {refl → pure4 {X} (app≡ (app≡ (~ (p2 ! p3)) p4) (~ p2)) (p2 ! p3)}) (λ {refl → exfalso (exf2 {X} ioInL3)}) (eq40lemmaIO L3 (io (io var P) Q) (λ x _ → refl) (p2 ! p3)) }
        ioNotInL2 : (i o) ∈ L2 → TwoCycleSolutions
        ioNotInL2 = λ q → L2IsntX (bind-rec L2 (io (io var P) Q) {x = i o} q p4)
        L4isntVar : L4 ≡ var o → TwoCycleSolutions
        L4isntVar = (λ { q → case (λ {refl → L2IsntX refl}) (λ q2 → exfalso (L3isntX (eq21Helper L3 Q q2))) (eq21HelperIo L2 (L3 [ Λ→i Q ]ₒ) q) })
        noOinL2 : o ∈ L2 → TwoCycleSolutions
        noOinL2 = λ {q → L4isntVar (oL2oL4 q)}
        -- c1 = λ {refl → exfalso (L3hasnoY here)}
        -- c2 = λ {refl → exfalso (L3hasnoY (down here))}
        eq40OCall = eq40O L3 L2 (io (io var P) Q) (λ x _ → refl) (p2 ! p3)    
        c1 = λ q → noOinL2 q
        c21 = λ q → ioNotInL2 q -- exfalso (ioNotInL2 q)
        c221 = λ {refl → exfalso (exf2 {X} ioInL3)} -- ioIn3
        c3 = λ {refl → case (λ q → noOinL2 (here ∈≡ (~ q))) (λ q → case (λ q2 → L2IsntX q2) (λ q2 → noOinL2 (down here ∈≡ (~ q2))) q) (eqL1 L2 (io (io var P) Q) (λ x _ → refl) (p4 ! p2 ! p3))}
        c4 = λ {refl → exfalso (exf1 {X} ioInL3 )} -- ioIn3
        c222 = λ q → case c3 c4 q
        c22 = λ q → case c221 c222 q
        c2 = λ q → case c21 c22 q
    in case c1 c2 eq40OCall -- case c1 c2 (CCGen2 L3 (io (io var P) Q) (λ x _ → refl) {Q = L2} (p2 ! p3))
eq21 {X} (app (app (var o) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p3 , p4 | inr ioNotInL3 =
    let doubleSub = ~ eqPf L3 P Q ! p2
        OccursMapCall = occurs-map (L3 [ lift (io var P) ]) _ _ doubleSub λ q → L3hasnoY (bind-o _ L3 q)
        finalCall = occurs-map-gen L3 (Λ→ i Q) (lift (io var P)) (λ {(i x) → λ _ → here; o → λ nc → exfalso (ioNotInL3 nc)})
                   (λ {(i x) → λ _ → refl; o → λ nc → exfalso (o∉Λ→i P nc)}) OccursMapCall L3hasnoY
        issueTerm : L3 ≡ Λ→i (Λ→ i Q) → TwoCycleSolutions {X}
        issueTerm = λ {refl →  exfalso (len≡≠ _ _ p3 (λ q → ¬S4≤ (zero≤ ≤+≤ ≡≤≡ ((~ len→ i Q ! ~ (len→ i (Λ→ i Q))))) q))}
    in issueTerm finalCall
eq21 (app (app (abs L1) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p3 , p4 with np (contr _ (appL→ (redex (abs (app (app (abs L1) L2) L3)) P)))
                                                                                        (contr _ (appL→ (appL→ (abs→ (abs→ (appL→ (redex L1 L2)))))))
... | ()
