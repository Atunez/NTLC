module BicyclesCase22 where

open import Lambda public
open import Cycles public
open import Length public
open import Decidability public
open import Bicycles public


liftProof : ∀ {X} (f : ↑ (↑ X) → Λ X) → ((x : X) → x ∈ f (i (i x)) → f (i (i x)) ≡ var x) → ((x : ↑ (↑ X)) → x ∈ Λ→i (Λ→i (f x)) → Λ→i (Λ→i (f x)) ≡ var x)
liftProof f fn = (λ {(i (i x)) → λ q → ext (Λ→i ∘ Λ→i) (fn x (occIni _ (occIni _ q)))
                                                ; (i o) → λ q → exfalso (x∉Λ→i (Λ→ i (f (i o))) o (λ q2 → exfalso (o∉Λ→i (f (i o)) q2)) q)
                                                 ; o → λ q → exfalso (o∉Λ→i (Λ→ i (f o)) q)})

eq40lemmaO : ∀ {X} (L : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) (fn : (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x)) → L [ f ] ≡ abs (abs (app (app (var o) (var o)) L)) → L ≡ var o ⊔ (L ≡ var (i o) ⊔ L ≡ abs (var (i o)))
eq40lemmaO (var (i (i x))) f fn pf with ~ pf ! fn x (transp (λ z → x ∈ z) (~ pf) (down (down (right (app (var o) (var o)) here))))
... | ()
eq40lemmaO (var (i o)) f fn pf = inr (inl refl)
eq40lemmaO (var o) f fn pf = inl refl
eq40lemmaO (abs (var (i (i (i x))))) f fn pf with abs≡inv pf
... | p1 with ~ p1 ! ext Λ→i (fn x (occIni (f (i (i x))) (down (right (app (var o) (var o)) (down here)) ∈≡ (~ p1))))
... | ()
eq40lemmaO (abs (var (i (i o)))) f fn pf with abs≡inv pf
... | p1 = exfalso (o∉Λ→i (f (i o)) (down (right (app (var o) (var o)) (down here)) ∈≡ (~ p1)))
eq40lemmaO (abs (var (i o))) f fn pf = inr (inr refl)
eq40lemmaO (abs (abs (var (i (i x))))) f fn pf with abs≡inv (abs≡inv pf)
... | p1 = exfalso (o∉Λ→i (Λ→ i (f x)) (left (left here (var o)) (abs (abs (var (i (i x))))) ∈≡ (~ p1)))
eq40lemmaO (abs (abs (app (var (i (i x))) L₁))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 = exfalso (o∉Λ→i (Λ→ i (f x)) (left here (var o) ∈≡ (~ p1)))
eq40lemmaO (abs (abs (app (app (var (i (i x))) L₂) L₁))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (o∉Λ→i (Λ→ i (f x)) (here ∈≡ (~ p3)))
eq40lemmaO (abs (abs (app (app (var o) (var (i (i x)))) L₁))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (o∉Λ→i (Λ→ i (f x)) (here ∈≡ (~ p4)))
eq40lemmaO (abs (abs (app (app (var o) (var o)) L))) f fn pf with eq40lemmaO L (lift (lift f)) (liftProof f fn) (_×_.snd (app≡inv (abs≡inv (abs≡inv pf))))
... | inl x = inl (~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) x)
... | inr (inl x) = inr (inl (~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) x))
... | inr (inr x) = inr (inr (~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) x)) -- ~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) m


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

eq40lemmaX : ∀ {X} (L : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) (fn : (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x)) {x} → L [ f ] ≡ abs (abs (app (app (var o) (var (i (i x)))) L)) → L ≡ var o ⊔ (L ≡ var (i o) ⊔ L ≡ abs (var (i o)))
eq40lemmaX (var (i (i x))) f fn pf with ~ pf ! fn x (transp (λ z → x ∈ z) (~ pf) (down (down (right (app (var o) (var _)) here))))
... | ()
eq40lemmaX (var (i o)) f fn pf = inr (inl refl)
eq40lemmaX (var o) f fn pf = inl refl
eq40lemmaX (abs (var (i (i (i x))))) f fn pf with abs≡inv pf
... | p1 with ~ p1 ! ext Λ→i (fn x (occIni (f (i (i x))) (down (right (app (var o) (var _)) (down here)) ∈≡ (~ p1))))
... | ()
eq40lemmaX (abs (var (i (i o)))) f fn pf with abs≡inv pf
... | p1 = exfalso (o∉Λ→i (f (i o)) (down (right (app (var o) (var _)) (down here)) ∈≡ (~ p1)))
eq40lemmaX (abs (var (i o))) f fn pf = inr (inr refl)
eq40lemmaX (abs (abs (var (i (i x))))) f fn pf with abs≡inv (abs≡inv pf)
... | p1 = exfalso (o∉Λ→i (Λ→ i (f x)) (left (left here (var _)) (abs (abs (var _))) ∈≡ (~ p1)))
eq40lemmaX (abs (abs (app (var (i (i x))) L₁))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 = exfalso (o∉Λ→i (Λ→ i (f x)) (left here (var _) ∈≡ (~ p1)))
eq40lemmaX (abs (abs (app (app (var (i (i x))) L₂) L₁))) f fn pf with app≡inv (abs≡inv (abs≡inv pf))
... | p1 , p2 with app≡inv p1
... | p3 , p4 = exfalso (o∉Λ→i (Λ→ i (f x)) (here ∈≡ (~ p3)))
eq40lemmaX (abs (abs (app (app (var o) (var (i (i x)))) L))) f fn pf with eq40lemmaX L (lift (lift f)) (liftProof f fn) (_×_.snd (app≡inv (abs≡inv (abs≡inv pf))))
... | inl x = inl (~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) x)
... | inr (inl x) = inr (inl (~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) x))
... | inr (inr x) = inr (inr (~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) x)) -- ~ (_×_.snd (app≡inv (abs≡inv (abs≡inv pf)))) !  ext (bind (lift (lift f))) m

eq40lemma : ∀ {X} (L : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) (fn : (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x)) {x} → L [ f ] ≡ abs (abs (app (app (var o) (var x)) L)) →  L ≡ var o ⊔ (L ≡ var (i o) ⊔ L ≡ abs (var (i o)))
eq40lemma L f fn {i (i x)} p = eq40lemmaX L f fn p
eq40lemma L f fn {i o} p with eq40lemmaIO L f fn p
... | inl x = inr (inl x)
... | inr x = inl x
eq40lemma L f fn {o} p = eq40lemmaO L f fn p


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
... | inl x = {!   !}
... | inr (inl x) = {!   !}
eq40O (abs (abs (app (app (var o) L5) .(var o)))) T f fn pf | p12 , () | p3 , p4 | inr (inr (inl refl))
eq40O (abs (abs (app (app (var o) L5) .(var (i o))))) T f fn pf | p12 , () | p3 , p4 | inr (inr (inr (inl refl)))
eq40O (abs (abs (app (app (var o) L5) .(abs (var (i o)))))) T f fn pf | p12 , () | p3 , p4 | inr (inr (inr (inr refl)))

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
