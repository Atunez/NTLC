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

-- CCGen2 : ∀ {X} (L P Q : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) → (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x) → bind f L ≡ abs (abs (app (app L (var (i o))) (var o))) → (∀ x → x ∈ L → L ≡ var x)
-- CCGen2 (var x) P Q f fn p .x here = refl
-- CCGen2 (abs (var (i x))) P Q f fn p y occ = exfalso (o∉Λ→i (f x) (transp (λ z → o ∈ z) (~ (abs≡inv p)) (down (left (right (abs (var (i x))) here) (var o)))))
-- CCGen2 (abs (abs (var (i x)))) P Q f fn p y occ = {!   !}
-- CCGen2 (abs (abs (app (var (i (i x))) L₁))) P Q f fn p y occ = {!   !}
-- CCGen2 (abs (abs (app (app L (var (i (i x)))) L₁))) P Q f fn p y occ = {!   !}
-- CCGen2 (abs (abs (app (app L (var (i o))) (var (i (i x)))))) P Q f fn p y occ = {!   !}
-- -- CCGen2 (abs (abs (app (app L (var (i o))) (var (i (i o)))))) P Q f p y occ = {!   !}
-- CCGen2 (abs (abs (app (app L (var (i o))) (var o)))) P Q f fn p (i (i x)) (down (down (left (left occ .(var (i o))) .(var o)))) =
--     let (p1 , p2) = app≡inv (abs≡inv (abs≡inv p))
--         (p3 , p4) = app≡inv p1
--         rec = CCGen2 L L L _ {!   !} p3 (i (i (i (i x)))) occ
--         extStuff = ~ p3 ! ext (bind (lift (lift f))) rec
--         check : i (i x) ∈ (lift (lift f)) (i (i (i (i x))))
--         check = {!   !}
--     in {! extStuff ! ext (Λ→ i ∘ Λ→ i) (fn x (occIni ? ?))   !}
-- CCGen2 (abs (abs (app (app L (var (i o))) (var o)))) P Q f fn p (i o) (down (down (left (left occ .(var (i o))) .(var o)))) =
--     let (p1 , p2) = app≡inv (abs≡inv (abs≡inv p))
--         (p3 , p4) = app≡inv p1
--         rec = CCGen2 L L L _ {!   !} p3 (i (i (i o))) occ
--         extStuff = ~ p3 ! ext (bind (lift (lift f))) rec
--     in {!   !}
-- CCGen2 (abs (abs (app (app L (var (i o))) (var o)))) P Q f fn p o (down (down (left (left occ .(var (i o))) .(var o)))) =
--     let (p1 , p2) = app≡inv (abs≡inv (abs≡inv p))
--         (p3 , p4) = app≡inv p1
--         rec = CCGen2 L L L _ {!   !} p3 (i (i o)) occ
--         extStuff = ~ p3 ! ext (bind (lift (lift f))) rec
--     in {!   !}

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
    in case c1 c2 (CCGen L L L (lift (lift f)) (λ {(i (i x)) → λ q → ext (Λ→i ∘ Λ→i) (fn x (occIni _ (occIni _ q)))
                                                ; (i o) → λ q → exfalso (x∉Λ→i (Λ→ i (f (i o))) o (λ q2 → exfalso (o∉Λ→i (f (i o)) q2)) q)
                                                 ; o → λ q → exfalso (o∉Λ→i (Λ→ i (f o)) q)}) p3)


eq21HelperIo : ∀ {X} (M : Λ (↑ (↑ X))) (N : Λ (↑ X)) → M [ N ]ₒ ≡ var o → M ≡ var (i o) ⊔ N ≡ var o
eq21HelperIo (var (i o)) N p = inl refl
eq21HelperIo (var o) N p = inr p

eq21Helper : ∀ {X} (M : Λ (↑ (↑ X))) (N : Λ X) → bind (io var (Λ→ i N)) M ≡ var o → M ≡ var (i o)
eq21Helper (var (i o)) N p = refl
eq21Helper (var o) N p = exfalso ((o∉Λ→i N) (var∈≡ (Λ→ i N) o p))

-- CCGen2 : ∀ {X} (L : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) → (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x) → {Q : Λ (↑ (↑ X))} → L [ f ] ≡ abs (abs (app (app (var o) Q) L)) → L ≡ var o ⊔ L ≡ abs (var (i o))
-- CCGen2 (var (i (i x))) f fn {Q} p with ~ fn x (transp (λ q → x ∈ q) (~ p) (down (down (right (app (var o) Q) here)))) ! p
-- ... | ()
-- CCGen2 (var (i o)) f fn {Q} p = {!   !}
-- CCGen2 (var o) f fn {Q} p = {!   !}
-- CCGen2 (abs (var (i (i (i x))))) f fn {Q} p with ~ ext (Λ→i) (fn x {!   !}) ! (abs≡inv p)
-- ... | ()
-- CCGen2 (abs (var (i (i o)))) f fn {Q} p = {!   !} -- L3[z] = λx.z , impossible since L3[P] contains x inside the abstraction, but L3[P] = abs ([Λ→i P]), and o ∉ Λ→i P
-- CCGen2 (abs (var (i o))) f fn {Q} p = {!   !}
-- CCGen2 (abs (abs (var (i (i (i (i x))))))) f fn {Q} p = {!   !}
-- CCGen2 (abs (abs (var (i (i (i o)))))) f fn {Q} p = {!   !}
-- CCGen2 (abs (abs (var (i (i o))))) f fn {Q} p = {!   !}
-- CCGen2 (abs (abs (app (var (i (i x))) L₁))) f fn {Q} p = {!   !}
-- CCGen2 (abs (abs (app (app (var (i (i x))) L₂) L₁))) f fn {Q} p = {!   !}
-- CCGen2 (abs (abs (app (app (var o) L₂) L₁))) f fn {Q} p with app≡inv (abs≡inv (abs≡inv p))
-- ... | p1 , p2 with CCGen2 L₁ (lift (lift f)) (λ {(i (i x)) → λ q → ext (Λ→i ∘ Λ→i) (fn x (occIni _ (occIni _ q)))
--                                                 ; (i o) → λ q → exfalso (x∉Λ→i (Λ→ i (f (i o))) o (λ q2 → exfalso (o∉Λ→i (f (i o)) q2)) q)
--                                                  ; o → λ q → exfalso (o∉Λ→i (Λ→ i (f o)) q)}) {Q = L₂} p2
-- CCGen2 (abs (abs (app (app (var o) L₂) .(var o)))) f fn {Q} p | p1 , () | inl refl
-- CCGen2 (abs (abs (app (app (var o) L₂) .(abs (var (i o)))))) f fn {Q} p | p1 , () | inr refl

-- eq40gen : ∀ {X} (L : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → {Q : Λ (↑ (↑ X))}
--      →  L [ f ] ≡ abs (abs (app (app (var o) Q) (Λ→i L))) → L ≡ var o
-- eq40gen (var x) f fn {Q} p = {!   !}
-- eq40gen (abs (var x)) f fn {Q} p = {!   !}
-- eq40gen (abs (abs (var x))) f fn {Q} p = {!   !}
-- eq40gen (abs (abs (app (var x) L₁))) f fn {Q} p = {!   !}
-- eq40gen (abs (abs (app (app L L₂) L₁))) f fn {Q} p with app≡inv (abs≡inv (abs≡inv p))
-- ... | p1 , p2 =
--    let rec = eq40gen L₁ (lift (lift f)) {!   !} (p2 ! abs≡ (abs≡ (app≡ {!   !} {!   !})))
--    in {!   !}

eq40lemma : ∀ {X} (L : Λ (↑ (↑ X))) (f : ↑ (↑ X) → Λ X) (fn : (∀ x → x ∈ f (i (i x)) → f (i (i x)) ≡ var x)) {x} → L [ f ] ≡ abs (abs (app (app (var o) (var x)) L)) → L ≡ var x
eq40lemma L f fn {x} p = {!   !}

-- eq40 : ∀ {X} (L3 L2 : Λ (↑ (↑ X))) (x : ↑ (↑ X)) → x ∈ L3 → ∀ (f : ↑ (↑ X) → Λ X) (fn : (∀ y → i (i y) ∈ L3 → y ∈ f x → ⊥)) → L3 [ f ] ≡ abs (abs (app (app (var o) L2) L3)) → L3 ≡ var x
eq40 : ∀ {X} (L3 : Λ (↑ (↑ X))) (x : ↑ (↑ X)) → x ∈ L3 → ∀ (f : ↑ (↑ X) → Λ X) (fn : Set) → L3 [ f ] ≡ abs (abs (app (app (var o) (Λ→i (Λ→i (f x)))) L3)) → L3 ≡ var x
eq40 (var x₁) .x₁ here f fn p = refl
eq40 (abs (var .(i o))) o (down here) f fn p with abs≡inv p
... | p1 with bind-rec (abs (app (app (var o) (var (i o))) (abs (var (i o))))) (io var (Λ→i (f o))) (down (left (right _ here) _) ) (~ p1)
... | ()
eq40 (abs (var .(i (i x)))) (i x) (down here) f fn p with abs≡inv p
-- ... | p1 with bind-rec (abs (app (app (var o) (var (i o))) (abs (var (i (i x)))))) (io var (Λ→i (f x))) (down (left (right _ here) _)) (~ (p1 ! {!   !} ) )
... | p1 with bind-rec (abs (app (app (var o) (var (i o))) (var (i (i o))))) (io (io var _) (Λ→i (f (i x)))) (down (left (right _ here) _))
                        (~ (p1 ! abs≡ (ext (app _) (abs≡ refl ) ) ) )
... | ()
eq40 (abs (abs (var .(i (i x))))) x (down (down here)) f fn p with abs≡inv (abs≡inv p)
... | p1 with bind-rec (app (app (var (i o)) (var o)) (abs (abs (var (i (i (i x)))))) ) (io var (Λ→i (Λ→ i (f x)))) (left (right  _ here) _) (~ p1)
... | ()
eq40 (abs (abs (app L3 L4))) x (down (down (left occ .L4))) f fn p with app≡inv (abs≡inv (abs≡inv p))
eq40 (abs (abs (app (var .(i (i x))) L4))) x (down (down (left here .L4))) f fn p | p1 , p2 = exfalso (o∉Λ→i _ (left here _ ∈≡ (~ p1)) )
eq40 (abs (abs (app (app L3 L5) L4))) x (down (down (left occ .L4))) f fn p | p1 , p2 with app≡inv p1
eq40 (abs (abs (app (app (var (i y)) L5) L4))) x (down (down (left occ .L4))) f fn p | p1 , p2 | p3 , p4 = exfalso (o∉Λ→i (lift f y) (here ∈≡ (~ p3) ) )
eq40 (abs (abs (app (app (var o) L5) L4))) x (down (down (left (right .(var o) occ) .L4))) f fn p | p1 , p2 | p3 , p4
      with bind-rec L5 (lift (lift f)) occ p4
... | refl with eq40lemma L4 (lift (lift f)) {!   !} {i (i x)} p2
eq40 (abs (abs (app (app (var o) .(var (i (i (i (i x)))))) .(var (i (i (i (i x)))))))) (i (i x)) (down (down (left (right .(var o) occ) .(var (i (i (i (i x)))))))) f fn p | p1 , p2 | p3 , p4 | refl | refl = {!   !}
eq40 (abs (abs (app (app (var o) .(var (i (i (i o))))) .(var (i (i (i o))))))) (i o) (down (down (left (right .(var o) occ) .(var (i (i (i o))))))) f fn p | p1 , p2 | p3 , p4 | refl | refl = {!   !}
eq40 (abs (abs (app (app (var o) .(var (i (i o)))) .(var (i (i o)))))) o (down (down (left (right .(var o) occ) .(var (i (i o)))))) f fn p | p1 , p2 | p3 , p4 | refl | refl = {!   !}
-- bind-rec L4 (lift (lift f)) {!   !} p2
eq40 (abs (abs (app L3 L4))) x (down (down (right .L3 occ))) f fn p with app≡inv (abs≡inv (abs≡inv p))
eq40 (abs (abs (app (var (i (i y))) L4))) x (down (down (right .(var (i (i y))) occ))) f fn p | p1 , p2 = exfalso (o∉Λ→i (Λ→ i (f y)) ((left here _) ∈≡ (~ p1) ) )
eq40 (abs (abs (app (app (var y) L5) L4))) x (down (down (right .(app (var y) L5) occ))) f fn p | p1 , p2 with app≡inv p1
eq40 (abs (abs (app (app (var (i y)) L5) L4))) x (down (down (right .(app (var (i y)) L5) occ))) f fn p | p1 , p2 | p3 , p4 = exfalso (o∉Λ→i (lift f y) (here ∈≡ (~ p3) ) )
eq40 (abs (abs (app (app (var o) L5) L4))) x (down (down (right .(app (var o) L5) occ))) f fn p | p1 , p2 | p3 , p4
  with eq40 L4 _ occ (lift (lift f)) _ (p2 ! abs≡ (abs≡ (app≡ (ext (app (var o)) goal ) refl  )))
       where goal = ? -- {!   !} ! ext Λ→i (ext Λ→i p4 )
... | refl = {! x  !}

-- eq40 (var y) P .y here f p = refl
-- eq40 (abs (var y)) P (i (i x)) occ f p = {!   !}
-- eq40 (abs (var y)) P (i o) occ f p = {!   !}
-- eq40 (abs (var .(i o))) P o (down here) f p with abs≡inv p
-- ... | p1 = {!   !}
-- eq40 (abs (abs L3)) P x occ f p = {!   !}

-- eq40 : ∀ {X} (L : Λ (↑ X)) (P : Λ X) f → bind f L ≡ abs (abs (app (app (var o) (Λ→i (Λ→i P))) (Λ→i L))) → L ≡ var o
-- eq40 (var x) P f p = {!   !}
-- eq40 (abs (var x)) P f p = {!   !}
-- eq40 (abs (abs (var x))) P f p = {!   !}
-- eq40 (abs (abs (app (var x) L₁))) P f p = {!   !}
-- eq40 (abs (abs (app (app (var (i x)) L₂) L₁))) P f p = {!   !}
-- eq40 (abs (abs (app (app (var o) L₂) L₁))) P f p with app≡inv (abs≡inv (abs≡inv p))
-- ... | p1 , p2 =
--     let rec = eq40 L₁ (L₂ [ I ]ₒ) (lift (lift f)) (p2 ! abs≡ (abs≡ (app≡ (app≡ refl {! unweaken L₂ ? {M = I}  !}) {!   !})))
--     in {!   !}

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
eq21 (app (app (var o) .(var o)) L3) P .P d p np | p1 , p2 | inr L3hasnoY | p3 , refl | inl ioInL3 | inr L3isntX | inl refl = exfalso (L3isntX (bind-rec L3 (io (io var P) P) {x = i o} ioInL3 p2))
... | inr L2isntVar =
    let
        L4 = L2 [ (L3 [ Λ→i Q ]ₒ) ]ₒ
        noOinL3Subs = occurs-map (L3 [ lift (io var P) ]) _ _ (~ eqPf L3 P Q ! p2) λ q → L3hasnoY (bind-oo (lift (io var P)) L3 (λ {(i (i x)) → λ ()
                                                                                                                                  ; (i o) → λ q → exfalso (o∉Λ→i P q)
                                                                                                                                  ; o → λ _ → refl}) q)
        oInL4isO : o ∈ L4 → L4 ≡ var o
        oInL4isO = λ {q → bind-rec L4 (io var P) {x = o} q (~ bind-law (io var (L3 [ Λ→i Q ]ₒ)) (io var P) L2 ! (bind-ext (λ {(i (i x)) → refl
                                                                                                                            ; (i o) → refl
                                                                                                                            ; o → ~ bind-law (io var (Λ→i Q)) (io var P) L3 ! bind-ext (λ {(i (i x)) → refl
                                                                                                                                                                                         ; (i o) → refl
                                                                                                                                                                                         ; o → NoBindOnWeaking Q P}) L3 ! p2}) L2 ! p4))}
        oL2oL4 : o ∈ L2 → L4 ≡ var o
        oL2oL4 = λ {q → oInL4isO (∈[∈]2 q _ (bind-io L3 (io var (Λ→ i Q)) o ioInL3 here))}
        L2IsntX : L2 ≡ var (i o) → ⊥
        L2IsntX = λ {refl → {!   !} }
        ioNotInL2 : (i o) ∈ L2 → ⊥
        ioNotInL2 = λ q → L2IsntX (bind-rec L2 (io (io var P) Q) {x = i o} q p4)
        L4isntVar : L4 ≡ var o → ⊥
        L4isntVar = (λ { q → case (λ {refl → L2IsntX refl}) (λ q2 → L3isntX (eq21Helper L3 Q q2)) (eq21HelperIo L2 (L3 [ Λ→i Q ]ₒ) q) })
        noOinL2 : o ∈ L2 → ⊥
        noOinL2 = λ {q → L4isntVar (oL2oL4 q)}
        -- c1 = λ {refl → exfalso (L3hasnoY here)}
        -- c2 = λ {refl → exfalso (L3hasnoY (down here))}
    in {!   !} -- case c1 c2 (CCGen2 L3 (io (io var P) Q) (λ x _ → refl) {Q = L2} (p2 ! p3))

    -- let bindrec0 : o ∈ L2 → ⊥
    --     bindrec0 = λ {q → case (λ {refl → {!   !}}) (λ q2 → q2 {!   !}) (decTop L2)}
    --     bindrec1 : (i o) ∈ L2 → L2 ≡ var (i o)
    --     bindrec1 = λ {q → bind-rec L2 (io (io var P) Q) q p4}
    --     bindrec2 : (i o) ∈ L3 → L3 ≡ var (i o)
    --     -- P4 into P2
    --     -- Bind (io (io var P) (L3 [ p ,, q ])) L2 = P
    --     bindrec2 = λ {q → let eqPfC = eqPf L3 P Q
    --                         --   ds2 = doubleSubSub2 L3 P _ Q Q (~ p4) refl
    --                         --   replace2 = eqPfC ! ds2
    --                         --   ds = doubleSubSub L3 P (bind (io (io var P) Q) L2) Q Q (~ p4) refl
    --                         --   replace = ~ ds ! p2
    --                         --   bl = bind-law (lift (io var (bind (io (io var P) Q) L2))) (io var Q) L3
    --                         --   blr = bl ! ~ replace2
    --                         --   bindrec = {!   !}
    --                       in {!   !}}
    -- in exfalso (L3isntX (bindrec2 ioInL3))
eq21 {X} (app (app (var o) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p3 , p4 | inr ioNotInL3 =
    let doubleSub = ~ eqPf L3 P Q ! p2
        OccursMapCall = occurs-map (L3 [ lift (io var P) ]) _ _ doubleSub λ q → L3hasnoY (bind-o _ L3 q)
        finalCall = occurs-map-gen L3 (Λ→ i Q) (lift (io var P)) (λ {(i x) → λ _ → here; o → λ nc → exfalso (ioNotInL3 nc)})
                   (λ {(i x) → λ _ → refl; o → λ nc → exfalso (o∉Λ→i P nc)}) OccursMapCall L3hasnoY
        issueTerm : L3 ≡ Λ→i (Λ→ i Q) → TwoCycleSolutions {X}
        issueTerm = λ {refl → exfalso (len≡≠ _ _ p3 (λ q → ¬S4≤ (zero≤ ≤+≤ ≡≤≡ ((~ len→ i Q ! ~ (len→ i (Λ→ i Q))))) q))}
    in issueTerm finalCall
eq21 (app (app (abs L1) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p3 , p4 with np (contr _ (appL→ (redex (abs (app (app (abs L1) L2) L3)) P)))
                                                                                        (contr _ (appL→ (appL→ (abs→ (abs→ (appL→ (redex L1 L2)))))))
... | ()
