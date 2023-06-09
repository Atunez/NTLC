module Cycles where

open import Lambda public

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

occurs-map : ∀ {X} (A : Λ (↑ X)) (B : Λ X) → A [ B ]ₒ ≡ B → ¬ (o ∈ A) → A ≡ Λ→ i B
occurs-map A B h nocc =
  let e0 : ∀ x → x ∈ A → var x ≡ (Λ→ i ∘ io var B) x
      e0 = (λ { (i x) → λ p → refl ; o → exfalso ∘ nocc })
      e1 = symm (bind-nat1 i (io var B))
      e2 = bind-occurs (var) (Λ→ i ∘ io var B) A e0
   in (~ bind-unit1 A) !  (e2 ! (e1 A ! ext (Λ→ i) h))

lercherEq3gen : ∀ {X Y} (A : Λ X) (f : X → Λ X) (x : X) (d : decAt X x) → (A [ f ] ≡ f x) → A ≡ var x ⊔ x ∉ A
lercherEq3gen (var y) f x d p with d y
... | inl yes  = inl (var≡ (~ yes) )
... | inr no   = inr (λ {  here → no refl })
lercherEq3gen (app A1 A2) f x d p with f x in p0
... | (app t1 t2) with app≡inv p | p0
... | (p1 , p2) | p3 = {!   !}
lercherEq3gen (abs A0) f x d p = {!   !}

lercherEq3 : ∀ {X} (A : Λ X) (B : Λ (↑ X)) → B [ A ]ₒ ≡ A → B ≡ var o ⊔ B ≡ Λ→ i A
lercherEq3 A B e = {!   !}

lercherEq2gen : ∀ {X} (A1 A2 : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → bind f A1 ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2gen (var (i x)) A2 f fn p with ~ (fn x (∈≡ (down (left here A2)) (~ p))) ! p
... | ()
lercherEq2gen (var o) A2 f fn p = refl
lercherEq2gen (abs (var (i (i x)))) A2 f fn p with abs≡inv p
... | M with  fn x (occIni (f (i x)) (∈≡ (left (down here) A2) (~ M)))
... | t with ~ (ext (Λ→ i) t) ! M
... | ()
lercherEq2gen (abs (var (i o))) A2 f fn p with abs≡inv p
...   | M = exfalso (o∉Λ→i (f o) (∈≡ (left (down here) A2) (~ M)))
lercherEq2gen (abs (app A1 A3)) A2 f fn p with app≡inv (abs≡inv p)
...         | (p1 , p2) = let g = lift f
                              gn = λ {o → λ q → exfalso (o∉Λ→i (f o) q); (i x) → λ q → ext (Λ→ i) (fn x (occIni (f (i x)) q))}
                              f' = (λ x → io (Λ→ i) (var o) (↑→ f x))
                              rec = lercherEq2gen A1 A3 g gn p1
                            in ~ p1 ! ext (bind g) rec

lercherEq2 : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X)→ A1 [ B ]ₒ ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2 A1 A2 B p = lercherEq2gen A1 A2 (io var B) (λ x _ → refl) p

lercherHelper : ∀ (P1 P2 : Λ (↑ ⊥)) (Q : Λ ⊥) → P1 ≡ var o → P2 ≡ var o ⊔ P2 ≡ Λ→ i Q → (app P1 P2) [ Q ]ₒ ≡ app (abs (app P1 P2)) Q → abs (app P1 P2) ≡ ω × Q ≡ ω
lercherHelper .(var o) .(var o) Q refl (inl refl) p3 = refl , _×_.fst (app≡inv p3)
lercherHelper .(var o) .(Λ→ i Q) Q refl (inr refl) p3 =
  let qPrf = _×_.fst (app≡inv p3)
  in exfalso {!   !}

lercher : ∀ (P : Λ (↑ ⊥)) (Q : Λ ⊥) → P [ Q ]ₒ ≡ app (abs P) Q → abs P ≡ ω × Q ≡ ω
lercher (var (i x)) q prf = exfalso x
lercher (var o) q prf with prf
... | p = {!   !}
lercher (app P1 P2) Q prf =
   let (lhs , rhs) = app≡inv prf
       l1 = lercherEq2 _ _ _ lhs
       l2 = lercherEq3 Q P2 rhs
   in lercherHelper _ _ _ l1 l2 prf




-- module CycleStuff where


--   data pre2cycle {X : Set} : Λ X → Set where
--     red2 : ∀ (P : Λ (↑ X)) (Q : Λ X) → (P [ Q ] ⟶ app (abs P) Q) → pre2cycle (app (abs P) Q)

--   -- data CycleEnum : Set where
--   --   case1 :

--   Qterm : ∀ {X} → Λ X
--   Qterm = Λ→ ex_falso (abs (abs (app (app (var o) (var (i o))) (var o))))

--   -- Qcyc : ∀ {X} → ∀ (P : Λ X) → pre2cycle (app (abs (app (app (var o) (Λ→ i P)) (var o))) (Qterm {X}))
--   -- Qcyc P = red2 (app (app (var o) (Λ→ i P)) (var o)) Qterm (appL→
--   --     (⟶≡ (redex (abs (app (app (var o) (var (i o))) (var o)))
--   --           (bind (io var (abs (abs (app (app (var o) (var (i o))) (var o)))))  (Λ→ i P)) )
--   --         {! bind-ext ? ? (abs (app (app (var o) (var (i o))) (var o)))  !} ) )

--             -- bind-ext : ∀ {X Y : Set} {f g : X → Λ Y} → f ≃ g → bind f ≃ bind g
