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

decAt : ∀ {X : Set} → X → Set
decAt x = ∀ y → x ≡ y ⊔ ¬ (x ≡ y)

decAto : ∀ {X : Set} → decAt {↑ X} o
decAto {X} (i x) = inr (λ ())
decAto {X} o = inl refl

decAti : ∀ {X} (x : X) → decAt x → decAt (i x)
decAti x p (i y) with p y
...                 | inl e = inl (ext i e)
...                 | inr n = inr λ {(refl) → n refl }
decAti x p o = inr (λ {()})

∈[∈] : ∀ {X} {x : X} {s : Λ X} → x ∈ s → (f : X → Λ X) → x ∈ f x → x ∈ (s [ f ])
∈[∈] here f oc2 = oc2
∈[∈] (left oc1 t) f oc2 = left (∈[∈] oc1 f oc2) (bind f t)
∈[∈] (right s oc1) f oc2 = right (bind f s) (∈[∈] oc1 f oc2)
∈[∈] (down oc1) f oc2 = down (∈[∈] oc1 (lift f) (oc2 ∈→ i))

update : ∀ {X Y : Set} (f : X → Λ Y) {x : X} (d : decAt x) (t : Λ Y) → X → Λ Y
update f d t y with d y
... | inl x=y = t
... | inr x≠y = f y

bind-recNoLen : ∀ {X Y : Set} (A : Λ X) (f : X → Λ Y) {x : X}
             → decAt x → x ∈ A → (A [ f ] ≡ f x) → A ≡ var x
bind-recNoLen A f d occ p = {!   !}
-- bind-rec (var y) f d here p = refl
-- bind-rec (app (var x₁) N) f {x} d (left occ .N) p = {!   !}
-- bind-rec (app (app M M₁) N) f {x} d (left occ .N) p with f x in fx
-- ... | app Q Q₁ with app≡inv p
-- ... | refl , refl = {! Q  !}
-- bind-rec (app (abs M) N) f {x} d (left (down occ) .N) p with f x in fx
-- ... | app Q Q₁ with app≡inv p
-- ... | refl , refl with d x in dx
-- ... | inl x₁ = let rec = bind-rec (abs M) f d (down occ) {!   !} 
--                in {!  rec !}
-- ... | inr x₁ = exfalso (x₁ refl)
-- bind-rec (app M N) f d (right .M occ) p = {!   !}
-- bind-rec (abs R) f {x} d (down occ) p with f x in fx
-- ... | abs M with abs≡inv p
-- ... | N = let rec = bind-rec R (lift f) (decAti x d) occ (N ! {!   !})
--           in exfalso {! occ  !}
-- bind-rec A f {x} d occ p with f x in fx
-- bind-rec A f {x} d occ p | var y with A | p
-- bind-rec A f {.z} d here p | var y | var z | q = refl
-- bind-rec (var x) f {x} d here p | app t1 t2 = refl
-- bind-rec (app s t) f {x} d (left  occ t) p | app t1 t2 with app≡inv p
-- ... | (p1 , p2) with d x in dx
-- ... | inr g = exfalso (g refl)
-- ... | inl refl = 
--   let g0 = λ y → case (λ q → app (var y) t ) (λ q → var y)
--       g = λ y → g0 y (d y)
--       f' = update f d t1
--       A' = s [ g ]
--       occ' = ∈[∈] occ g (left here t ∈≡ (~ ext (g0 x) refl ) )
--       br = bind-rec A' f' {x} d occ' {!   !}
--    in {!   !}
-- -- with g0 ← (λ y → case (λ _ → app (var y) t) (λ _ → var y))
-- --                with g ← (λ y → g0 y (d y))
-- --                with A' ← s [ g ]
-- --                with g0 x (inl refl)  | g x in gx
-- -- ... | u | q with occ' ← ∈[∈] occ g (left here t ∈≡ {!   !} )
-- --   = {!   !}
-- --                -- with br ← bind-rec A' f {x} d occ' {!   !}
-- --                with occ' ← ∈[∈] occ g (left here t ∈≡ {!   !} )
-- --                with br ← bind-rec (s [ g ]) f d occ' {!   !}
-- --                with s | occ
-- -- ... | var y | here = {! br   !}
--   -- with occ' ← ∈[∈] occ g (left here t ∈≡ {!   !}  ) = {!   !}
-- -- bind-rec (s [ g) ]) g {x} (right s occ) f {x} d oc' p = {!   !}
-- bind-rec .(app s _) f {x} d (right s occ) p | app t1 t2 = {!   !}
-- bind-rec A f {x} d occ p | abs t0 = {!   !}

bind-rec : ∀ {X Y : Set} (A : Λ X) (f : X → Λ Y) {x : X}
             → decAt x → x ∈ A → (A [ f ] ≡ f x) → A ≡ var x
bind-rec (var x) f d here p = refl
bind-rec (app A A₁) f {x} d occ p with f x
... | app P P₁ = {!   !}
bind-rec (abs A) f {x} d (down occ) p with f x
... | abs P with abs≡inv p
bind-rec (abs A) f {x} d (down occ) refl | abs .(bind (lift f) A) | refl = {!   !}

occurs-map : ∀ {X} (A : Λ (↑ X)) (B : Λ X) → A [ B ]ₒ ≡ B → ¬ (o ∈ A) → A ≡ Λ→ i B
occurs-map A B h nocc =
  let e0 : ∀ x → x ∈ A → var x ≡ (Λ→ i ∘ io var B) x
      e0 = (λ { (i x) → λ p → refl ; o → exfalso ∘ nocc })
      e1 = symm (bind-nat1 i (io var B))
      e2 = bind-occurs (var) (Λ→ i ∘ io var B) A e0
   in (~ bind-unit1 A) !  (e2 ! (e1 A ! ext (Λ→ i) h))

decTop : ∀ {X} (A : Λ (↑ X)) → A ≡ var o ⊔ ¬ (A ≡ var o)
decTop (var (i x)) = inr (λ { () })
decTop (var o) = inl refl
decTop (app A1 A2) = inr (λ { () })
decTop (abs A0) = inr (λ { () })

lercherEq3 : ∀ {X} (A : Λ (↑ X)) (B : Λ X) → A [ B ]ₒ ≡ B → A ≡ var o ⊔ A ≡ Λ→ i B
lercherEq3 A B e with decTop A
... | inl yes = inl yes
... | inr no  = inr (occurs-map A B e o∉A)
  where o∉A = λ occ → no (bind-rec A (io var B) decAto occ e)


lercherEq2gen : ∀ {X} (A1 A2 : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → bind f A1 ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2gen (var (i x)) A2 f fn p with ~ (fn x (down (left here A2) ∈≡ (~ p))) ! p
... | ()
lercherEq2gen (var o) A2 f fn p = refl
lercherEq2gen (abs (var (i (i x)))) A2 f fn p with abs≡inv p
... | M with  fn x (occIni (f (i x)) (left (down here) A2 ∈≡ (~ M)))
... | t with ~ (ext (Λ→ i) t) ! M
... | ()
lercherEq2gen (abs (var (i o))) A2 f fn p with abs≡inv p
...   | M = exfalso (o∉Λ→i (f o) (left (down here) A2 ∈≡ (~ M)))
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
      A = abs (app (var o) (var (i o)))
      br = bind-rec A (io var Q) {o} decAto (down (right (var o) here) ) (~ qPrf)
      contra : ∀ r → abs r ≡ var o → ⊥
      contra = λ { r () }
  in exfalso (contra _ br)

lercher : ∀ (P : Λ (↑ ⊥)) (Q : Λ ⊥) → P [ Q ]ₒ ≡ app (abs P) Q → abs P ≡ ω × Q ≡ ω
lercher (var (i x)) q prf = exfalso x
lercher (var o) q prf with prf
... | p =
  let A = app (abs (var o)) (var o)
      br = bind-rec A (io var q) {o} decAto (right (abs (var o)) here) (~ p)
      contra : ∀ {r1 r2} → app r1 r2 ≡ var o → ⊥
      contra = λ { () }
      in exfalso (contra br)
lercher (app P1 P2) Q prf =
   let (lhs , rhs) = app≡inv prf
       l1 = lercherEq2 _ _ _ lhs
       l2 = lercherEq3 P2 Q rhs
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
 