module Cycles where

open import Lambda public

lenTerm : ∀ {X : Set} → Λ X → Nat
lenTerm (var x) = O
lenTerm (app x x₁) = S (lenTerm x ++ lenTerm x₁)
lenTerm (abs x) = S (lenTerm x)

data _∈_ {X : Set} (x : X) : Λ X → Set where
  here  : x ∈ var x
  left  : ∀ {s : Λ X} → (x ∈ s) → (t : Λ X) → x ∈ app s t
  right : ∀ (s : Λ X) → {t : Λ X} → (x ∈ t) → x ∈ app s t
  down  : ∀ {r : Λ (↑ X)} → (i x ∈ r) → (x ∈ abs r)

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


mapKeepsLength : ∀ {X Y : Set} → (f : X → Y) → (M : Λ X) → lenTerm M ≡ lenTerm (Λ→ f M)
mapKeepsLength f (var x) = refl
mapKeepsLength f (app M₁ M₂) = ext S (tran++ (mapKeepsLength f M₁)  (mapKeepsLength f M₂) )
mapKeepsLength f (abs M₀) = ext S (mapKeepsLength (↑→ f) M₀ )

ω : Λ ⊥
ω = abs (app (var o) (var o))

bind-occurs : ∀ {X Y : Set} (f g : X → Λ Y) (t : Λ X)
                → (∀ x → x ∈ t → f x ≡ g x) → bind f t ≡ bind g t
bind-occurs f g (var x) fn = fn x here
bind-occurs f g (app t t₁) fn = app≡ (bind-occurs f g t (λ x z → fn x (left z t₁))) (bind-occurs f g t₁ (λ x z → fn x (right t z)))
bind-occurs f g (abs t) fn = abs≡ (bind-occurs (Λ↑ ∘ ↑→ f) (Λ↑ ∘ ↑→ g) t λ {(i x) → λ q → ext (Λ↑ ∘ i) (fn x (down q)) ; o → λ _ → refl})

map-occurs : ∀ {X Y : Set} (f g : X → Y) (t : Λ X)
                → (∀ x → x ∈ t → f x ≡ g x) → Λ→ f t ≡ Λ→ g t
map-occurs f g t h =
  let f' = mapIsBind f
      g' = symm (mapIsBind g)
      h' = (λ x occ → ext var (h x occ) )
   in f' t ! bind-occurs (var ∘ f) (var ∘ g) t h' ! g' t

occurs-map : ∀ {X} (A : Λ (↑ X)) (B : Λ X) → A [ B ] ≡ B → ¬ (o ∈ A) → A ≡ Λ→ i B
occurs-map A B h nocc =
  let e0 : ∀ x → x ∈ A → var x ≡ (Λ→ i ∘ io var B) x
      e0 = (λ { (i x) → λ p → refl ; o → exfalso ∘ nocc })
      e1 = symm (bind-nat1 i (io var B))
      e2 = bind-occurs (var) (Λ→ i ∘ io var B) A e0
   in (~ bind-unit1 A) !  (e2 ! (e1 A ! ext (Λ→ i) h))

occursLemmaLen : ∀ {X} {Y} (f : X → Λ Y) (A : Λ X) (x : X) → x ∈ A → lenTerm (bind f A) ≤ lenTerm (f x) → A ≡ var x
occursLemmaLen f .(var x) x here l = refl
occursLemmaLen f (app s t) x (left occ t) l =
  let x1 = occursLemmaLen f s x occ
      x2 = add>S (lenTerm (bind f s)) (lenTerm (bind f t))
      x3 = x1 (lelte x2 l)
      x4 = ≤-eq {l = lenTerm (bind f s)} l (ext lenTerm (~ ext (bind f) x3))
   in exfalso (lestrict x2 x4)
occursLemmaLen f (app s t) x (right s occ) l =
  let x1 = occursLemmaLen f t x occ
      x2 = add>S (lenTerm (bind f t)) (lenTerm (bind f s))
      x3 = x1 (lelte x2 (++S≤ {n = lenTerm (bind f t)} l))
      x4 = ≤-eq (++S≤ {n = lenTerm (bind f t)} l) (ext lenTerm (~ ext (bind f) x3))
   in exfalso (lestrict x2 x4)
occursLemmaLen f (abs r) x (down occ) l =
  let x1 = occursLemmaLen (Λ↑ ∘ ↑→ f) r (i x) occ
      x2 = mapKeepsLength i (f x)
      x3 = lelte (<S _) (≤-eq l x2)
      x4 = x1 x3
      x5 = ≡≤ (ext S (x2 ! ext lenTerm (ext (bind (Λ↑ ∘ ↑→ f)) (~ x4)) ) ) l
   in exfalso (lestrict (<S (lenTerm (f x))) x5)

lercherEq3 : ∀ {X} (A : Λ X) (B : Λ (↑ X)) → B [ A ] ≡ A → B ≡ var o ⊔ B ≡ Λ→ i A
lercherEq3 A B e with decΛ decAto B
...                 | inr no  = inr (occurs-map B A e no )
...                 | inl yes = inl (occursLemmaLen (io var A) B o yes (≤≡ (ext lenTerm e)))


equalLength : ∀ {X : Set} (M N : Λ X) → M ≡ N → ¬ (lenTerm M ≡ lenTerm N) → ⊥
equalLength M .M refl p = p refl

isInj : ∀ {X Y : Set} → (X → Y) → Set
isInj f = ∀ {x1 x2} → f x1 ≡ f x2 → x1 ≡ x2

iInj : ∀ {X} → isInj (i {X})
iInj refl = refl

↑→Inj : ∀ {X Y} (f : X → Y) → isInj f → isInj (↑→ f)
↑→Inj f inj {i x} {i x₁} p with iInj p
...                           | q = ext i (inj q)
↑→Inj f inj {o} {o} refl = refl

occInj : ∀ {X Y} (f : X → Y) (finj : isInj f) (x : X) (t : Λ X) → f x ∈ Λ→ f t → x ∈ t
occInj f finj x (var y) occ with f x | f y | finj {x} {y}
occInj f finj x (var y) here | z | .z | q with q refl
... | refl = here
occInj f finj x (app t1 t2) (left occ .(Λ→ f t2)) = left (occInj f finj x t1 occ ) t2
occInj f finj x (app t1 t2) (right .(Λ→ f t1) occ) = right t1 (occInj f finj x t2 occ)
occInj f finj x (abs t0) (down occ) =  down (occInj (↑→ f) (↑→Inj f finj) (i x) t0 occ)

occIni : ∀ {X} (s : Λ X) {x : X} → i x ∈ Λ→ i s → x ∈ s
occIni s occ = occInj i iInj _ s occ

notoccursΛ→  : ∀ {X Y} (f : X → Y) (y : Y) → (∀ x → ¬ (f x ≡ y) ) → ∀ t → ¬ (y ∈ Λ→ f t)
notoccursΛ→ f .(f x) h (var x) here = h x refl
notoccursΛ→ f y h (app t1 t2) (left occ .(Λ→ f t2)) = notoccursΛ→ f y h t1 occ
notoccursΛ→ f y h (app t1 t2) (right .(Λ→ f t1) occ) = notoccursΛ→ f y h t2 occ
notoccursΛ→ f y h (abs t0) (down occ) = notoccursΛ→ (↑→ f) (i y) h' t0 occ
  where h' : ∀ x → ¬ (↑→ f x ≡ i y)
        h' o ()
        h' (i x) e = h x (iInj e)

o∉Λ→i : ∀ {X} (s : Λ X) → ¬ (o ∈ Λ→ i s)
o∉Λ→i s = notoccursΛ→ i o (λ x → λ {()} ) s

∈≡ : ∀ {X} {x : X} {s t : Λ X} → x ∈ s → s ≡ t → x ∈ t
∈≡ occ refl = occ

lercherEq2gen : ∀ {X} (A1 A2 : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → bind f A1 ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2gen (var (i x)) A2 f fn p = 
 let t = ~ (fn x (∈≡ (down (left here A2)) (~ p))) ! p
 in exfalso (equalLength _ _ t (λ {()}))
lercherEq2gen (var o) A2 f fn p = refl
lercherEq2gen (abs (var (i (i x)))) A2 f fn p with abs≡inv p
...   | M = let t = fn x (occIni (f (i x)) (∈≡ (left (down here) A2) (~ M)))
                pt = ~ (ext (Λ→ i) t) ! M
            in exfalso (equalLength _ _ pt λ ())
lercherEq2gen (abs (var (i o))) A2 f fn p with abs≡inv p
...   | M = exfalso (o∉Λ→i (f o) (∈≡ (left (down here) A2) (~ M)))
lercherEq2gen (abs (app A1 A3)) A2 f fn p with app≡inv (abs≡inv p)
...         | (p1 , p2) = let g = λ x → io (Λ→ i) (var o) (↑→ f x)
                              gn = λ {o → λ q → exfalso (o∉Λ→i (f o) q); (i x) → λ q → ext (Λ→ i) (fn x (occIni (f (i x)) q))}
                              rec = lercherEq2gen A1 A3 g gn p1 
                            in ~ p1 ! ext (bind g) rec

lercherEq2 : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X)→ A1 [ B ] ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2 A1 A2 B p = lercherEq2gen A1 A2 (io var B) (λ x _ → refl) p

lercherHelper : ∀ (P1 P2 : Λ (↑ ⊥)) (Q : Λ ⊥) → P1 ≡ var o → P2 ≡ var o ⊔ P2 ≡ Λ→ i Q → (app P1 P2) [ Q ] ≡ app (abs (app P1 P2)) Q → abs (app P1 P2) ≡ ω × Q ≡ ω
lercherHelper .(var o) .(var o) Q refl (inl refl) p3 = refl , _×_.fst (app≡inv p3)
lercherHelper .(var o) .(Λ→ i Q) Q refl (inr refl) p3 =
  let qPrf = _×_.fst (app≡inv p3)
  in exfalso (equalLength _ _ qPrf (λ q → numbersDontAdd (mapKeepsLength i Q) q))

lercher : ∀ (P : Λ (↑ ⊥)) (Q : Λ ⊥) → P [ Q ] ≡ app (abs P) Q → abs P ≡ ω × Q ≡ ω
lercher (var (i x)) q prf = exfalso x
lercher (var o) q prf = exfalso (<-irrefl lt (<-eq (<<S lt) (ext (lenTerm) (~ prf)))) where lt = lenTerm q
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
