module Subterms where

data _∈_ {X : Set} (x : X) : Λ X → Set where
  here  : x ∈ var x
  left  : ∀ {s : Λ X} → (x ∈ s) → (t : Λ X) → x ∈ app s t
  right : ∀ (s : Λ X) → {t : Λ X} → (x ∈ t) → x ∈ app s t
  down  : ∀ {r : Λ (↑ X)} → (i x ∈ r) → (x ∈ abs r)

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

lercherEq3 : ∀ {X} (A : Λ X) (B : Λ (↑ X)) → B [ A ] ≡ A → B ≡ var o ⊔ B ≡ Λ→ i A
lercherEq3 A B e with decΛ decAto B
...                 | inr no  = inr (occurs-map B A e no )
...                 | inl yes = inl (occursLemmaLen (io var A) B o yes (≤≡ (ext lenTerm e)))


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
