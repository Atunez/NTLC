open import BasicLogic
open import Lifting
open import Terms
open import Substitution

module Occurrences where

data _∈_ {X : Set} (x : X) : Λ X → Set where
  here  : x ∈ var x
  left  : ∀ {s : Λ X} → (x ∈ s) → (t : Λ X) → x ∈ app s t
  right : ∀ (s : Λ X) → {t : Λ X} → (x ∈ t) → x ∈ app s t
  down  : ∀ {r : Λ (↑ X)} → (i x ∈ r) → (x ∈ abs r)

_∉_ : ∀ {X : Set} (x : X) → Λ X → Set
x ∉ t = ¬ (x ∈ t)

_∈≡_ : ∀ {X} {x : X} {s t : Λ X} → x ∈ s → s ≡ t → x ∈ t
occ ∈≡ refl = occ

_∈→_ : ∀ {X Y} {x : X} {t : Λ X} → x ∈ t → (f : X → Y) → f x ∈ Λ→ f t
here ∈→ f = here
left occ t ∈→ f = left (occ ∈→ f) (Λ→ f t)
right s occ ∈→ f = right (Λ→ f s) (occ ∈→ f)
down occ ∈→ f = down (occ ∈→ ↑→ f)

-- _≃[_]_ : ∀ {X Y : Set} → (X → Y) → Λ X → (X → Y) → Set
-- f ≃[ t ] g = (∀ x → x ∈ t → f x ≡ g x)

-- ↓ is \d
_≃_↓_ : ∀ {X Y : Set} (f : X → Y) (P : X → Set) (g : X → Y) → Set
f ≃ P ↓ g = ∀ x → P x → f x ≡ g x

_≃_∋_ : ∀ {X Y : Set} (f : X → Y) (t : Λ X) (g : X → Y) → Set
-- f ≃ t ∋ g = ∀ x → x ∈ t → f x ≡ g x
f ≃ t ∋ g = f ≃ (λ x → x ∈ t) ↓ g

liftOverFV : ∀ {X Y : Set} {f g : X → Λ Y} {t : Λ (↑ X)}
             → f ≃ (abs t) ∋ g → lift f ≃ t ∋ lift g
liftOverFV p (i x) occ = ext Λ→i (p x (down occ))
liftOverFV p o occ = refl

bind-occurs : ∀ {X Y : Set} (f g : X → Λ Y) (t : Λ X) → f ≃ t ∋ g → t [ f ] ≡ t [ g ]
bind-occurs f g (var x)   fn = fn x here
bind-occurs f g (app s t) fn = app≡ (bind-occurs f g s (λ x z → fn x (left z t)))
                                    (bind-occurs f g t (λ x z → fn x (right s z)))
bind-occurs f g (abs r)   fn = abs≡ (bind-occurs (lift f) (lift g) r (liftOverFV fn))

map-occurs : ∀ {X Y : Set} (f g : X → Y) (t : Λ X)
                → f ≃ t ∋ g → Λ→ f t ≡ Λ→ g t
map-occurs f g (var x)   h = var≡ (h x here)
map-occurs f g (app s t) h = app≡ (map-occurs f g s λ x z → h x (left z t) )
                                  (map-occurs f g t (λ x z → h x (right s z)))
map-occurs f g (abs t)   h = abs≡ (map-occurs (↑→ f) (↑→ g) t h')
                  where h' = λ { (i x) occ → ext i (h x (down occ)) ; o occ → refl }

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
