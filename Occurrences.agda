open import Base
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

Λ→Inj : ∀ {X Y} (f : X → Y) → isInj f → isInj (Λ→ f)
Λ→Inj f inj {var x} {var x₁} p = ext var (inj (var≡inv p))
Λ→Inj f inj {app x1 x2} {app x3 x4} p = app≡ (Λ→Inj f inj (_×_.fst pinv)) (Λ→Inj f inj (_×_.snd pinv)) where pinv = app≡inv p
Λ→Inj f inj {abs x1} {abs x2} p = abs≡ (Λ→Inj (↑→ f) (↑→Inj f inj) (abs≡inv p))

occInj : ∀ {X Y} (f : X → Y) (finj : isInj f) (x : X) (t : Λ X) → f x ∈ Λ→ f t → x ∈ t
occInj f finj x (var y) occ with f x | f y | finj {x} {y}
occInj f finj x (var y) here | z | .z | q with q refl
... | refl = here
occInj f finj x (app t1 t2) (left occ .(Λ→ f t2)) = left (occInj f finj x t1 occ ) t2
occInj f finj x (app t1 t2) (right .(Λ→ f t1) occ) = right t1 (occInj f finj x t2 occ)
occInj f finj x (abs t0) (down occ) =  down (occInj (↑→ f) (↑→Inj f finj) (i x) t0 occ)

InjOcc : ∀ {X Y} (f : X → Y) (finj : isInj f) (x : X) (t : Λ X) → x ∈ t → f x ∈ Λ→ f t
InjOcc f finj x (var .x) here = here
InjOcc f finj x (app y y₁) (left occ .y₁) = left (InjOcc f finj x y occ) (Λ→ f y₁)
InjOcc f finj x (app y y₁) (right .y occ) = right (Λ→ f y) (InjOcc f finj x y₁ occ)
InjOcc f finj x (abs y) (down occ) = down (InjOcc (↑→ f) (↑→Inj f finj) (i x) y occ)

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

x∉Λ→i : ∀ {X} (s : Λ X) (x : X) → x ∉ s → ¬ ((i x) ∈ Λ→ i s)
x∉Λ→i s x nocc occ = nocc (occInj i iInj x s occ)

var∈≡ : ∀ {X} (M : Λ X) (x : X) → M ≡ var x → x ∈ M
var∈≡ M x refl = here

∈[∈] : ∀ {X} {x : X} {s : Λ X} → x ∈ s → (f : X → Λ X) → x ∈ f x → x ∈ (s [ f ])
∈[∈] here f oc2 = oc2
∈[∈] (left oc1 t) f oc2 = left (∈[∈] oc1 f oc2) (bind f t)
∈[∈] (right s oc1) f oc2 = right (bind f s) (∈[∈] oc1 f oc2)
∈[∈] (down oc1) f oc2 = down (∈[∈] oc1 (lift f) (oc2 ∈→ i))

∈[f] : ∀ {X} (M : Λ (↑ (↑ X))) (N : Λ X) (f : ↑ X → Λ X) (x : X) → x ∈ f (i x) → (i (i x)) ∈ M → (i x) ∈ (M [ (lift f) ])
∈[f] (var .(i (i x))) N f x fn here = fn ∈→ i
∈[f] (app M M₁) N f x fn (left occ .M₁) = left (∈[f] M N f x fn occ) _
∈[f] (app M M₁) N f x fn (right .M occ) = right _ (∈[f] M₁ N f x fn occ)
∈[f] (abs M) N f x fn (down occ) = down (∈[f] M (Λ→ i N) (lift f) (i x) (fn ∈→ i) occ)

∈[∈]2 : ∀ {X Y} {x : X} {y : Y} {s : Λ X} → x ∈ s → (f : X → Λ Y) → y ∈ f x → y ∈ (s [ f ])
∈[∈]2 here f occ2 = occ2
∈[∈]2 (left occ t) f occ2 = left (∈[∈]2 occ f occ2) (bind f t)
∈[∈]2 (right s occ) f occ2 = right (bind f s) (∈[∈]2 occ f occ2)
∈[∈]2 (down occ) f occ2 = down (∈[∈]2 occ (lift f) (occ2 ∈→ i))

-- ∈[∈]3 : ∀ {X Y} {x : X} {y : Y} {s : Λ X} → (f : X → Λ Y) → y ∈ f x → y ∈ (s [ f ]) → x ∈ s
-- ∈[∈]3 f occ1 occ2 = {! occ1  !}

∈∉ : ∀ {X} {x : X} {s : Λ X} → x ∈ s → x ∉ s → ⊥
∈∉ occ nocc = nocc occ

∉[∈] : ∀ {X} {x : X} (s : Λ (↑ X)) → (i x) ∉ s → (f : ↑ X → Λ X) → (∀ y → y ∈ s → x ∉ f y) → x ∉ (s [ f ])
∉[∈] (var x) nocc f fn occ = fn x here occ
∉[∈] (app M M₁) nocc f fn (left occ .(bind f M₁)) = ∉[∈] M (λ z → nocc (left z M₁)) f (λ y z → fn y (left z M₁)) occ
∉[∈] (app M M₁) nocc f fn (right .(bind f M) occ) = ∉[∈] M₁ (λ z → nocc (right M z)) f (λ y z → fn y (right M z)) occ
∉[∈] (abs M) nocc f fn (down occ) = ∉[∈] M (λ q → nocc (down q)) (lift f) (λ {(i x) → λ q q2 → fn x (down q) (occIni (f x) q2)
                                                                            ; o → λ _ ()}) occ

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

-- ∈[∋] : ∀ {X} (M : Λ (↑ X)) (N : Λ (↑ X)) (f : ↑ X → Λ (↑ X)) → M [ f ] ≡ N → o ∈ N → (∀ x → x ∈ M → (x ≡ o × f x ≡ var o) ⊔ (f x ≡ )) → o ∈ M
-- ∈[∋] (var x) .(var x [ f ]) f refl occ fn = case (λ {(refl , snd) → here}) (λ {q → {!   !}}) (fn x here)
-- ∈[∋] (app M M₁) .(app M M₁ [ f ]) f refl occ fn = {!   !}
-- ∈[∋] (abs M) .(abs M [ f ]) f refl occ fn = {!   !}


-- strTerm : ∀ {X} (M : Λ (↑ X)) → o ∉ M → Λ X
-- strTerm (var (i x)) nocc = var x
-- strTerm (var o) nocc = exfalso (nocc here)
-- strTerm (app M1 M2) nocc = app (strTerm M1 λ z → nocc (left z M2) ) (strTerm M2 λ z → nocc (right M1 z) )
-- strTerm (abs M) nocc = {!   !}

-- strProof : ∀ {X} (M : Λ (↑ X)) {x : ↑ X} → x ∉ M → M ≡ Λ
