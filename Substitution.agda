open import Base

module Substitution where

-- The lifting of a function
lift : ∀ {X Y : Set} → (X → Λ Y) → (↑ X → Λ (↑ Y))
lift f (i x) = Λ→i (f x)
lift f o = var o
-- lift f = io (Λ→i ∘ f) (var o)

lift≃ : ∀ {X Y : Set} → {f g : X → Λ Y} (fg : f ≃ g) → lift f ≃ lift g
lift≃ fg (i x) = ext Λ→i (fg x)
lift≃ fg o = refl

Λ↑ : ∀ {X : Set} → ↑ (Λ X) → Λ (↑ X)
Λ↑ = lift id 

-- BIND: The generic substitution operator:
--   Given M ∈ Λ X, where X = {x1,..,xk}, and
--   a function f : X → Λ Y, assigning to each xi ∈ X
--     a term Ni ∈ Λ Y, where Y = {y1,..,ym},
--   produce a term M [xi := Ni]_{i=1..k} ∈ Λ Y
bind : ∀ {X Y : Set} → (X → Λ Y) → Λ X → Λ Y
bind f (var x)     = f x
bind f (app t₀ t₁) = app (bind f t₀) (bind f t₁)
bind f (abs t)     = abs (bind (lift f) t)

bind-ext : ∀ {X Y : Set} {f g : X → Λ Y} → f ≃ g → bind f ≃ bind g
bind-ext fg (var x)     = fg x
bind-ext fg (app t₀ t₁) = app≡ (bind-ext fg t₀) (bind-ext fg t₁)
bind-ext fg (abs t)     = abs≡ (bind-ext (lift≃ fg) t)
-- bind-ext fg (abs t) = abs≡ (bind-ext (ext Λ↑  ∘  ↑-ext fg) t)

_[_] : ∀ {X Y : Set} → Λ X → (X → Λ Y) → Λ Y
M [ f ] = bind f M

-- ₒ is \_o
-- SUBSTITUTION
--   Given M ∈ Λ {x1,..,xk+1}, and N ∈ Λ {x1,..,xk},
--   produce M[xk+1 := N] ∈ Λ {x1,..,xk}
infixr 30 _[_]ₒ
_[_]ₒ : ∀ {X : Set} → Λ (↑ X) → Λ X → Λ X
M [ N ]ₒ = M [ io var N ]

bind-unit1 : ∀ {X : Set} (t : Λ X) → bind var t ≡ t
bind-unit1 (var x) = refl
bind-unit1 (app t t₁) = app≡ (bind-unit1 t) (bind-unit1 t₁)
bind-unit1 {X} (abs t) = abs≡ (bind-ext (λ {(i x) → refl ; o → refl}) t ! bind-unit1 t)

-- LAWS OF BIND
-- Naturality of bind
bind-nat1 : ∀ {X Y Y' : Set} (y : Y → Y') (f : X → Λ Y)
           → Λ→ y ∘ bind f ≃ bind (Λ→ y ∘ f)
bind-nat1 y f (var x) = refl
bind-nat1 y f (app t₀ t₁) = app≡ (bind-nat1 y f t₀) (bind-nat1 y f t₁)
bind-nat1 y f (abs t) = abs≡ (bind-nat1 (↑→ y) (lift f) t !
                      bind-ext (λ {(i x) → ~ (Λ-func (↑→ y) i (f x)) ! Λ-func i y (f x) ; o → refl}) t)


-- Following lemmas needed in reductions
bind-nat2 : ∀ {X X' Y : Set} (x : X → X') (f : X' → Λ Y)
              → bind (f ∘ x) ≃ bind f ∘ Λ→ x
bind-nat2 x f (var y) = refl
bind-nat2 x f (app t₀ t₁) = app≡ (bind-nat2 x f t₀) (bind-nat2 x f t₁)
bind-nat2 x f (abs t) = abs≡ (bind-ext (λ {o → refl; (i x) → refl}) t ! bind-nat2 (↑→ x) (lift f) t)

-- Substitution Lemma
subst→ : ∀ {X Y : Set} (f : X → Y) (M : Λ (↑ X)) (N : Λ X)
           → Λ→ f (M [ N ]ₒ) ≡ Λ→ (↑→ f) M [ Λ→ f N ]ₒ
subst→ f M N = bind-nat1 f (io var N) M
              ! bind-ext (λ {o → refl; (i x) → refl}) M
              ! bind-nat2 (↑→ f) (io var (Λ→ f N)) M

-- -- Associativity of bind
bind-law : ∀ {X Y Z : Set} (f : X → Λ Y) (g : Y → Λ Z)
         → bind (bind g ∘ f) ≃ (bind g ∘ bind f)
bind-law f g (var x) = refl
bind-law f g (app t₀ t₁) = app≡ (bind-law f g t₀) (bind-law f g t₁)
bind-law f g (abs t) = abs≡ (bind-ext (λ {o → refl; (i x) → bind-nat1 i g (f x) ! bind-nat2 i (lift g) (f x)}) t ! bind-law (lift f) (lift g) t)

-- μ is mu
-- MULTIPLICATION: Monad Structure on Λ
Λμ : ∀ {X} → Λ (Λ X) → Λ X
Λμ = bind id

{-

mapIsBind : ∀ {X Y : Set} → (f : X → Y) → Λ→ f ≃ bind (var ∘ f)
mapIsBind f (var x) = refl
mapIsBind f (app t₀ t₁) = app≡ (mapIsBind f t₀ ) (mapIsBind f t₁)
mapIsBind f (abs t) = abs≡ (mapIsBind (↑→ f) t ! bind-ext (λ {(i x) → refl ; o → refl} ) t )

-}
