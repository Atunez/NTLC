open import BasicLogic
open import Lifting
open import Terms

module Substitution where

-- The lifting of a function
lift : ∀ {X Y : Set} → (X → Λ Y) → (↑ X → Λ (↑ Y))
lift f (i x) = Λ→i (f x)
lift f o = var o
-- lift f = io (Λ→i ∘ f) (var o)

lift≃ : ∀ {X Y : Set} → {f g : X → Λ Y} (fg : f ≃ g) → lift f ≃ lift g
lift≃ fg (i x) = ext Λ→i (fg x)
lift≃ fg o = refl

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
bind-nat1 y f (abs t) =
  abs≡ ( bind-nat1 (↑→ y) (lift f) t
  ! bind-ext  ( λ { o → refl ; (i x) → tran (symm (Λ-func (↑→ y) i)) (tran (λ x → refl) (Λ-func i y)) (f x) } ) t)

{-
bind-nat2 : ∀ {X X' Y : Set} (x : X → X') (f : X' → Λ Y)
              → bind (f ∘ x) ≃ bind f ∘ Λ→ x
bind-nat2 x f (var y) = refl
bind-nat2 x f (app t₀ t₁) = app≡ (bind-nat2 x f t₀) (bind-nat2 x f t₁)
bind-nat2 x f (abs t) =  abs≡ ( bind-ext lemma t ! bind-nat2 (↑→ x) (Λ↑ ∘ ↑→ f) t )
  where lemma = λ y → ext Λ↑ (↑-func f x y )

-- Interaction between bind and i (Or more generally, between bind and X → ↑ X)
bind↑inter : ∀ {Y Z : Set} (g : Y → Λ Z) (f : Z → ↑ Z) (p : Y → ↑ Y) (x : Λ Y)
  → (Λ→ f) ∘ g ≃ (Λ↑ ∘ ↑→ g) ∘ p → Λ→ f (bind g x) ≡ bind (Λ↑ ∘ ↑→ g) (Λ→ p x)
bind↑inter g f p (var x) prf = prf x
bind↑inter g f p (app x x₁) prf = app≡ (bind↑inter g f p x prf) (bind↑inter g f p x₁ prf)
bind↑inter g f p (abs x) prf = abs≡ (bind↑inter (Λ↑ ∘ ↑→ g) (↑→ f) (↑→ p) x
  λ {(i x) → (~ Λ-func (↑→ f) i (g x)) ! (Λ-func i f (g x) ! ext (Λ→ i) (prf x)) ; o → refl})

bind↑-dist : ∀ {X Y : Set} (g : X → Λ Y) → Λ↑ ∘ ↑→ (bind g) ≃ bind (Λ↑ ∘ ↑→ g) ∘ Λ↑
bind↑-dist g = λ { (i x) -> bind↑inter g i i x (λ x → refl) ; o -> refl}

-- -- Associativity of bind
bind-law : ∀ {X Y Z : Set} (f : X → Λ Y) (g : Y → Λ Z)
         → bind (bind g ∘ f) ≃ (bind g ∘ bind f)
bind-law f g (var x) = refl
bind-law f g (app t₀ t₁) = app≡ (bind-law f g t₀) (bind-law f g t₁)
bind-law f g (abs t) = abs≡ (bind-ext
  (λ {(i x) → bind↑inter g i i (f x) (λ x → refl) ; o → refl}) t
  ! bind-law (Λ↑ ∘ ↑→ f) (Λ↑ ∘ ↑→ g) t)

-- μ is mu
-- MULTIPLICATION: Monad Structure on Λ
Λμ : ∀ {X} → Λ (Λ X) → Λ X
Λμ = bind id

-- SUBSTITUTION
--   Given M ∈ Λ {x1,..,xk+1}, and N ∈ Λ {x1,..,xk},
--   produce M[xk+1 := N] ∈ Λ {x1,..,xk}
infixr 30 _[_]
_[_] : ∀ {X : Set} → Λ (↑ X) → Λ X → Λ X

M [ N ] = bind (io var N) M

io-var-nat : ∀ {X Y : Set} (f : X → Y) (M : Λ X)
            → Λ→ f ∘ io var M ≃ io var (Λ→ f M) ∘ ↑→ f
io-var-nat f M = λ {(i x) → refl ; o → refl}

-- Substitution Lemma
subst→ : ∀ {X Y : Set} (f : X → Y) (M : Λ (↑ X)) (N : Λ X)
           → Λ→ f (M [ N ]) ≡ Λ→ (↑→ f) M [ Λ→ f N ]
subst→ f M N =   bind-nat1 f (io var N) M
               ! bind-ext (io-var-nat f N) M
               ! bind-nat2 (↑→ f) (io var (Λ→ f N)) M

mapIsBind : ∀ {X Y : Set} → (f : X → Y) → Λ→ f ≃ bind (var ∘ f)
mapIsBind f (var x) = refl
mapIsBind f (app t₀ t₁) = app≡ (mapIsBind f t₀ ) (mapIsBind f t₁)
mapIsBind f (abs t) = abs≡ (mapIsBind (↑→ f) t ! bind-ext (λ {(i x) → refl ; o → refl} ) t )

bind-unit1 : ∀ {X : Set} (t : Λ X) → bind var t ≡ t
bind-unit1 (var x) = refl
bind-unit1 (app t t₁) = app≡ (bind-unit1 t) (bind-unit1 t₁)
bind-unit1 {X} (abs t) = abs≡ (bind-ext (λ {(i x) → refl ; o → refl}) t ! bind-unit1 t) -- (bind-ext {! symm var-lifting   !} {! t   !})
-}
