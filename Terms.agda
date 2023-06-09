open import Base

module Terms where
  -- LAMBDA TERMS
  -- Λ is \GL
  -- Λ as a nested type
  -- Λ : Set → Set
  -- For a set X = {x1,..,xk}, Λ X = terms with free variables in the set X
  data Λ (X : Set) : Set where
    var : X → Λ X
    app : Λ X → Λ X → Λ X
    abs : Λ (↑ X) → Λ X
  open Λ

  -- Λ⁰ is \GL\^0
  -- Λ⁰ is the set of *closed* λ-terms
  Λ⁰ : Set
  Λ⁰ = Λ ⊥

  -- Congruence
  var≡ : ∀ {X} {x y : X} → x ≡ y → var x ≡ var y
  var≡ = ext var

  app≡ : ∀ {X} {s s' t t' : Λ X} → s ≡ s' → t ≡ t' → app s t ≡ app s' t'
  app≡ refl refl = refl

  abs≡ : ∀ {X} {s t : Λ (↑ X)} → s ≡ t → abs s ≡ abs t
  abs≡ = ext abs


  app≡inv : ∀ {X} {M M' N N' : Λ X} → app M N ≡ app M' N' → M ≡ M' × N ≡ N'
  app≡inv refl = ( refl , refl )

  abs≡inv : ∀ {X} {M M' : Λ (↑ X)} → abs M ≡ abs M' → M ≡ M'
  abs≡inv refl = refl

  var≡inv : ∀ {X} {M M' : X} → var M ≡ var M' → M ≡ M'
  var≡inv refl = refl

  -- Λ is a functor, too. (it has a map function)
  Λ→ : ∀ {X Y : Set} → (X → Y) → Λ X → Λ Y
  Λ→ f (var x)     = var (f x)
  Λ→ f (app M₀ M₁) = app (Λ→ f M₀) (Λ→ f M₁)
  Λ→ f (abs M)     = abs (Λ→ (↑→ f) M)


  Λ-ext : ∀ {X Y : Set} {f g : X → Y} → f ≃ g → Λ→ f ≃ Λ→ g
  Λ-ext fg (var x)     = var≡ (fg x)
  Λ-ext fg (app t₀ t₁) = app≡ (Λ-ext fg t₀) (Λ-ext fg t₁)
  Λ-ext fg (abs t)     = abs≡ (Λ-ext (↑-ext fg) t)

  Λ-func :  ∀ {X Y Z : Set} (f : Y → Z) (g : X → Y)
             → Λ→ (f ∘ g) ≃ (Λ→ f ∘ Λ→ g)
  Λ-func f g (var x)     = refl
  Λ-func f g (app t₀ t₁) = app≡ (Λ-func f g t₀) (Λ-func f g t₁)
  Λ-func f g (abs t)     = abs≡ ( Λ-ext (↑-func f g) t
                                ! Λ-func (↑→ f) (↑→ g) t )

  -- Helper function for proofs involving repeated functoriality
  Λ→-aux : ∀ {X Y Z : Set} (f : Y → Z) (g : X → Y) (h : X → Z)
          → (f ∘ g) ≃ h → ((Λ→ f) ∘ (Λ→ g)) ≃ Λ→ h
  Λ→-aux f g h fgh x = (~ (Λ-func f g x)) ! (Λ-ext fgh x)

  -- This function takes either a λ-term M ∈ Λ(x1,..,xk),
  -- or a special symbol o ∈ 1,
  -- and returns a λ-term ∈ Λ(x1,..,xk+1)
  Λ↑ : ∀ {X : Set} → ↑ (Λ X) → Λ (↑ X)
  Λ↑ = io (Λ→ i) (var o)

  Λ↑-ext : ∀ {X : Set} {s t : ↑ (Λ X)} → s ≡ t → Λ↑ s ≡ Λ↑ t
  Λ↑-ext = ext Λ↑

  Λ↑-nat : ∀ {X Y : Set} (f : X → Y) → Λ→ (↑→ f) ∘ Λ↑ ≃ Λ↑ ∘ ↑→ (Λ→ f)
  Λ↑-nat f (i (var x)) = refl
  Λ↑-nat f (i (app t₀ t₁)) = app≡ (Λ↑-nat f (i t₀)) (Λ↑-nat f (i t₁))
  Λ↑-nat f (i (abs t)) =
    abs≡ ( Λ→-aux (↑→ (↑→ f)) (↑→ i) (↑→ (↑→ f ∘ i)) (symm (↑-func (↑→ f) i)) t
         ! ~ Λ→-aux (↑→ i) (↑→ f) _ (symm (↑-func i f ) ) t )
  Λ↑-nat f o = refl