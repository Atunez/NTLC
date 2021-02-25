module SimpleLambda where

-- BASIC COMBINATORS
-- ∘ is \o
infixl 30 _∘_
-- function composition
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

-- identity function
id : ∀ {A : Set} → A → A
id x = x


-- EMPTY AND UNIT TYPE
-- ⊥ is \bot
-- The Empty type
data ⊥ : Set where
-- ⊤ is \top
-- The Unit type
data ⊤ : Set where
  tt : ⊤

module Equality where
  -- EQUALITY
  -- ≡ is \==
  infix 18 _≡_
  data _≡_ {A : Set} : A → A → Set where
    refl : ∀ {a : A} → a ≡ a

  -- Transport of properties over equality (≡-elim)
  transp : ∀ {A : Set} (B : A → Set) {a1 a2 : A} → a1 ≡ a2 → B a1 → B a2
  transp B refl b = b

  -- Symmetry
  ~_ : ∀ {X} {x y : X} → x ≡ y → y ≡ x
  ~ refl = refl

  infixl 10 _!_
  -- Transitivity
  _!_ : ∀ {X} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
  refl ! q = q

  -- Equality of functions
  -- ≃ is \simeq or \~-
  _≃_ : ∀ {X Y : Set} → (X → Y) → (X → Y) → Set
  f ≃ g = ∀ x → f x ≡ g x

  symm : ∀ {X Y : Set} {f g : X → Y} → f ≃ g → g ≃ f
  symm fg x = ~ fg x

  tran : ∀ {X Y : Set} {f g h : X → Y} → f ≃ g → g ≃ h → f ≃ h
  tran fg gh x = fg x ! gh x

  ext : ∀ {X Y : Set} (f : X → Y) {x y : X} → x ≡ y → f x ≡ f y
  ext f refl = refl

  ext≃ : ∀ {X Y : Set} {f g : X → Y} → f ≃ g → ∀ {x y : X} → x ≡ y → f x ≡ g y
  ext≃ fg refl = fg _

  -- random-lemma: ∀ {X Y : Set} {f g : X → Y} {x : X} → f ≡ g → f x ≡ g x
  -- random-lemma input = ?
open Equality