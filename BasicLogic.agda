module BasicLogic where

-- IDENTITY AND COMPOSITION
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

exfalso : ∀ {X : Set} → ⊥ → X
exfalso ()

¬_ : Set → Set
¬ A = A → ⊥

-- PRODUCT AND SUM TYPES
infixl 15 _×_
infixl 14 _⊔_

record _×_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_

data _⊔_ (A B : Set) : Set where
  inl : A → A ⊔ B
  inr : B → A ⊔ B

case : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊔ B → C)
case f g (inl x) = f x
case f g (inr x) = g x

-- EQUALITY
-- ≡ is \==
infix 18 _≡_
data _≡_ {A : Set} : A → A → Set where
    refl : ∀ {a : A} → a ≡ a
{-# BUILTIN EQUALITY _≡_  #-}

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

-- EQUALITY OF FUNCTIONS
-- ≃ is \simeq or \~-
_≃_ : ∀ {X Y : Set} → (X → Y) → (X → Y) → Set
f ≃ g = ∀ x → f x ≡ g x

-- ≃ is reflexive
funcid : ∀ {X Y : Set} {f : X → Y} → f ≃ f
funcid = λ x → refl

-- ≃ is symmetric
symm : ∀ {X Y : Set} {f g : X → Y} → f ≃ g → g ≃ f
symm fg x = ~ fg x

-- ≃ is transitive
tran : ∀ {X Y : Set} {f g h : X → Y} → f ≃ g → g ≃ h → f ≃ h
tran fg gh x = fg x ! gh x

-- functions are extensional
ext : ∀ {X Y : Set} (f : X → Y) {x y : X} → x ≡ y → f x ≡ f y
ext f refl = refl

iext : ∀ {X Y : Set} {f : X → Y} {x y : X} → x ≡ y → f x ≡ f y
iext refl = refl

ext≃ : ∀ {X Y : Set} {f g : X → Y} → f ≃ g → ∀ {x y : X} → x ≡ y → f x ≡ g y
ext≃ fg refl = fg _
