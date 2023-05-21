open import Equality

module Lifting where
  -- LIFTING MONAD
  -- ↑ is \u
  -- ↑ X = X + 1 (in types) = X ⊔ {*} (in sets) = Maybe X (in Haskell)
  data ↑ (X : Set) : Set where
    i : X → ↑ X    -- in1 x  = inclusion of X into ↑ X =  "Just x" in Haskell
    o : ↑ X        -- in2 tt = inclusion of 1 into ↑ X = "Nothing" in Haskell


  
  io : ∀ {X Y : Set} → (X → Y) → Y → ↑ X → Y
  io f y (i x) = f x
  io f y o = y

  -- ↑ is a functor: it has a map function
  ↑→ : ∀ {X Y} → (X → Y) → ↑ X → ↑ Y
  ↑→ f (i x) = i (f x)
  ↑→ f o = o

  ↑-ext : ∀ {X Y : Set} {f g : X → Y} → f ≃ g → ↑→ f ≃ ↑→ g
  ↑-ext fg (i x) = ext i (fg x)
  ↑-ext fg o = refl

  ↑-func : ∀ {X Y Z : Set} (f : Y → Z) (g : X → Y) → ↑→ (f ∘ g) ≃ (↑→ f ∘ ↑→ g)
  ↑-func f g (i x) = refl
  ↑-func f g o = refl

  i-nat : ∀ {X Y : Set} (f : X → Y) → (↑→ f ∘ i) ≃ (i ∘ f)
  i-nat f x = refl

