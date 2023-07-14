module Decidability where

open import Lambda public

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