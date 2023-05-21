module Reductions where

open import Base
open import Terms
open import Substitution

-- Data Rel x y, Equ y ≡ y' > Rel x y'
Rel : Set → Set₁
Rel X = X → X → Set

data _* {X : Set} (R : Rel X) : Rel X where
  ε* : ∀ (x : X) → (R *) x x
  c* : ∀ {x y z : X} → R x y → (R *) y z → (R *) x z

appendR : ∀ {X : Set} {R : Rel X} {x y z : X} → (R *) x y → (R *) y z → (R *) x z
appendR (ε* x) yz = yz
appendR (c* r xy) yz = c* r (appendR xy yz)

≡R : ∀ {X : Set} {R : Rel X} {x y z : X} → R x y → y ≡ z → R x z 
≡R input refl = input

-- i→R : ∀ {X : Set} (R : Rel (Λ X)) (R' : Rel (Λ (↑ X))) {x y : Λ X} → R x y → R' (Λ↑ (i x)) (Λ↑ (i y))


infix 15 _⟶_

-- Beta reduction
-- If M,N : Λ X, then M ⟶ N = { ρ : M →β N }
data _⟶_ {X : Set} : Rel (Λ X) where
  redex : ∀ M N → app (abs M) N ⟶ (M [ N ])
  abs→  : ∀ {P Q} → P ⟶ Q → abs P ⟶ abs Q
  appL→ : ∀ {L M Z} → L ⟶ M → app L Z ⟶ app M Z
  appR→ : ∀ {Z M N} → M ⟶ N → app Z M ⟶ app Z N

⟶≡ : ∀ {X : Set} {M N N' : Λ X} → M ⟶ N → N ≡ N' → M ⟶ N'
⟶≡ = ≡R {R = _⟶_}

map⟶ : ∀ {X Y} (f : X → Y) {M N : Λ X} → M ⟶ N → Λ→ f M ⟶ Λ→ f N
map⟶ f (redex M N) = ⟶≡ (redex (Λ→ (↑→ f) M) (Λ→ f N)) (~ subst→ f M N )
map⟶ f (abs→ r)    = abs→ (map⟶ (↑→ f) r)
map⟶ f (appL→ r)   = appL→ (map⟶ f r)
map⟶ f (appR→ r)   = appR→ (map⟶ f r)

-- Multi-step beta reduction
_⇒_ : ∀ {X : Set} → Rel (Λ X)
_⇒_ = (_⟶_)*

⇒≡ : ∀ {X : Set} {M N N' : Λ X} → M ⇒ N → N ≡ N' → M ⇒ N'
⇒≡ = ≡R {R = (_⟶_)*}

append⇒ : ∀ {X : Set} {L M N : Λ X} → L ⇒ M → M ⇒ N → L ⇒ N
append⇒ = appendR {R = _⟶_}

infix 15 _⇉_

-- Parallel Reduction
data _⇉_ {X : Set} : Rel (Λ X) where
  ε⇉   : ∀ {x : X} → var x ⇉ var x
  abs⇉ : ∀ {M} {N} → M ⇉ N → abs M ⇉ abs N
  app⇉ : ∀ {M M' N N'} → M ⇉ M' → N ⇉ N' → app M N ⇉ app M' N'
  red⇉ : ∀ {M M' N N'} → M ⇉ M' → N ⇉ N' → app (abs M) N ⇉ M' [ N' ]

⇉≡ : ∀ {X : Set} {M N N' : Λ X} → M ⇉ N → N ≡ N' → M ⇉ N'
⇉≡ = ≡R {R = _⇉_}

map⇉ : ∀ {X Y : Set} (f : X → Y) {M N : Λ X} (ρ : M ⇉ N) → Λ→ f M ⇉ Λ→ f N
map⇉ f ε⇉ = ε⇉
map⇉ f (abs⇉ ρ) = abs⇉ (map⇉ (↑→ f) ρ )
map⇉ f (app⇉ ρ₀ ρ₁) = app⇉ (map⇉ f ρ₀) (map⇉ f ρ₁)
map⇉ f (red⇉ {M} {M'} {N} {N'} ρ₀ ρ₁)
  = ⇉≡ (red⇉ (map⇉ (↑→ f) ρ₀) (map⇉ f ρ₁) ) (~ (subst→ f M' N' ))
  
refl⇉ : ∀ {X} (M : Λ X) → M ⇉ M
refl⇉ (var x) = ε⇉
refl⇉ (app M₀ M₁) = app⇉ (refl⇉ M₀) (refl⇉ M₁)
refl⇉ (abs M) = abs⇉ (refl⇉ M)

-- Multi-step parallel reduction
_≡>_ : ∀ {X : Set} → Rel (Λ X)
_≡>_ = (_⇉_)*

≡>≡ : ∀ {X : Set} {M N N' : Λ X} → M ≡> N → N ≡ N' → M ≡> N'
≡>≡ = ≡R {R = (_⇉_)*}

append≡> : ∀ {X : Set} {L M N : Λ X} → L ≡> M → M ≡> N → L ≡> N
append≡> = appendR {R = _⇉_}

bind⇉ : ∀ {X Y : Set} (M : Λ X) (f g : X → Λ Y)
          → (∀ (x : X) → f x ⇉ g x)
          → bind f M ⇉ bind g M
bind⇉ (var x) f g red = red x
bind⇉ (app t t₁) f g red = app⇉ (bind⇉ t f g red) (bind⇉ t₁ f g red)
bind⇉ (abs t) f g red = abs⇉ (bind⇉ t (Λ↑ ∘ ↑→ f) (Λ↑ ∘ ↑→ g)
  λ { (i x) → map⇉ i (red x) ; o → refl⇉ (var o) })


buildproofv2 : ∀ {X : Set} (x : Λ X) → bind (λ x₁ → var x₁) x ≡ x
buildproofv2 (var x) = refl
buildproofv2 (app x x₁) = app≡ (buildproofv2 x) (buildproofv2 x₁)
buildproofv2 (abs x) = abs≡ (bind-ext {f = Λ↑ ∘ ↑→ var} {g = var}
 (λ {(i x) → refl; o → refl}) x ! buildproofv2 x)


bind⇉subst : ∀ {X Y : Set} {M1 M2 : Λ X} → M1 ⇉ M2
             → ∀ {f g : X → Λ Y}
             → (∀ x → f x ⇉ g x)
             → bind f M1 ⇉ bind g M2
bind⇉subst ε⇉ prf = prf _
bind⇉subst (abs⇉ red) prf = abs⇉ (bind⇉subst red 
  λ {(i x) → map⇉ i (prf x) ; o → refl⇉ (var o)})
bind⇉subst (app⇉ red red₁) prf = app⇉ (bind⇉subst red prf) (bind⇉subst red₁ prf)
bind⇉subst (red⇉ {M} {M'} {N} {N'} red red₁) {f} {g} prf = 
  ⇉≡ (red⇉ (bind⇉subst red (λ {(i x) → map⇉ i (prf x) ; o → refl⇉ (var o)})) 
  (bind⇉subst red₁ prf))
   (((~ bind-law (Λ↑ ∘ ↑→ g) (io var (bind g N')) M') ! 
   bind-ext (λ {(i x) → (~ bind-nat2 i (io var (bind g N')) (g x)) 
   ! ext≃ buildproofv2 (refl {a = (g x)}) ; o → refl}) M') ! 
   bind-law (io var N') g M')

⇉-subst : ∀ {X : Set} {M M'} {N N' : Λ X} →
            M ⇉ M' → N ⇉ N' → M [ N ] ⇉ M' [ N' ]
⇉-subst rd1 rd2 = bind⇉subst rd1 (λ {(i x) → ε⇉; o → rd2})