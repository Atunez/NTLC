module SimpleLambda where

-- import Agda.Builtin.Sigma

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

  funcid : ∀ {X Y : Set} {f : X → Y} → f ≃ f
  funcid = λ x → refl

open Equality


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

open Lifting

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
open Terms

module Substitution where
  -- BIND: The generic substitution operator:
  --   Given M ∈ Λ X, where X = {x1,..,xk}, and
  --   a function f : X → Λ Y, assigning to each xi ∈ X
  --     a term Ni ∈ Λ Y, where Y = {y1,..,ym},
  --   produce a term M [xi := Ni]_{i=1..k} ∈ Λ Y
  bind : ∀ {X Y : Set} → (X → Λ Y) → Λ X → Λ Y
  bind f (var x)     = f x
  bind f (app t₀ t₁) = app (bind f t₀) (bind f t₁)
  bind f (abs t)     = abs (bind (Λ↑ ∘ ↑→ f) t)

  bind-ext : ∀ {X Y : Set} {f g : X → Λ Y} → f ≃ g → bind f ≃ bind g
  bind-ext fg (var x)     = fg x
  bind-ext fg (app t₀ t₁) = app≡ (bind-ext fg t₀) (bind-ext fg t₁)
  bind-ext fg (abs t)     = abs≡ (bind-ext (λ x → ext Λ↑ (↑-ext fg x)) t)
  -- bind-ext fg (abs t) = abs≡ (bind-ext (ext Λ↑  ∘  ↑-ext fg) t)

  -- LAWS OF BIND
  -- Naturality of bind
  bind-nat1 : ∀ {X Y Y' : Set} (y : Y → Y') (f : X → Λ Y)
             → Λ→ y ∘ bind f ≃ bind (Λ→ y ∘ f)
  bind-nat1 y f (var x) = refl
  bind-nat1 y f (app t₀ t₁) = app≡ (bind-nat1 y f t₀) (bind-nat1 y f t₁)
  bind-nat1 y f (abs t) =
    abs≡ ( bind-nat1 (↑→ y) (Λ↑ ∘ ↑→ f) t
    ! bind-ext  ( λ x → Λ↑-nat y (↑→ f x) ! ext Λ↑ (~ ↑-func (Λ→ y) f x)) t)

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

open Substitution


module Reductions where

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

infix 15 _⟶_

-- Beta reduction
-- If M,N : Λ X, then M ⟶ N = { ρ : M →β N }
data _⟶_ {X : Set} : Λ X → Λ X → Set where
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
_⇒_ : ∀ {X : Set} → Λ X → Λ X → Set
_⇒_ = (_⟶_)*

append⇒ : ∀ {X : Set} {L M N : Λ X} → L ⇒ M → M ⇒ N → L ⇒ N
append⇒ = appendR {R = _⟶_}

infix 15 _⇉_

-- Parallel Reduction
data _⇉_ {X : Set} : Λ X → Λ X → Set where
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
_≡>_ : ∀ {X : Set} → Λ X → Λ X → Set
_≡>_ = (_⇉_)*

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

open Reductions

module ChurchRosserTheorem where


-- Conf⇉ M N = { (Z,l,r) | Z ∈ Λ X , l : M ⇉ Z, r : N ⇉ Z }
-- Conf⇉ M N = { Z ∈ Λ X |  M ⇉ Z ∧ N ⇉ Z }
record Conf {X : Set} (R : Rel X) (M : X) (N : X) : Set where
  constructor conf
  field
    node : X
    lleg : R M node
    rleg : R N node
open Conf

-- These two allow for different starting points
-- ie, reductions are X > Z and Y > Z
Conf⇉ : ∀ {X : Set} → Λ X → Λ X → Set
Conf⇉ = Conf _⇉_

Conf≡> : ∀ {X : Set} → Λ X → Λ X → Set
Conf≡> = Conf _≡>_


-- These two DONT allow for different starting points
-- ie, reductions are X > Z and X > Z
SConf⇉ : ∀ {X : Set} → Λ X → Set
SConf⇉ input = Conf _⇉_ input input

SConf≡> : ∀ {X : Set} → Λ X → Set
SConf≡> input = Conf _≡>_ input input

dp⇉ : ∀ {X : Set} {M N : Λ X} → M ⇉ N → ∀ {L : Λ X} → M ⇉ L → Conf⇉ N L
dp⇉ ε⇉ {(var x)} ε⇉ = conf (var x) ε⇉ ε⇉
dp⇉ (abs⇉ ρ) {(abs L)} (abs⇉ ml) = let (conf Z l r) = dp⇉ ρ ml
                                    in conf (abs Z) (abs⇉ l) (abs⇉ r)
dp⇉ {X} {app M₀ M₁} {app N₀ N₁} (app⇉ ρ₀ ρ₁) (app⇉ σ₀ σ₁) =
  let (conf Z₀ l₀ r₀) = dp⇉ ρ₀ σ₀
      (conf Z₁ l₁ r₁) = dp⇉ ρ₁ σ₁
  in conf (app Z₀ Z₁) (app⇉ l₀ l₁) (app⇉ r₀ r₁)
dp⇉ {X} {app (abs M₀) M₁} {app (abs N₀) N₁} (app⇉ (abs⇉ ρ₀) ρ₁) (red⇉ σ₀ σ₁) =
  let (conf Z₁ l₁ r₁) = dp⇉ ρ₁ σ₁
      (conf Z₀ l₀ r₀) = dp⇉ ρ₀ σ₀
      Z = Z₀ [ Z₁ ]
      l = red⇉ l₀ l₁
      r = ⇉-subst r₀ r₁
  in  conf Z l r
dp⇉ (red⇉ ρ₀ ρ₁) (app⇉ (abs⇉ σ₀) σ₁) = 
  let (conf Z₁ l₁ r₁) = dp⇉ σ₁ ρ₁
      (conf Z₀ l₀ r₀) = dp⇉ σ₀ ρ₀
      Z = Z₀ [ Z₁ ]
      l = red⇉ l₀ l₁
      r = ⇉-subst r₀ r₁
  in conf Z r l
dp⇉ (red⇉ ρ₀ ρ₁) (red⇉ σ₀ σ₁) = 
  let (conf Z₁ l₁ r₁) = dp⇉ σ₁ ρ₁
      (conf Z₀ l₀ r₀) = dp⇉ σ₀ ρ₀
      Z = Z₀ [ Z₁ ]
      l = ⇉-subst r₀ r₁
      r = ⇉-subst l₀ l₁
  in conf Z l r


open ChurchRosserTheorem