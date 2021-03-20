module Lambda where

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

  -- random-lemma: ∀ {X Y : Set} {f g : X → Y} {x : X} → f ≡ g → f x ≡ g x
  -- random-lemma input = ?
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

-- module Types where

-- -- 𝕋 > bT
-- data 𝕋 (A : Set) : Set where
--   Tvar : A → 𝕋 A 
--   Fun : 𝕋 A → 𝕋 A → 𝕋 A
--   -- All : 𝕋 (↑ A) → 𝕋 A

-- 𝕋Env : Set → Set → Set
-- 𝕋Env A X = X → 𝕋 A 

-- open Types

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

  -- -- : is \: ∶ 
  -- data _⊢_∶_ {A X : Set} : 𝕋Env A X → Λ X → 𝕋 A → Set where 
  --   Ax : ∀ Γ x → Γ ⊢ var x ∶ Γ x 
  --   App : ∀ Γ {M N : Λ X} {α β : 𝕋 A} → Γ ⊢ M ∶ (Fun α β) → Γ ⊢ N ∶ α → Γ ⊢ (app M N) ∶ β 
  --   Abs : ∀ Γ {M : Λ (↑ X)} {α β : 𝕋 A} → (io Γ α) ⊢ M ∶ β → Γ ⊢ (abs M) ∶ Fun α β  
  --   -- APP : ∀ Γ {M : Λ X} {Ψ : 𝕋 (↑ A)} → Γ ⊢ M ∶ All Ψ → (α : 𝕋 A) → Γ ⊢ M ∶ (io id α Ψ)
  --   -- ABS : ∀ Γ {M : Λ X} {Ψ : 𝕋 (↑ A)} → (∀ (α : 𝕋 A) → Γ ⊢ M ∶ io id α Ψ) → Γ ⊢ M ∶ All Ψ 
  
  -- Congruence
  var≡ : ∀ {X} {x y : X} → x ≡ y → var x ≡ var y
  var≡ = ext var
  -- var≡ refl = refl

  app≡ : ∀ {X} {s s' t t' : Λ X} → s ≡ s' → t ≡ t' → app s t ≡ app s' t'
  app≡ refl refl = refl

  abs≡ : ∀ {X} {s t : Λ (↑ X)} → s ≡ t → abs s ≡ abs t
  abs≡ = ext abs
  -- abs≡ refl = refl

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
  Λ→-aux f g h fgh x = (~ Λ-func f g x) ! Λ-ext fgh x

  -- This function takes either a λ-term M ∈ Λ(x1,..,xk),
  -- or a special symbol o ∈ 1,
  -- and returns a λ-term ∈ Λ(x1,..,xk+1)
  Λ↑ : ∀ {X : Set} → ↑ (Λ X) → Λ (↑ X)
  Λ↑ = io (Λ→ i) (var o)
  -- Λ↑ (i M) = Λ→ i M
  -- Λ↑ o = var o

  Λ↑-ext : ∀ {X : Set} {s t : ↑ (Λ X)} → s ≡ t → Λ↑ s ≡ Λ↑ t
  Λ↑-ext = ext Λ↑
  -- Λ↑-ext refl = refl

  Λ↑-nat : ∀ {X Y : Set} (f : X → Y) → Λ→ (↑→ f) ∘ Λ↑ ≃ Λ↑ ∘ ↑→ (Λ→ f)
  Λ↑-nat f (i (var x)) = refl
  Λ↑-nat f (i (app t₀ t₁)) = app≡ (Λ↑-nat f (i t₀)) (Λ↑-nat f (i t₁))
  Λ↑-nat f (i (abs t)) =
    abs≡ ( Λ→-aux (↑→ (↑→ f)) (↑→ i) (↑→ (↑→ f ∘ i)) (symm (↑-func (↑→ f) i)) t
         ! ~ Λ→-aux (↑→ i) (↑→ f) _ (symm (↑-func i f ) ) t )
  Λ↑-nat f o = refl

  -- ΛMorph : ∀ {X : Set} → Λ (Λ X) → Λ X
  -- ΛMorph (var x) = x
  -- ΛMorph (app x x₁) = app (ΛMorph x) (ΛMorph x₁)
  -- ΛMorph (abs x) = abs (ΛMorph (Λ→ Λ↑ x))
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

  -- special : ∀ {X X' Y : Set} (x : X → X') (f : X' → Λ Y) (ip : ↑ X) (t : Λ (↑ X)) → Λ↑ ip ≡ ((λ x₁ → Λ↑ (↑→ f x₁)) ∘ ↑→ x)
  -- special input1 input2 input3 input4 = ?

  bind-nat2 : ∀ {X X' Y : Set} (x : X → X') (f : X' → Λ Y)
                → bind (f ∘ x) ≃ bind f ∘ Λ→ x
  bind-nat2 x f (var y) = refl
  bind-nat2 x f (app t₀ t₁) = app≡ (bind-nat2 x f t₀) (bind-nat2 x f t₁)
  bind-nat2 x f (abs t) =  abs≡ ( bind-ext lemma t ! bind-nat2 (↑→ x) (Λ↑ ∘ ↑→ f) t )
    where lemma = λ y → ext Λ↑ (↑-func f x y )

  -- Λ↑ ( (↑→ g) (p x)) ≡ (Λ→ f) (g x)

  -- extplz : ∀ {Y Z : Set} (g : Y → Λ Z) (f : Z → ↑ Z) (x : Z) → f (g x) ≡ (Λ↑ ∘ ↑→ g) (i x) → Λ→ f (g x) ≡ (Λ↑ ∘ ↑→ g) (i x)
  -- extplz g f x = ?

  Λ→-ext : ∀ {X Y : Set} {f g : X → Y} → f ≡ g → Λ→ f ≡ Λ→ g
  Λ→-ext refl = refl

  isittruethough : ∀ {Y Z : Set} {f g : Λ (↑ Z)} → f ≡ g → Λ→ i f ≡ Λ→ i g
  isittruethough refl = refl

  smollift :  ∀ {Y Z : Set} (g : Y → Λ Z) (f : Z → ↑ Z) (p : Y → ↑ Y) → Λ→ f ∘ g ≃ Λ↑ ∘ ↑→ g ∘ p → Λ→ (↑→ f) ∘ (λ x₁ → Λ↑ (↑→ g x₁)) ≃ Λ↑ ∘ ↑→ (λ x₁ → Λ↑ (↑→ g x₁)) ∘ ↑→ p
  smollift {Y} g f p prf = λ {(i x) → (~ Λ-func (↑→ f) i (g x)) ! (Λ-func i f (g x) ! isittruethough {Y = Y} (prf x)) ; o → refl}

  maybelemma : ∀ {Y Z : Set} (g : Y → Λ Z) (f : Z → ↑ Z) (p : Y → ↑ Y) (x : Λ Y) → (Λ→ f) ∘ g ≃ (Λ↑ ∘ ↑→ g) ∘ p → Λ→ f (bind g x) ≡ bind (Λ↑ ∘ ↑→ g) (Λ→ p x)
  maybelemma g f p (var x) prf = prf x
  maybelemma g f p (app x x₁) prf = app≡ (maybelemma g f p x prf) (maybelemma g f p x₁ prf)
  maybelemma g f p (abs x) prf = abs≡ (maybelemma (Λ↑ ∘ ↑→ g) (↑→ f) (↑→ p) x (smollift g f p prf))

  rightext : ∀ {Y Z : Set} (g f : Y → Z) (x : Y) → g ≡ f → g x ≡ f x
  rightext g .g x refl = refl

  bind↑-dist : ∀ {Y Z : Set} (g : Y → Λ Z)
               → Λ↑ ∘ ↑→ (bind g) ≃ bind (Λ↑ ∘ ↑→ g) ∘ Λ↑
  bind↑-dist g (i (var x)) = refl
  bind↑-dist g (i (app x x₁)) = app≡ (maybelemma g i i x λ x → refl) (maybelemma g i i x₁ (λ x → refl))
  bind↑-dist g (i (abs x)) =  abs≡ (maybelemma (Λ↑ ∘ ↑→ g) (↑→ i) (↑→ i) x λ {(i y) → (~ Λ-func (↑→ i) i (g y)) ! Λ-func i i (g y) ; o → refl})
  bind↑-dist g o = refl

  bindext : ∀ {Y Z : Set} {g f : Y → Λ Z} {x y : Λ Y} → g ≡ f → x ≡ y → bind g x ≡ bind f y
  bindext refl refl = refl

  lastpart : ∀ {X Y Z : Set} (f : X → Λ Y) (g : Y → Λ Z) (x : X) → bind (Λ→ i) (Λ→ g (f x)) ≡ bind (Λ↑ ∘ ↑→ g) (Λ→ i (f x))
  lastpart f g x = ~ bind-nat2 g (Λ→ i) (f x) ! bind-nat2 i (Λ↑ ∘ ↑→ g) ((f x))

  smalltheory : ∀ {X Y Z : Set} (f : X → Λ Y) (g : Y → Λ Z) (x : X) → Λ→ i (bind g (f x)) ≡ bind (λ x₁ → io (Λ→ i) (var o) (↑→ g x₁)) (Λ→ i (f x))
  smalltheory f g x = bind-nat1 i g (f x) ! (bind-nat2 g (Λ→ i) (f x) ! lastpart f g x)

  -- -- Associativity of bind
  bind-law : ∀ {X Y Z : Set} (f : X → Λ Y) (g : Y → Λ Z)
           → bind (bind g ∘ f) ≃ (bind g ∘ bind f)
  bind-law f g (var x) = refl
  bind-law f g (app t₀ t₁) = app≡ (bind-law f g t₀) (bind-law f g t₁)
  bind-law f g (abs t) = abs≡ (bind-ext (λ {(i x) → smalltheory f g x ; o → refl}) t ! bind-law (Λ↑ ∘ ↑→ f) (Λ↑ ∘ ↑→ g) t)

  -- bind-law : ∀ {X Y Z : Set} (f : X → Λ Y) (g : Y → Λ Z)
  --          → (bind g ∘ bind f) ≃ bind (bind g ∘ f)
  -- bind-law f g (var x) = refl
  -- bind-law f g (app t₀ t₁) = app≡ (bind-law f g t₀) (bind-law f g t₁)
  -- bind-law f g (abs t) = abs≡ (
  --           tran (bind-law (Λ↑ ∘ ↑→ f) (Λ↑ ∘ ↑→ g) )
  --                (bind-ext {!   !} ) t )
  --
  -- μ is mu
  -- MULTIPLICATION: Monad Structure on Λ
  Λμ : ∀ {X} → Λ (Λ X) → Λ X
  Λμ = bind id
  -- Λμ (var M) = M
  -- Λμ (app M N) = app (Λμ M) (Λμ N)
  -- Λμ (abs M) = abs (Λμ (Λ→ Λ↑ M ) )

  -- bind-from-mu : ∀ {X Y : Set} → (X → Λ Y) → Λ X → Λ Y
  -- bind-from-mu f t = Λμ (Λ→ f t)

  -- SUBSTITUTION
  --   Given M ∈ Λ {x1,..,xk+1}, and N ∈ Λ {x1,..,xk},
  --   produce M[xk+1 := N] ∈ Λ {x1,..,xk}
  infixr 30 _[_]
  _[_] : ∀ {X : Set} → Λ (↑ X) → Λ X → Λ X

  M [ N ] = bind (io var N) M
  -- M [ N ] = bind (λ { (i x) → var x ; o → N }) M

  io-var-nat : ∀ {X Y : Set} (f : X → Y) (M : Λ X)
              → Λ→ f ∘ io var M ≃ io var (Λ→ f M) ∘ ↑→ f
  io-var-nat f M (i x) = refl
  io-var-nat f M o = refl

  -- Substitution Lemma
  subst→ : ∀ {X Y : Set} (f : X → Y) (M : Λ (↑ X)) (N : Λ X)
             → Λ→ f (M [ N ]) ≡ Λ→ (↑→ f) M [ Λ→ f N ]
  subst→ f M N =   bind-nat1 f (io var N) M
                 ! bind-ext (io-var-nat f N) M
                 ! bind-nat2 (↑→ f) (io var (Λ→ f N)) M

  -- subst-lemma : ∀ {X : Set} (L : Λ (↑ (↑ X))) (M : Λ (↑ X)) (N : Λ X)
  --               → L [ M ] [ N ] ≡ L [ Λ→ i N ] [ M [ N ] ]
  -- subst-lemma L M N = {! bind-law (io var M ) (io var N) L  !}
open Substitution

this : ∀ {X} → Λ (↑ X)
this = var o

module Example1 where
  -- λ x. x (λ y. V y x) ∈ Λ ⊤
  term1 : Λ ⊤             -- ⊤ holds V
  term1 = abs (app this
                   (abs (app (app (var (i (i tt)))
                                  this)
                             (var (i o)))))

  -- x (λ z. z z x x)
  term2 : Λ (↑ ⊤)
  term2 = app (var (i tt))
              (abs (app (app (app this this)
                             (var (i (i tt))))
                        (var (i (i tt)))))



  -- (λ x. x (λ y. V y x)) (λ z. V z (λ x. x (λ y. V y x)) (S V))
  --    = term2 [ x := term1 ]
  term3 : Λ ⊤
  term3 = term2 [ term1 ]

  
  g : ⊤ → Λ ⊤
  g tt = term1

  bind-dist1 = (Λ↑ ∘ ↑→ (bind g)) (i term1)
  bind-dist2 = (bind (Λ↑ ∘ ↑→ g) ∘ Λ↑) (i term1)

  hey : bind-dist1 ≡ bind-dist2
  hey = refl
-- SINGLE-STEP BETA REDUCTION
-- ⟶ is \-->
infix 15 _⟶_

-- If M,N : Λ X, then M ⟶ N = { ρ : M →β N }
data _⟶_ {X : Set} : Λ X → Λ X → Set where
  redex : ∀ M N → app (abs M) N ⟶ (M [ N ])
  abs→  : ∀ {P Q} → P ⟶ Q → abs P ⟶ abs Q
  appL→ : ∀ {L M Z} → L ⟶ M → app L Z ⟶ app M Z
  appR→ : ∀ {Z M N} → M ⟶ N → app Z M ⟶ app Z N

⟶≡ : ∀ {X : Set} {M N N' : Λ X} → M ⟶ N → N ≡ N' → M ⟶ N'
⟶≡ r refl = r

map⟶ : ∀ {X Y} (f : X → Y) {M N : Λ X} → M ⟶ N → Λ→ f M ⟶ Λ→ f N
map⟶ f (redex M N) = ⟶≡ (redex (Λ→ (↑→ f) M) (Λ→ f N)) (~ subst→ f M N )
map⟶ f (abs→ r)    = abs→ (map⟶ (↑→ f) r)
map⟶ f (appL→ r)   = appL→ (map⟶ f r)
map⟶ f (appR→ r)   = appR→ (map⟶ f r)

term21 : Λ⁰ -- λ x. I x x
term21 = abs (app (app (abs this ) this ) this)
term22 : Λ⁰ -- λ x. x x
term22 = abs (app this this )

term21→term22 : term21 ⟶ term22
term21→term22 = abs→ (appL→ (redex _ _) )

-- MANY-STEP BETA REDUCTION

-- ⇒ is \=>
infix 15 _⇒_

data _⇒_ {X : Set} : Λ X → Λ X → Set where
  ε⇒   : ∀ {M} → M ⇒ M  -- reduction in 0 steps (empty reduction)
  _c⇒_ : ∀ {L M N} → (L ⟶ M) → (M ⇒ N) → (L ⇒ N)

append⇒ : ∀ {X} {L M N : Λ X} → L ⇒ M → M ⇒ N → L ⇒ N
append⇒ ε⇒ r2 = r2
append⇒ (c c⇒ r1) r2 = c c⇒ (append⇒ r1 r2)


-- Parallel reduction

-- ⇉ is \r-2
infix 15 _⇉_

data _⇉_ {X : Set} : Λ X → Λ X → Set where
  ε⇉   : ∀ {x : X} → var x ⇉ var x
  abs⇉ : ∀ {M} {N} → M ⇉ N → abs M ⇉ abs N
  app⇉ : ∀ {M M' N N'} → M ⇉ M' → N ⇉ N' → app M N ⇉ app M' N'
  red⇉ : ∀ {M M' N N'} → M ⇉ M' → N ⇉ N' → app (abs M) N ⇉ M' [ N' ]

-- HW for next time: Prove (λ x. x ((λ y. y) ((λ z. z) x)))) V ⇉ V V

refl⇉ : ∀ {X} (M : Λ X) → M ⇉ M
refl⇉ (var x) = ε⇉
refl⇉ (app M₀ M₁) = app⇉ (refl⇉ M₀) (refl⇉ M₁)
refl⇉ (abs M) = abs⇉ (refl⇉ M)

⇉≡ : ∀ {X : Set} {M N N' : Λ X} → M ⇉ N → N ≡ N' → M ⇉ N'
⇉≡ ρ refl = ρ

map⇉ : ∀ {X Y : Set} (f : X → Y) {M N : Λ X} (ρ : M ⇉ N) → Λ→ f M ⇉ Λ→ f N
map⇉ f ε⇉ = ε⇉
map⇉ f (abs⇉ ρ) = abs⇉ (map⇉ (↑→ f) ρ )
map⇉ f (app⇉ ρ₀ ρ₁) = app⇉ (map⇉ f ρ₀) (map⇉ f ρ₁)
map⇉ f (red⇉ {M} {M'} {N} {N'} ρ₀ ρ₁)
  = ⇉≡ (red⇉ (map⇉ (↑→ f) ρ₀) (map⇉ f ρ₁) ) (~ (subst→ f M' N' ))

-- Conf⇉ M N = { (Z,l,r) | Z ∈ Λ X , l : M ⇉ Z, r : N ⇉ Z }
-- Conf⇉ M N = { Z ∈ Λ X |  M ⇉ Z ∧ N ⇉ Z }
record Conf {X : Set} (R : X → X → Set) (M : X) (N : X) : Set where
  constructor conf
  field
    node : X
    lleg : R M node
    rleg : R N node
open Conf

Conf⇉ : ∀ {X : Set} → Λ X → Λ X → Set
Conf⇉ = Conf _⇉_

i⇉ : ∀ {X : Set} (x y : Λ X) → x ⇉ y → Λ↑ (i x) ⇉ Λ↑ (i y)
i⇉ (var x) .(var x) ε⇉ = ε⇉
i⇉ (app s1 s2) t r with r
i⇉ (app s1 s2) t r | (app⇉ r1 r2) = app⇉ (map⇉ i r1) (map⇉ i r2)
...                | (red⇉ {N'} {N''} {M} {M'} r1 r2) = map⇉ i (red⇉ r1 r2)
i⇉ (abs u) (abs v) (abs⇉ r) = abs⇉ (map⇉ (↑→ i) (r))

Λ↑-ext⇉ : ∀ {X Y : Set} (f g : X → Λ Y) (x : X) → f x ⇉ g x → Λ↑ (i (f x)) ⇉ Λ↑ (i (g x))
Λ↑-ext⇉ f g x prf = i⇉ (f x) (g x) prf

lift-prf : ∀ {X Y : Set} (f g : X → Λ Y)
          → (∀ (x : X) → f x ⇉ g x)
          → ((x : ↑ X) → Λ↑ (↑→ f x) ⇉ Λ↑ (↑→ g x))
lift-prf f g prf = λ { (i x) → Λ↑-ext⇉ f g x (prf x) ; o → refl⇉ (var o) }

bind⇉ : ∀ {X Y : Set} (M : Λ X) (f g : X → Λ Y)
          → (∀ (x : X) → f x ⇉ g x)
          → bind f M ⇉ bind g M
bind⇉ (var x) f g red = red x
bind⇉ (app t t₁) f g red = app⇉ (bind⇉ t f g red) (bind⇉ t₁ f g red)
bind⇉ (abs t) f g red = abs⇉ (bind⇉ t (((Λ↑ ∘ ↑→ f))) ((Λ↑ ∘ ↑→ g)) (lift-prf f g red))

io-var⇉ : ∀ {X : Set} (x : ↑ X) {N N' : Λ X} → N ⇉ N' → io var N x ⇉ io var N' x
io-var⇉ (i x) prf = ε⇉
io-var⇉ o prf = prf

Λ↑↑-ext : ∀ {X : Set} (x : ↑ (↑ X)) {N N' : Λ X} → N ⇉ N' → Λ↑ (↑→ (io var N) x) ⇉ Λ↑ (↑→ (io var N') x)
Λ↑↑-ext (i x) prf = map⇉ i (io-var⇉ x prf)
Λ↑↑-ext o prf = ε⇉

⇉-subst1 : ∀ {X : Set} (M) {N N' : Λ X} → N ⇉ N' → M [ N ] ⇉ M [ N' ]
⇉-subst1 (var (i x)) ν = ε⇉
⇉-subst1 (var o) ν = ν
⇉-subst1 (app M₁ M₂) ν = app⇉ (⇉-subst1 M₁ ν) (⇉-subst1 M₂ ν)
⇉-subst1 (abs M) {N} {N'} ν = abs⇉ (bind⇉ M (λ x → Λ↑ (↑→ (io var N) x)) (λ x → Λ↑ (↑→ (io var N') x)) λ x → Λ↑↑-ext x ν)

proofsarehard : ∀ {X Y : Set} (M : ↑ (Λ (↑ X))) (N : Λ X) → (Λ↑ ∘ ↑→ (bind (io var N))) M ≡ (bind (Λ↑ ∘ ↑→ (io var N)) ∘ Λ↑) M
proofsarehard M N = bind↑-dist (io var N) M

-- doubletrouble : ∀ {X : Set} (M : Λ (↑ (↑ X))) (N : Λ (↑ X)) (P : Λ X) →  bind (λ z → Λ↑ (↑→ (io var P) z)) M [ N [ P ] ] ≡ (M [ N ]) [ P ]
-- doubletrouble M N P = {!  !}

random : ∀ {X : Set} →  Λ↑ {X = X} ∘ ↑→ var ≃ var
random (i x) = refl
random o = refl

buildproofv2 : ∀ {X : Set} (x : Λ X) → bind (λ x₁ → var x₁) x ≡ x
buildproofv2 (var x) = refl
buildproofv2 (app x x₁) = app≡ (buildproofv2 x) (buildproofv2 x₁)
buildproofv2 (abs x) = abs≡ (bind-ext {f = Λ↑ ∘ ↑→ var} {g = var} random x ! buildproofv2 x)
-- abs≡ ( bind-ext {! random   !} x ! buildproofv2 x)


bind-unit : ∀ {X : Set} (N : Λ X) → bind (io var N) ∘ (Λ→ i) ≃ id
bind-unit N x = (~ bind-nat2 i (io var N) x) ! buildproofv2 x

typesquare : ∀ {X Y : Set} (g : X → Λ Y) (N : Λ X) → (bind (io var (bind g N)) ∘ (λ x → Λ↑ (↑→ g x))) ≃ (bind g ∘ io var N)
-- ( io var (bind g N)  ∘ (Λ↑ ∘ ↑→ g) ) ≡ (g ∘ io var N)
typesquare g N (i x) = bind-unit (bind g N) (g x)
typesquare g N o = refl



-- Need more general lemma:
bind⇉subst : ∀ {X Y : Set} {M1 M2 : Λ X} → M1 ⇉ M2
             → ∀ {f g : X → Λ Y}
             → (∀ x → f x ⇉ g x)
             → bind f M1 ⇉ bind g M2
bind⇉subst ε⇉ {f} {g} fg = fg _
bind⇉subst (abs⇉ μ) {f} {g} fg = abs⇉ (bind⇉subst μ (lift-prf f g fg) )
bind⇉subst (app⇉ μ₀ μ₁) {f} {g} fg = app⇉ (bind⇉subst μ₀ fg) (bind⇉subst μ₁ fg)
bind⇉subst {X} {Y} {M1} {M2} (red⇉ {M} {M'} {N} {N'} μ μ₁) {f} {g} fg = 
  ⇉≡ (red⇉ (bind⇉subst μ (lift-prf f g fg)) (bind⇉subst μ₁ fg)) 
    (((~ bind-law (Λ↑ ∘ ↑→ g) (io var (bind g N')) M') 
      ! bind-ext (typesquare g N') M') 
        ! bind-law (io var N') g M')

buildproof : ∀ {X : Set} {N N' : Λ X} → N ⇉ N' → (x : ↑ (↑ X)) → Λ↑ (↑→ (io var N) x) ⇉ Λ↑ (↑→ (io var N') x)
buildproof red (i (i x)) = ε⇉
buildproof {X} {N} {N'} red (i o) = i⇉ N N' red
buildproof red o = ε⇉

addition : ∀ {X : Set} {N N' : Λ X} → N ⇉ N' → ( ∀ x → (io var N) x ⇉ (io var N') x )
addition red (i x) = ε⇉
addition red o = red

⇉-subst : ∀ {X : Set} {M M'} {N N' : Λ X} →
            M ⇉ M' → N ⇉ N' → M [ N ] ⇉ M' [ N' ]
⇉-subst rd1 rd2 = bind⇉subst rd1 (addition rd2)
-- ⇉-subst {X} {var (i x)} ε⇉ ν = ε⇉
-- ⇉-subst {X} {var o} ε⇉ ν = ν
-- ⇉-subst {X} {abs M} {abs M'} {N} {N'} (abs⇉ μ) ν
--   = abs⇉ (bind⇉subst μ λ x → buildproof ν x)
--   -- = abs⇉ (⇉-subst {! Λ↑↑-ext M μ   !} (io-var⇉ {!   !} {! μ   !} ) )
-- ⇉-subst (app⇉ μ₀ μ₁) ν = app⇉ (⇉-subst μ₀ ν) (⇉-subst μ₁ ν)
-- ⇉-subst {X} {P} {P'} {Q} {Q'} (red⇉ {M} {M'} {N} {N'} μ₀ μ₁) ν = ⇉≡ (red⇉ (bind⇉subst μ₀ (buildproof ν)) (⇉-subst μ₁ ν)) {!   !}
  -- = ⇉≡ (red⇉ f (⇉-subst μ₁ ν) ) {!   !}
  -- where f = bind⇉ M
                  --  (λ x → Λ↑ (↑→ (io var Q) x))
                  -- (λ x → Λ↑ (↑→ (io var Q') x))
                    --  λ x → Λ↑↑-ext x ν

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

-- 1. Define multi-step parallel reduction, say, =>>, which is a sequence of usual parallel reduction steps, ⇉.  (Just like multi-step beta reduction is to single-step beta reduction.)

data _≡>_ {X : Set} : Λ X → Λ X → Set where
  ε≡> : ∀ {M} → M ≡> M -- Start
  _c≡>_ : ∀ {L M N} → (M ≡> N) → (L ⇉ M) → (L ≡> N)

Conf≡> : ∀ {X : Set} → Λ X → Λ X → Set
Conf≡> = Conf _≡>_

SConf⇉ : ∀ {X : Set} → Λ X → Set
SConf⇉ input = Conf _⇉_ input input

SConf≡> : ∀ {X : Set} → Λ X → Set
SConf≡> input = Conf _≡>_ input input

-- 2. Prove "Strip lemma", if M =>> N and also M ⇉ M', then there is Z such that N ⇉ Z and M' =>> Z.
-- (Hint: Use induction on the thing you just proved, the diamond property for ⇉.)

-- Hiding the fact that the base of Conf has to be Z. // 2nd reduction doesn't matter.
StripLemmaFirst : ∀ {X : Set} {M N M' : Λ X} → M ≡> N → M ⇉ M' → SConf⇉ N -- N ⇉ Z
StripLemmaFirst {X} {M} {.M} {M'} ε≡> single = conf M' single single
StripLemmaFirst {X} {M} {N} {M'} (multi c≡> x) single = 
  let (conf Q l r) = dp⇉ x single
      (conf P l' r') = StripLemmaFirst multi l
  in conf P l' l'

StripLemmaSecond : ∀ {X : Set} {M N M' : Λ X} → M ≡> N → M ⇉ M' → SConf≡> M' -- M' ≡> Z
StripLemmaSecond {X} {M} {.M} {M'} ε≡> single = conf M' ε≡> ε≡>
StripLemmaSecond {X} {M} {N} {M'} (multi c≡> x) single =
  let (conf Q l r) = dp⇉ x single
      (conf P l' r') = StripLemmaSecond multi l
  in conf P (r' c≡> r) (r' c≡> r)

-- 3. Prove that if M =>> N1 and M =>> N2 then there exists Z with N1 =>> Z, N2 =>> Z.

StripLimit : ∀ {X : Set} {M N P : Λ X} (red1 : M ≡> N) (red2 : M ⇉ P) → node (StripLemmaFirst (red1) (red2)) ≡ node (StripLemmaSecond (red1) (red2))
StripLimit ε≡> red2 = refl
StripLimit (red1 c≡> x) red2 =
  let (conf Z l r) = dp⇉ x red2
  in refl ! StripLimit red1 l

=≡> : ∀ {X : Set} {M N P : Λ X} → M ≡> N → N ≡ P → M ≡> P
=≡> red refl = red 

≡>= : ∀ {X : Set} {M N P : Λ X} → M ≡> N → M ≡ P → P ≡> N
≡>= red refl = red 

dp≡> :  ∀ {X : Set} {M N P : Λ X} → M ≡> N → M ≡> P → Conf≡> N P
dp≡> {X} {M} {.M} {P} ε≡> red2 = conf P red2 ε≡>
dp≡> {X} {M} {N} {P} (red1 c≡> x) red2 = 
  let (conf Z l r) = StripLemmaSecond red2 x
      (conf Z₁ l₂ r₂) = StripLemmaFirst red2 x
      (conf G l₁ r₁) = dp≡> red1 r
  in conf G l₁ (≡>= r₁ (~ StripLimit red2 x) c≡> r₂)
  --conf G l₁ (append≡> (=≡> (ε≡> c≡> r₂) (StripLimit red2 x)) r₁) 


-- 4. Prove that if M ⇉ N then M => N (multi-step beta).  Using that, prove if M =>> N then M => N (multistep parellel converts into multistep beta).

absred : ∀ {X : Set} {M N : Λ (↑ X)} → M ⇒ N → abs M ⇒ abs N
absred ε⇒ = ε⇒
absred (x c⇒ red) = abs→ x c⇒ absred red

appred : ∀ {X : Set} {M M' N N' : Λ X} → M ⇒ M' → N ⇒ N' → app M N ⇒ app M' N'
appred ε⇒ ε⇒ = ε⇒
appred ε⇒ (x c⇒ red2) = appR→ x c⇒ appred ε⇒ red2
appred (x c⇒ red1) red2 = appL→ x c⇒ appred red1 red2

redred : ∀ {X : Set} {M M' : Λ (↑ X)} {N N' : Λ X} → M ⇒ M' → N ⇒ N' → app (abs M) N ⇒ M' [ N' ]
redred {X} {M} {.M} {N} ε⇒ ε⇒ = redex M N c⇒ ε⇒
redred ε⇒ (x c⇒ red2) = appR→ x c⇒ redred ε⇒ red2
redred (x c⇒ red1) red2 = appL→ (abs→ x) c⇒ redred red1 red2


append≡> : ∀ {X : Set} {M M' N : Λ X} → M ≡> M' → M' ≡> N → M ≡> N
append≡> ε≡> red2 = red2
append≡> (red1 c≡> x) red2 = append≡> red1 red2 c≡> x

ParltoMB : ∀ {X : Set} {M N : Λ X} → M ⇉ N → M ⇒ N
ParltoMB ε⇉ = ε⇒
ParltoMB (abs⇉ red) = absred (ParltoMB red)
ParltoMB (app⇉ red red₁) = appred (ParltoMB red) (ParltoMB red₁)
ParltoMB (red⇉ red red₁) = redred (ParltoMB red) (ParltoMB red₁) 

MPtoMB : ∀ {X : Set} {M N : Λ X} → M ≡> N → M ⇒ N
MPtoMB ε≡> = ε⇒
MPtoMB (red c≡> x) = append⇒ (ParltoMB x) (MPtoMB red)

-- 5. Prove backward: if M -> N then M ⇉ N.  If M => N then M =>> N.

BtoP : ∀ {X : Set} {M N : Λ X} → M ⟶ N → M ⇉ N
BtoP {X} {.(app (abs M) N)} {.(bind (io var N) M)} (redex M N) = red⇉ (refl⇉ M) (refl⇉ N)
BtoP {X} {.(abs _)} {.(abs _)} (abs→ red) = abs⇉ (BtoP red)
BtoP {X} {.(app _ _)} {.(app _ _)} (appL→ {Z} {P} {Q} red) = app⇉ (BtoP red) (refl⇉ Q)
BtoP {X} {.(app _ _)} {.(app _ _)} (appR→ {Z} {P} {Q} red) = app⇉ (refl⇉ Z) (BtoP red)

ParltoMP : ∀ {X : Set} {M N : Λ X} → M ⇉ N → M ≡> N
ParltoMP {X} {M} {N} red = ε≡> c≡> red

MBtoMP : ∀ {X : Set} {M N : Λ X} → M ⇒ N → M ≡> N
MBtoMP ε⇒ = ε≡>
MBtoMP (x c⇒ red) = append≡> (ParltoMP (BtoP x)) (MBtoMP red)

-- 6.  Use the above facts to prove dp for =>.  AKA The Church-Rosser Theorem.

Conf⇒ : ∀ {X : Set} → Λ X → Λ X → Set
Conf⇒ = Conf _⇒_

=⇒ : ∀ {X : Set} {M N P : Λ X} → M ⇒ N → N ≡ P → M ⇒ P
=⇒ red refl = red

cr⇒ : ∀ {X : Set} {M N : Λ X} → M ⇒ N → ∀ {L : Λ X} → M ⇒ L → Conf⇒ N L
cr⇒ {X} {M} {.M} ε⇒ {L} red2 = conf L red2 ε⇒
cr⇒ {X} {M} {N} (x c⇒ red1) {.M} ε⇒ = conf N ε⇒ (x c⇒ red1)
cr⇒ {X} {M} {N} (x c⇒ red1) {L} (x₁ c⇒ red2) = 
  let (conf Z l r) = dp⇉ (BtoP x) (BtoP x₁)
      seered2 = MBtoMP red2
      seer = ParltoMP r
      (conf Q l₁ r₁) = dp≡> seer seered2
      seered1 = MBtoMP red1
      seel = ParltoMP l
      (conf Q' l₂ r₂) = dp≡> seel seered1
      (conf G l₃ r₃) = dp≡> l₁ l₂
  in conf G (append⇒ (MPtoMB r₂) (MPtoMB r₃)) (append⇒ (MPtoMB r₁) (MPtoMB l₃))

module Example2 where
I : Λ⁰
I = abs (var o)



ω : Λ⁰
ω = abs (app (var o) (var o))

randomthing : Λ⁰
randomthing = abs (app (var o) (abs (app (var o) (var (i o)))))

Term : Λ⁰
Term = app ω (app I I)

Reduct1 : Λ⁰
Reduct1 = app ω I

Reduct2 : Λ⁰
Reduct2 = app (app I I) (app I I)

Reduct3 : Λ⁰
Reduct3 = app I I

Red1 : Term ⇒ Reduct1
Red1 = appR→ (redex (var o) I) c⇒ ε⇒

Red2 : Term ⇒ Reduct2
Red2 = redex (app (var o) (var o)) (app I I) c⇒ ε⇒

Terminal : Λ⁰
Terminal = node (cr⇒ Red1 Red2)

Red3 : Term ⇒ Reduct3
Red3 = redex (app (var o) (var o)) (app I I) 
  c⇒ (appL→ (redex (var o) (abs (var o))) 
  c⇒ (redex (var o) (app (abs (var o)) (abs (var o))) 
  c⇒ ε⇒))

Terminal1 : Λ⁰
Terminal1 = node (cr⇒ Red1 Red3)

Terminal2 : Λ⁰
Terminal2 = node (cr⇒ Red2 Red3)
open Example2

module Standarization where

data _→w_ {X : Set} : Λ X → Λ X → Set where
  ε→w : ∀ {M N}  → app (abs M) N →w (M [ N ])
  _c→w_ : ∀ {M N} (Z : Λ X) → M →w N → app M Z →w app N Z

data _→s_ {X : Set} : Λ X → Λ X → Set where
  ε→s :   ∀ {x : X} → var x →s var x
  app→s : ∀ {M M' N N'} → M →s M' → N →s N' → app M N →s app M' N'
  abs→s : ∀ {M} {N} → M →s N → abs M →s abs N
  append→s : ∀ {M M' N} → M →w M' → M' →s N → M →s N

refl→s :  ∀ {X : Set} (M : Λ X) → M →s M
refl→s (var x) = ε→s
refl→s (app M M₁) = app→s (refl→s M) (refl→s M₁)
refl→s (abs M) = abs→s (refl→s M)

wtos : ∀ {X : Set} {M N : Λ X} → M →w N → M →s N
wtos ε→w = append→s ε→w (refl→s _)
wtos (Z c→w red) = app→s (wtos red) (refl→s Z)

-- Data Rel x y, Equ y ≡ y' > Rel x y'
Rel : Set → Set₁
Rel X = X → X → Set

data _* {X : Set} (R : Rel X) : Rel X where
  ε* : ∀ (x : X) → (R *) x x
  c* : ∀ {x y z : X} → R x y → (R *) y z → (R *) x z

append : ∀ {X : Set} {R : Rel X} {x y z : X} → (R *) x y → (R *) y z → (R *) x z
append (ε* x) yz = yz
append (c* r xy) yz = c* r (append xy yz)

≡R : ∀ {X : Set} {R : Rel X} {x y z : X} → R x y → y ≡ z → R x z 
≡R input refl = input

≡→s' : ∀ {X : Set} {M N N' : Λ X} → M →s N → N ≡ N' → M →s N'
≡→s' = ≡R {R = _→s_}

≡→w :  ∀ {X : Set}  {M N N' : Λ X} → M →w N → N ≡ N' → M →w N'
≡→w red refl = red

≡→s :  ∀ {X : Set}  {M N N' : Λ X} → M →s N → N ≡ N' → M →s N'
≡→s red refl = red

≡→sf :  ∀ {X : Set}  {M N M' : Λ X} → M →s N → M ≡ M' → M' →s N
≡→sf red refl = red


-- randomred : ∀ {X : Set}  {M M' : Λ X} {N : Λ (↑ X)} → M →s M' → bind (io var M) N → bind (io var M') N
-- randomred red = ?


isthistrue : ∀ {X : Set} → Λ↑ ∘ i ≃ Λ→ {X = X} i
isthistrue x = refl



i→w : ∀ {X : Set} {x y : Λ X} → x →w y → Λ↑ (i x) →w Λ↑ (i y)
i→w {X} {(app (abs M) N)} {.(bind (io var N) M)} ε→w = ≡→w (ε→w) ((~ bind-nat2 (↑→ i) (io var (Λ→ i N)) M) !
   ((~ ext≃ (bind-ext (io-var-nat i N)) (refl {a = M})) 
   ! (~ bind-nat1 i (io var N) M)))
  -- (((~ bind-nat2 (↑→ i) (io var (Λ→ i N)) M) ! (~ ext≃ (bind-ext {f = Λ→ i ∘ io var N} {g = io var (Λ→ i N) ∘ ↑→ i} (io-var-nat i N)) refl)) ! (~ bind-nat1 i (io var N) M))
i→w (Z c→w red) = Λ→ (λ z → i z) Z c→w i→w red

Λ→→w : ∀ {X Y : Set} {x y : Λ (↑ X)} (f : (↑ X) → Y) → x →w y → Λ→ f x →w Λ→ f y
Λ→→w {X} {Y} {(app (abs M) N)} {.(bind (io var N) M)} f ε→w = ≡→w ε→w 
  (~ (bind-nat1 f (io var N) M ! (ext≃ (bind-ext (io-var-nat f N)) (refl {a = M}) ! bind-nat2 (↑→ f) (io var (Λ→ f N)) M)))
Λ→→w {X} {Y} {.(app _ Z)} {.(app _ Z)} f (Z c→w red) = Λ→ f Z c→w Λ→→w f red

Λ→→s : ∀ {X Y : Set} {x y : Λ (↑ X)} (f : (↑ X) → Y) → x →s y → Λ→ f x →s Λ→ f y
Λ→→s f ε→s = ε→s
Λ→→s f (app→s red red₁) = app→s (Λ→→s f red) (Λ→→s f red₁)
Λ→→s f (abs→s red) = abs→s (Λ→→s (↑→ f) red)
Λ→→s f (append→s x red) = append→s (Λ→→w f x) (Λ→→s f red)

i→s : ∀ {X : Set} {x y : Λ X} → x →s y → Λ↑ (i x) →s Λ↑ (i y)
i→s ε→s = ε→s
i→s (app→s red red₁) = app→s (i→s red) (i→s red₁)
i→s (abs→s red) = abs→s (Λ→→s (↑→ i) red)
i→s (append→s x red) = append→s (i→w x) (i→s red)

liftprfs : ∀ {X Y : Set} {f g : X → Λ Y}
          → (∀ (x : X) → f x →s g x)
          → ((x : ↑ X) → Λ↑ (↑→ f x) →s Λ↑ (↑→ g x))
liftprfs {X} {Y} {f} {g} prf = λ { (i x) → i→s (prf x) ; o → ε→s }

bind→wrandom : ∀ {X Y : Set} {M1 M2 : Λ X} {f : X → Λ Y} → M1 →w M2 → bind f M1 →w bind f M2
bind→wrandom {X} {Y} {(app (abs M) N)} {.(bind (io var N) M)} {f} ε→w = ≡→w ε→w ((((~ bind-law (Λ↑ ∘ ↑→ f) (io var (bind f N)) M) ! bind-ext (typesquare f N) M) ! bind-law (io var N) f M))
bind→wrandom (Z c→w red) = bind _ Z c→w bind→wrandom red

bind→ssubst : ∀ {X Y : Set} {M1 M2 : Λ X} → M1 →s M2
             → ∀ {f g : X → Λ Y}
             → (∀ x → f x →s g x)
             → bind f M1 →s bind g M2
bind→ssubst ε→s prf = prf _
bind→ssubst (app→s red red₁) prf = app→s (bind→ssubst red prf) (bind→ssubst red₁ prf)
bind→ssubst (abs→s red) prf = abs→s (bind→ssubst red (liftprfs prf))
bind→ssubst (append→s x red) prf = append→s (≡→w (bind→wrandom x) refl) (bind→ssubst red prf)

redsubst→sprf : ∀ {X : Set}  {M M' : Λ X} (x : ↑ X) → M →s M' → io var M x →s io var M' x
redsubst→sprf (i x) red = ε→s
redsubst→sprf o red = red

redsubst→s : ∀ {X : Set}  {M M' : Λ X} (N : Λ (↑ X)) → M →s M' → N [ M ] →s N [ M' ]
redsubst→s N red = bind→ssubst (refl→s N) (λ x → redsubst→sprf x red)

subst→s : ∀ {X : Set}  {N N' : Λ X} {M M' : Λ (↑ X)} → M →s M' → N →s N' → M [ N ] →s M' [ N' ]
subst→s red red2 = bind→ssubst red λ { (i x) -> ε→s ; o -> red2 } 

data Nat : Set where
  O : Nat
  S : Nat → Nat

_++_ : Nat → Nat → Nat
O ++ n = n
(S m) ++ n = S (m ++ n)

len : ∀ {X : Set} {M M' : Λ X} → M →s M' → Nat
len ε→s = O
len (app→s r r₁) = len r ++ len r₁
len (abs→s r) = len r
len (append→s x r) = S (len r)

data lenOf {X : Set} : ∀ {M M' : Λ X} → M →s M' → Nat → Set where
  lenε   : ∀ {x : X} → lenOf (ε→s {X} {x}) O
  lenApp : ∀ {M M' N N'} → (r0 : M →s M') → (r1 : N →s N') → (m n : Nat)
          → lenOf r0 m → lenOf r1 n → lenOf (app→s r0 r1) (m ++ n)
  lenAbs : ∀ {M} {N} → (r0 : M →s N) → (m : Nat) → lenOf r0 m → lenOf (abs→s r0) m
  lenRed : ∀ {M M' N} → (x : M →w M') → (r : M' →s N) → (m : Nat)
          → lenOf r m → lenOf (append→s x r) (S m)

specialcasetranssw : ∀ {X : Set} {N M : Λ X} {M' : Λ (↑ X)} (r : M →s app (abs M') N)
                       → (n : Nat) → lenOf r n → M →s M' [ N ]
specialcasetranssw .(app→s (abs→s r0) r1) .n (lenApp (abs→s r0) r1 O n prf prf₁) = append→s ε→w (subst→s r0 r1)
specialcasetranssw .(app→s (abs→s r0) r1) .(S (m ++ n)) (lenApp (abs→s r0) r1 (S m) n prf prf₁) = append→s ε→w (subst→s r0 r1 )
specialcasetranssw .(app→s (append→s x r0) r1) .(S (m ++ n)) (lenApp (append→s x r0) r1 .(S m) n (lenRed .x .r0 m prf) prf₁) = append→s (_ c→w x) (specialcasetranssw (app→s r0 r1) (m ++ n) (lenApp r0 r1 m n prf  prf₁))
specialcasetranssw .(append→s x r) .(S m) (lenRed x r m prf) = append→s x (specialcasetranssw r m prf)

WhyDrP : ∀ {X : Set} {M M' : Λ X} → (r : M →s M') → lenOf r (len r)
WhyDrP ε→s = lenε
WhyDrP (app→s red red₁) = lenApp red red₁ (len red) (len red₁) (WhyDrP red) (WhyDrP red₁)
WhyDrP (abs→s red) = lenAbs red (len red) (WhyDrP red)
WhyDrP (append→s x red) = lenRed x red (len red) (WhyDrP red)

trans→sw : ∀ {X : Set} {M M' N : Λ X} → M →s M' → M' →w N → M →s N
trans→sw red ε→w = specialcasetranssw red (len red) (WhyDrP red)
trans→sw (app→s red1 red3) (Z c→w red2) = app→s (trans→sw red1 red2) red3
trans→sw (append→s x red1) (Z c→w red2) = append→s x (trans→sw red1 (Z c→w red2))

trans→s : ∀ {X : Set} {M M' N : Λ X} → M →s M' → M' →s N → M →s N
trans→s ε→s red2 = red2
trans→s (app→s red1 red3) (app→s red2 red4) = app→s (trans→s red1 red2) (trans→s red3 red4)
trans→s (app→s red1 red3) (append→s x red2) = trans→s (trans→sw (app→s red1 red3) x) red2 
trans→s (abs→s red1) (abs→s red2) = abs→s (trans→s red1 red2)
trans→s (append→s x red1) red2 = append→s x (trans→s red1 red2)

singlestepstand : ∀ {X : Set} {M M' N : Λ X} → M →s M' → M' ⟶ N → M →s N
singlestepstand (app→s (abs→s red1) red3) (redex M _) = trans→s (wtos ε→w) (subst→s red1 red3)
singlestepstand (app→s (append→s x red1) red3) (redex M _) = trans→s (app→s (append→s x red1) red3) (wtos ε→w)
singlestepstand (app→s red1 red3) (appL→ red2) = app→s (singlestepstand red1 red2) red3
singlestepstand (app→s red1 red3) (appR→ red2) = app→s red1 (singlestepstand red3 red2)
singlestepstand (abs→s red1) (abs→ red2) = abs→s (singlestepstand red1 red2)
singlestepstand (append→s x red1) red2 = trans→s (wtos x) (singlestepstand red1 red2)

multistepstand : ∀ {X : Set} {M M' N : Λ X} → M →s M' → M' ⇒ N → M →s N
multistepstand red1 ε⇒ = red1
multistepstand red1 (x c⇒ red2) = trans→s red1 (multistepstand (singlestepstand (refl→s _) x) red2)

standarization : ∀ {X : Set} {M N : Λ X} → M ⇒ N → M →s N
standarization ε⇒ = refl→s _
standarization (x c⇒ red) = trans→s (singlestepstand (refl→s _) x) (multistepstand (refl→s _) red)


open Standarization
