module ChurchRosserTheorem where

open import Lambda

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
Conf⇉ : ∀ {X : Set} → Rel (Λ X)
Conf⇉ = Conf _⇉_

Conf≡> : ∀ {X : Set} → Rel (Λ X)
Conf≡> = Conf _≡>_

Conf⇒ : ∀ {X : Set} → Rel (Λ X)
Conf⇒ = Conf _⇒_

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
      Z = Z₀ [ Z₁ ]ₒ
      l = red⇉ l₀ l₁
      r = ⇉-subst r₀ r₁
  in  conf Z l r
dp⇉ (red⇉ ρ₀ ρ₁) (app⇉ (abs⇉ σ₀) σ₁) = 
  let (conf Z₁ l₁ r₁) = dp⇉ σ₁ ρ₁
      (conf Z₀ l₀ r₀) = dp⇉ σ₀ ρ₀
      Z = Z₀ [ Z₁ ]ₒ
      l = red⇉ l₀ l₁
      r = ⇉-subst r₀ r₁
  in conf Z r l
dp⇉ (red⇉ ρ₀ ρ₁) (red⇉ σ₀ σ₁) = 
  let (conf Z₁ l₁ r₁) = dp⇉ σ₁ ρ₁
      (conf Z₀ l₀ r₀) = dp⇉ σ₀ ρ₀
      Z = Z₀ [ Z₁ ]ₒ
      l = ⇉-subst r₀ r₁
      r = ⇉-subst l₀ l₁
  in conf Z l r


StripLemmaFirst : ∀ {X : Set} {M N M' : Λ X} → M ≡> N → M ⇉ M' → SConf⇉ N -- N ⇉ Z
StripLemmaFirst  {X} {M} {.M} {M'} (ε* _) single = conf M' single single
StripLemmaFirst (c* x multi) single =
  let (conf Q l r) = dp⇉ x single
      (conf P l' r') = StripLemmaFirst multi l
  in conf P l' l'

StripLemmaSecond : ∀ {X : Set} {M N M' : Λ X} → M ≡> N → M ⇉ M' → SConf≡> M' -- M' ≡> Z
StripLemmaSecond {X} {M} {.M} {M'} (ε* _) single = conf M' (ε* _) (ε* _)
StripLemmaSecond {X} {M} {N} {M'} (c* x multi) single =
  let (conf Q l r) = dp⇉ x single
      (conf P l' r') = StripLemmaSecond multi l
  in conf P (c* r r') (c* r r')

StripLimit : ∀ {X : Set} {M N P : Λ X} (red1 : M ≡> N) (red2 : M ⇉ P) → node (StripLemmaFirst (red1) (red2)) ≡ node (StripLemmaSecond (red1) (red2))
StripLimit (ε* _) red2 = refl
StripLimit (c* x red1) red2 =
  let (conf Z l r) = dp⇉ x red2
  in StripLimit red1 l

dp≡> :  ∀ {X : Set} {M N P : Λ X} → M ≡> N → M ≡> P → Conf≡> N P
dp≡> {X} {M} {.M} {P} (ε* _) red2 = conf P red2 (ε* _)
dp≡> {X} {M} {N} {P} (c* x red1) red2 = 
  let (conf Z l r) = StripLemmaSecond red2 x
      (conf Z₁ l₂ r₂) = StripLemmaFirst red2 x
      (conf G l₁ r₁) = dp≡> red1 r
  in conf G l₁ (c* (⇉≡ r₂ (StripLimit red2 x)) r₁)

-- Helper Functions Start

absred : ∀ {X : Set} {M N : Λ (↑ X)} → M ⇒ N → abs M ⇒ abs N
absred (ε* _) = (ε* _)
absred (c* x input) = c* (abs→ x) (absred input)

appred : ∀ {X : Set} {M M' N N' : Λ X} → M ⇒ M' → N ⇒ N' → app M N ⇒ app M' N'
appred (ε* _) (ε* _) = (ε* _)
appred (ε* _) (c* x input2) = c* (appR→ x) (appred (ε* _) input2)
appred (c* x input1) input2 = c* (appL→ x) (appred input1 input2)

redred : ∀ {X : Set} {M M' : Λ (↑ X)} {N N' : Λ X} → M ⇒ M' → N ⇒ N' → app (abs M) N ⇒ M' [ N' ]ₒ
redred (ε* _) (ε* _) = c* (redex _ _) (ε* _)
redred (ε* _) (c* x input2) = c* (appR→ x) (redred (ε* _) input2)
redred (c* x input1) input2 = c* (appL→ (abs→ x)) (redred input1 input2)

-- Helper Functions End


ParltoMB : ∀ {X : Set} {M N : Λ X} → M ⇉ N → M ⇒ N
ParltoMB ε⇉ = ε* _
ParltoMB (abs⇉ red) = absred (ParltoMB red)
ParltoMB (app⇉ red red₁) = appred (ParltoMB red) (ParltoMB red₁)
ParltoMB (red⇉ red red₁) = redred (ParltoMB red) (ParltoMB red₁)

MPtoMB : ∀ {X : Set} {M N : Λ X} → M ≡> N → M ⇒ N
MPtoMB (ε* _) = (ε* _)
MPtoMB (c* x red) = append⇒ (ParltoMB x) (MPtoMB red)

BtoP : ∀ {X : Set} {M N : Λ X} → M ⟶ N → M ⇉ N
BtoP (redex M N) = red⇉ (refl⇉ M) (refl⇉ N)
BtoP (abs→ red) = abs⇉ (BtoP red)
BtoP (appL→ {Z} {P} {Q} red) = app⇉ (BtoP red) (refl⇉ Q)
BtoP (appR→ {Z} {P} {Q} red) = app⇉ (refl⇉ Z) (BtoP red)

ParltoMP : ∀ {X : Set} {M N : Λ X} → M ⇉ N → M ≡> N
ParltoMP red = c* red (ε* _)

MBtoMP : ∀ {X : Set} {M N : Λ X} → M ⇒ N → M ≡> N
MBtoMP (ε* _) = (ε* _)
MBtoMP (c* x input) = append≡> (ParltoMP (BtoP x)) (MBtoMP input)

cr⇒ : ∀ {X : Set} {M N : Λ X} → M ⇒ N → ∀ {L : Λ X} → M ⇒ L → Conf⇒ N L
cr⇒ (ε* _) {L} red2 = conf L red2 (ε* _)
cr⇒ {X} {M} {N} (c* x red1) {.M} (ε* _) = conf N (ε* _) (c* x red1)
cr⇒ {X} {M} {N} (c* x red1) {L} (c* x₁ red2) = 
  let (conf Z l r) = dp⇉ (BtoP x) (BtoP x₁)
      seered2 = MBtoMP red2
      seer = ParltoMP r
      (conf Q l₁ r₁) = dp≡> seer seered2
      seered1 = MBtoMP red1
      seel = ParltoMP l
      (conf Q' l₂ r₂) = dp≡> seel seered1
      (conf G l₃ r₃) = dp≡> l₁ l₂
  in conf G (append⇒ (MPtoMB r₂) (MPtoMB r₃)) (append⇒ (MPtoMB r₁) (MPtoMB l₃))
