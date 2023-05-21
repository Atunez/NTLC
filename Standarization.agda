module Standarization where

open import Lambda

data _→w_ {X : Set} : Rel (Λ X) where
  ε→w : ∀ {M N}  → app (abs M) N →w (M [ N ])
  _c→w_ : ∀ {M N} (Z : Λ X) → M →w N → app M Z →w app N Z

data _→s_ {X : Set} : Rel (Λ X) where
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

≡→s : ∀ {X : Set} {M N N' : Λ X} → M →s N → N ≡ N' → M →s N'
≡→s = ≡R {R = _→s_}

≡→w :  ∀ {X : Set}  {M N N' : Λ X} → M →w N → N ≡ N' → M →w N'
≡→w = ≡R {R = _→w_}

i→w : ∀ {X : Set} {x y : Λ X} → x →w y → Λ↑ (i x) →w Λ↑ (i y)
i→w {X} {(app (abs M) N)} {.(bind (io var N) M)} ε→w = ≡→w (ε→w) 
   ((~ bind-nat2 (↑→ i) (io var (Λ→ i N)) M) !
   ((~ ext≃ (bind-ext (io-var-nat i N)) (refl {a = M})) 
   ! (~ bind-nat1 i (io var N) M)))
i→w (Z c→w red) = Λ→ (λ z → i z) Z c→w i→w red
      
Λ→→w : ∀ {X Y : Set} {x y : Λ (↑ X)} (f : (↑ X) → Y) → x →w y → Λ→ f x →w Λ→ f y
Λ→→w {X} {Y} {(app (abs M) N)} {.(bind (io var N) M)} f ε→w = ≡→w ε→w 
  (~ (bind-nat1 f (io var N) M ! (ext≃ (bind-ext (io-var-nat f N)) (refl {a = M}) 
  ! bind-nat2 (↑→ f) (io var (Λ→ f N)) M)))
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

bind→wsubst : ∀ {X Y : Set} {M1 M2 : Λ X} {f : X → Λ Y} → M1 →w M2 → bind f M1 →w bind f M2
bind→wsubst {X} {Y} {(app (abs M) N)} {.(bind (io var N) M)} {f} ε→w = ≡→w ε→w 
  ((((~ bind-law (Λ↑ ∘ ↑→ f) (io var (bind f N)) M) ! 
  bind-ext (λ { (i x) → (~ bind-nat2 i (io var (bind f N)) (f x)) 
  ! buildproofv2 (f x) ; o → refl}) M) ! bind-law (io var N) f M))
bind→wsubst (Z c→w red) = bind _ Z c→w bind→wsubst red

bind→ssubst : ∀ {X Y : Set} {M1 M2 : Λ X} → M1 →s M2
             → ∀ {f g : X → Λ Y}
             → (∀ x → f x →s g x)
             → bind f M1 →s bind g M2
bind→ssubst ε→s prf = prf _
bind→ssubst (app→s red red₁) prf = app→s (bind→ssubst red prf) (bind→ssubst red₁ prf)
bind→ssubst (abs→s red) prf = abs→s (bind→ssubst red λ { (i x) → i→s (prf x) ; o → ε→s })
bind→ssubst (append→s x red) prf = append→s (≡→w (bind→wsubst x) refl) (bind→ssubst red prf)

redsubst→s : ∀ {X : Set}  {M M' : Λ X} (N : Λ (↑ X)) → M →s M' → N [ M ] →s N [ M' ]
redsubst→s N red = bind→ssubst (refl→s N) λ {(i x) → ε→s ; o → red}

subst→s : ∀ {X : Set}  {N N' : Λ X} {M M' : Λ (↑ X)} → M →s M' → N →s N' → M [ N ] →s M' [ N' ]
subst→s red red2 = bind→ssubst red λ { (i x) -> ε→s ; o -> red2 } 

-- Checker Problems workaround.

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
specialcasetranssw .(app→s (abs→s r0) r1) .n (lenApp (abs→s r0) r1 O n prf prf₁) =
 append→s ε→w (subst→s r0 r1)
specialcasetranssw .(app→s (abs→s r0) r1) .(S (m ++ n)) 
  (lenApp (abs→s r0) r1 (S m) n prf prf₁) = append→s ε→w (subst→s r0 r1 )
specialcasetranssw .(app→s (append→s x r0) r1) .(S (m ++ n)) 
  (lenApp (append→s x r0) r1 .(S m) n (lenRed .x .r0 m prf) prf₁) =
  append→s (_ c→w x) (specialcasetranssw (app→s r0 r1) (m ++ n) (lenApp r0 r1 m n prf  prf₁))
specialcasetranssw .(append→s x r) .(S m) (lenRed x r m prf) = 
  append→s x (specialcasetranssw r m prf)

BuildLenRed : ∀ {X : Set} {M M' : Λ X} → (r : M →s M') → lenOf r (len r)
BuildLenRed ε→s = lenε
BuildLenRed (app→s red red₁) = 
  lenApp red red₁ (len red) (len red₁) (BuildLenRed red) (BuildLenRed red₁)
BuildLenRed (abs→s red) = lenAbs red (len red) (BuildLenRed red)
BuildLenRed (append→s x red) = lenRed x red (len red) (BuildLenRed red)

-- End of workaround

trans→sw : ∀ {X : Set} {M M' N : Λ X} → M →s M' → M' →w N → M →s N
trans→sw red ε→w = specialcasetranssw red (len red) (BuildLenRed red)
trans→sw (app→s red1 red3) (Z c→w red2) = app→s (trans→sw red1 red2) red3
trans→sw (append→s x red1) (Z c→w red2) = append→s x (trans→sw red1 (Z c→w red2))

trans→s : ∀ {X : Set} {M M' N : Λ X} → M →s M' → M' →s N → M →s N
trans→s ε→s red2 = red2
trans→s (app→s red1 red3) (app→s red2 red4) = app→s (trans→s red1 red2) (trans→s red3 red4)
trans→s (app→s red1 red3) (append→s x red2) = trans→s (trans→sw (app→s red1 red3) x) red2 
trans→s (abs→s red1) (abs→s red2) = abs→s (trans→s red1 red2)
trans→s (append→s x red1) red2 = append→s x (trans→s red1 red2)

singlestepstand : ∀ {X : Set} {M M' N : Λ X} → M →s M' → M' ⟶ N → M →s N
singlestepstand (app→s (abs→s red1) red3) (redex M _) = 
  trans→s (wtos ε→w) (subst→s red1 red3)
singlestepstand (app→s (append→s x red1) red3) (redex M _) = 
  trans→s (app→s (append→s x red1) red3) (wtos ε→w)
singlestepstand (app→s red1 red3) (appL→ red2) = app→s (singlestepstand red1 red2) red3
singlestepstand (app→s red1 red3) (appR→ red2) = app→s red1 (singlestepstand red3 red2)
singlestepstand (abs→s red1) (abs→ red2) = abs→s (singlestepstand red1 red2)
singlestepstand (append→s x red1) red2 = trans→s (wtos x) (singlestepstand red1 red2)

multistepstand : ∀ {X : Set} {M M' N : Λ X} → M →s M' → M' ⇒ N → M →s N
multistepstand red1 (ε* _) = red1
multistepstand red1 (c* x red2) = trans→s red1 (multistepstand (singlestepstand (refl→s _) x) red2)

standarization : ∀ {X : Set} {M N : Λ X} → M ⇒ N → M →s N
standarization (ε* _) = refl→s _
standarization (c* x red) = trans→s (singlestepstand (refl→s _) x) (multistepstand (refl→s _) red)
