module Cycles2 where

open import Lambda public

-- open import Agda.Builtin.Sigma


eqParts : ∀ {X : Set} {M N M' N' : Λ X} → app M N ≡ app M' N' → M ≡ M' × N ≡ N'
eqParts refl = refl , refl

eqAbs : ∀ {X : Set} {M N : Λ (↑ X)} → abs M ≡ abs N → M ≡ N
eqAbs refl = refl

lenTerm : ∀ {X : Set} → Λ X → Nat
lenTerm (var x) = O
lenTerm (app x x₁) = S (lenTerm x ++ lenTerm x₁)
lenTerm (abs x) = S (lenTerm x)

data _∈_ {X : Set} (x : X) : Λ X → Set where
  here  : x ∈ var x
  left  : ∀ {s : Λ X} → (x ∈ s) → (t : Λ X) → x ∈ app s t
  right : ∀ (s : Λ X) → {t : Λ X} → (x ∈ t) → x ∈ app s t
  down  : ∀ {r : Λ (↑ X)} → (i x ∈ r) → (x ∈ abs r)

data Bool : Set where
  True : Bool
  False : Bool

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

dec2decAt : ∀ {X} → dec X → (x : X) → decAt X x
dec2decAt d x y = d x y

decAto : ∀ {X} → decAt (↑ X) o
decAto (i x) = inr (λ {()})
decAto o = inl refl

decAti : ∀ {X} x → decAt X x → decAt (↑ X) (i x)
decAti x p (i y) with p y
...                 | inl e = inl (ext i e)
...                 | inr n = inr λ {(refl) → n refl }
decAti x p o = inr (λ {()})

decio↑  : ∀ {X} → ∀ (x : ↑ X) → x ≡ o ⊔ ¬ (x ≡ o)
decio↑  (i x) = inr λ {()}
decio↑  o = inl refl


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


mapKeepsLength : ∀ {X Y : Set} → (f : X → Y) → (M : Λ X) → lenTerm M ≡ lenTerm (Λ→ f M)
mapKeepsLength f (var x) = refl
mapKeepsLength f (app M₁ M₂) = ext S (tran++ (mapKeepsLength f M₁)  (mapKeepsLength f M₂) )
mapKeepsLength f (abs M₀) = ext S (mapKeepsLength (↑→ f) M₀ )

ω : Λ ⊥
ω = abs (app (var o) (var o))

app≡inv : ∀ {X} {M M' N N' : Λ X} → app M N ≡ app M' N' → M ≡ M' × N ≡ N'
app≡inv refl = ( refl , refl )

abs≡inv : ∀ {X} {M M' : Λ (↑ X)} → abs M ≡ abs M' → M ≡ M'
abs≡inv refl = refl

var≡inv : ∀ {X} {M M' : X} → var M ≡ var M' → M ≡ M'
var≡inv refl = refl

bind-occurs : ∀ {X Y : Set} (f g : X → Λ Y) (t : Λ X)
                → (∀ x → x ∈ t → f x ≡ g x) → bind f t ≡ bind g t
bind-occurs f g (var x) fn = fn x here
bind-occurs f g (app t t₁) fn = app≡ (bind-occurs f g t (λ x z → fn x (left z t₁))) (bind-occurs f g t₁ (λ x z → fn x (right t z)))
bind-occurs f g (abs t) fn = abs≡ (bind-occurs (Λ↑ ∘ ↑→ f) (Λ↑ ∘ ↑→ g) t λ {(i x) → λ q → ext (Λ↑ ∘ i) (fn x (down q)) ; o → λ _ → refl})

map-occurs : ∀ {X Y : Set} (f g : X → Y) (t : Λ X)
                → (∀ x → x ∈ t → f x ≡ g x) → Λ→ f t ≡ Λ→ g t
map-occurs f g t h =
  let f' = mapIsBind f
      g' = symm (mapIsBind g)
      h' = (λ x occ → ext var (h x occ) )
   in f' t ! bind-occurs (var ∘ f) (var ∘ g) t h' ! g' t

occurs-map : ∀ {X} (A : Λ (↑ X)) (B : Λ X) → A [ B ] ≡ B → ¬ (o ∈ A) → A ≡ Λ→ i B
occurs-map A B h nocc =
  let e0 : ∀ x → x ∈ A → var x ≡ (Λ→ i ∘ io var B) x
      e0 = (λ { (i x) → λ p → refl ; o → exfalso ∘ nocc })
      e1 = symm (bind-nat1 i (io var B))
      e2 = bind-occurs (var) (Λ→ i ∘ io var B) A e0
   in (~ bind-unit1 A) !  (e2 ! (e1 A ! ext (Λ→ i) h))

occursLemmaLen : ∀ {X} {Y} (f : X → Λ Y) (A : Λ X) (x : X) → x ∈ A → lenTerm (bind f A) ≤ lenTerm (f x) → A ≡ var x
occursLemmaLen f .(var x) x here l = refl
occursLemmaLen f (app s t) x (left occ t) l =
  let x1 = occursLemmaLen f s x occ
      x2 = add>S (lenTerm (bind f s)) (lenTerm (bind f t))
      x3 = x1 (lelte x2 l)
      x4 = ≤-eq {l = lenTerm (bind f s)} l (ext lenTerm (~ ext (bind f) x3))
   in exfalso (lestrict x2 x4)
occursLemmaLen f (app s t) x (right s occ) l =
  let x1 = occursLemmaLen f t x occ
      x2 = add>S (lenTerm (bind f t)) (lenTerm (bind f s))
      x3 = x1 (lelte x2 (++S≤ {n = lenTerm (bind f t)} l))
      x4 = ≤-eq (++S≤ {n = lenTerm (bind f t)} l) (ext lenTerm (~ ext (bind f) x3))
   in exfalso (lestrict x2 x4)
occursLemmaLen f (abs r) x (down occ) l =
  let x1 = occursLemmaLen (Λ↑ ∘ ↑→ f) r (i x) occ
      x2 = mapKeepsLength i (f x)
      x3 = lelte (<S _) (≤-eq l x2)
      x4 = x1 x3
      x5 = ≡≤ (ext S (x2 ! ext lenTerm (ext (bind (Λ↑ ∘ ↑→ f)) (~ x4)) ) ) l
   in exfalso (lestrict (<S (lenTerm (f x))) x5)


occursLemma : ∀ {X} {Y} (f : X → Λ Y) (A : Λ X) (x : X) → x ∈ A → bind f A ≡ f x → A ≡ var x
occursLemma f A x occ eq = occursLemmaLen f A x occ (≤≡ (ext (lenTerm) eq))

occursLemma' : ∀ {X} {Y} (f : X → Λ Y) (A : Λ X) (x : X) → x ∈ A → A ≡ var x ⊔ ¬ (bind f A ≡ f x)
occursLemma' f .(var x) x here = inl refl
occursLemma' f (app s t) x (left occ t) = inr aux where
  ol = occursLemma f (app s t) x (left occ t)
  aux : ¬ (app (bind f s) (bind f t) ≡ f x)
  aux p with ol p
  ...      | ()
occursLemma' f (app s t) x (right s occ) = inr aux where
  ol = occursLemma f (app s t) x (right s occ)
  aux : ¬ (app (bind f s) (bind f t) ≡ f x)
  aux p with ol p
  ...      | ()
occursLemma' f (abs r) x (down occ) = inr aux where
  ol : abs (bind (Λ↑ ∘ ↑→ f) r) ≡ f x → abs r ≡ var x
  ol = occursLemma f (abs r) x (down occ)
  aux : ¬ (abs (bind (Λ↑ ∘ ↑→ f) r) ≡ f x)
  aux p with ol p
  ...      | ()


lercherEq3 : ∀ {X} (A : Λ X) (B : Λ (↑ X)) → B [ A ] ≡ A → B ≡ var o ⊔ B ≡ Λ→ i A
lercherEq3 A B e with decΛ decAto B
...                 | inr no  = inr (occurs-map B A e no )
...                 | inl yes with occursLemma' (io var A) B o yes
...                              | inl yesvar = inl yesvar
...                              | inr notvar = exfalso (notvar e)


_∧_ : ∀ (X Y : Bool) → Bool
True ∧ Y = Y
False ∧ Y = False

IfThenElse : ∀ {X : Set} → (V : Bool) → (A B : X) → X
IfThenElse True a b = a
IfThenElse False a b = b

∧-elim : ∀ (X Y : Bool) → X ∧ Y ≡ False → X ≡ False ⊔ Y ≡ False
∧-elim True Y prf = inr prf
∧-elim False Y prf = inl refl

-- Structural Equality, Assumes X == X for all X
equalityOfTerms : ∀ {X : Set} (M N : Λ X) → dec X → Bool
equalityOfTerms (var x) (var y) d with d x y
...                                 | inr notEq = False
...                                 | inl eq = True
equalityOfTerms (app M M₁) (app N N₁) d = equalityOfTerms M N d ∧ equalityOfTerms M₁ N₁ d
equalityOfTerms (abs M) (abs N) d = equalityOfTerms M N (dec↑ d)
equalityOfTerms M N d = False

-- -- If two terms are ≡, then they should be literallyEqual too...
equalTermsEqualLengths : ∀ {X : Set} (M N : Λ X) → (D : dec X) → M ≡ N → equalityOfTerms M N D ≡ False → ⊥
equalTermsEqualLengths (var x) .(var x) d refl p2 with d x x
...  | inr notEq = notEq refl
equalTermsEqualLengths (var x) .(var x) d refl () | inl refl
equalTermsEqualLengths (app M M₁) .(app M M₁) d refl p2 = case c1 c2 (∧-elim (equalityOfTerms M M d) (equalityOfTerms M₁ M₁ d) p2) where
  c1 = λ x → equalTermsEqualLengths M M d refl x
  c2 = λ x → equalTermsEqualLengths M₁ M₁ d refl x
equalTermsEqualLengths (abs M) .(abs M) d refl p2 = equalTermsEqualLengths M M (dec↑ d) refl p2

equalLength : ∀ {X : Set} (M N : Λ X) → M ≡ N → ¬ (lenTerm M ≡ lenTerm N) → ⊥
equalLength M .M refl p = p refl

nottrue : ∀ {X} (A1 A2 : Λ (↑ (↑ X))) (B : Λ X) → A1 ≡ var o → bind (λ x → Λ↑ (↑→ (io var B) x)) A1 ≡ abs (app A1 A2) → ⊥
nottrue .(var o) A2 B refl p2 = exfalso (equalLength _ _ p2 (λ ()))

-- bind f M = bind g M, but the result is equal if applied to O, otherwise not?
-- bind-lemma : ∀ {X Y : Set} (f g : ↑ X → Λ Y) (M : Λ (↑ X)) → (∀ x → (x ≡ o) × (f o ≡ g o) ⊔ (x ∈ M → f x ≡ g x)) → bind f M ≡ bind g M
-- bind-lemma f g (var x) p =
--    let c1 = λ {(refl , rhs) → rhs}
--        c2 = λ z → z here
--     in case c1 c2 (p x)
-- bind-lemma f g (app M M₁) p = app≡ (bind-lemma _ _ M (λ q → case _ _ (p q))) (((bind-lemma _ _ M₁ (λ q → case _ _ (p q)))))
-- bind-lemma f g (abs M) p = abs≡ (bind-lemma _ _ M λ {o → inl (refl , refl) ; (i k) → inr λ q → case (λ {(refl , rhs) → ext (Λ→ i) rhs}) (λ u → ext (Λ→ i) (u (down q))) (p k)})

bind-lemma2 : ∀ {X Y : Set} (f g : ↑ X → Λ Y) (M : Λ (↑ X)) → ¬ (o ∈ M) → (∀ x → x ∈ M → f x ≡ g x) → bind f M ≡ bind g M
bind-lemma2 f g M _ h = bind-occurs f g M h
-- bind-lemma2 f g (var (i x)) neg p = p (i x) here
-- bind-lemma2 f g (var o) neg p = exfalso (neg here)
-- bind-lemma2 f g (app M M₁) neg p = {!   !}
-- bind-lemma2 f g (abs M) neg p = abs≡ (bind-lemma2 {!   !} {!   !} {!   !} {! neg  !} {!p   !})

-- liftingDoesNothing : ∀ {X Y} (f : X → Λ Y) (B : Λ X) (A : Λ (↑ X)) → ¬ (o ∈ A) → lenTerm (bind f ∘ (io var B) A) ≡ lenTerm A
-- liftingDoesNothing B (var (i x)) neg = refl
-- liftingDoesNothing B (var o) neg = exfalso (neg here)
-- liftingDoesNothing B (app A A₁) neg = ext S (tran++ (liftingDoesNothing B A _) (liftingDoesNothing B A₁ _))
-- liftingDoesNothing B (abs A) neg = ext S ( {!   !})


-- lercherEq2' : ∀ {X} (A1 A2 : Λ (↑ X)) (f : ↑ X → Λ X) → bind f A1 ≡ abs (app A1 A2) → A1 ≡ var o
-- lercherEq2' (var (i x)) A2 f p = {!   !}
-- lercherEq2' (var o) A2 f p = refl
-- -- lercherEq2' (var x) A2 f p with f x | p
-- -- ...                             | abs (app (var x) A1) | refl = {! x  !}
-- lercherEq2' (abs (var x)) A2 f p = {!   !}
-- lercherEq2' (abs (app A1 A3)) A2 f p =
--   let (lhs , rhs) = app≡inv (abs≡inv p)
--       e = λ {(o) → refl ; (i x) → refl }
--       q = bind-ext e A1 ! lhs
--       recCall = lercherEq2' A1 A3 (io (Λ↑ ∘ i ∘ f) (var o) ) q
--     in {!   !}

-- occursLemma : ∀ {X} {Y} (f : X → Λ Y) (A : Λ X) (x : X) → x ∈ A → bind f A ≡ f x → A ≡ var x

occursLemmaAbs' : ∀ {X} (A1 : Λ (↑ X)) (A2 : Λ (↑ (↑ X))) → A1 ≡ abs (app (Λ→ (↑→ i) A1) A2) → ⊥
-- occursLemmaAbs' : ∀ {X Y} (A1 : Λ (↑ X)) (A2 : Λ (↑ Y)) (f : ↑ X → Λ Y) → bind f A1 ≡ abs (app (Λ↑ ∘ ↑→ f) A1) A2) → ⊥
-- occursLemmaAbs' : ∀ {X Y} (A1 : Λ (↑ X)) (A2 : Λ (↑ Y)) (f : ↑ X → Λ Y) → bind f A1 ≡ abs (app (Λ→ ()) A1) A2) → ⊥
occursLemmaAbs' (abs (app A1 A3)) A2 p =
  let (lhs , rhs) = app≡inv (abs≡inv p)
   in equalLength _ _ lhs λ q → (numbersDontAdd2 _ _ _ (mapKeepsLength (↑→ (↑→ i)) A1) q)

-- lercherEq2lemma : ∀ {X} {x} (A1 : Λ (↑ X)) A2 (f : ↑ X → Λ (↑ X))→ x ∈ A1 → bind f A1  ≡ abs (app (Λ→ (↑→ i) A1) A2) → A1 ≡ var x
-- lercherEq2lemma .(var _) A2 f here p = refl
-- lercherEq2lemma .(abs (var (i _))) A2 f (down here) p = {!   !}
-- lercherEq2lemma .(abs (app _ t)) A2 f (down (left occ t)) p = {!   !}
-- lercherEq2lemma .(abs (app s _)) A2 f (down (right s occ)) p = {!   !}

-- absOccursLemma :  ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X) → dec X → A1 [ B ] ≡ abs (app A1 A2) → o ∈ A1 → A1 ≡ var o
-- absOccursLemma .(var o) A2 B d p here = refl
-- absOccursLemma .(abs _) A2 B d p (down occ) with abs≡inv p
-- ...                                            | q = {!   !}

-- absOccursLemma :  ∀ {X} (A1 A2 : Λ (↑ X)) (f : ↑ X → Λ X) (x : ↑ X) → dec X → bind f A1 ≡ abs (app A1 A2) → x ∈ A1  → A1 ≡ var x ⊔ A1 ≡ abs (var (i x))
-- -- absOccursLemma .(var x) A2 f x d p here = inl refl
-- -- absOccursLemma (abs (var .(i x))) A2 f x d p (down here) = inr refl
-- -- absOccursLemma (abs (app r₁ r₂)) A2 f (i x) d p (down occ) = {!   !}
-- -- absOccursLemma (abs (app r₁ r₂)) A2 f o d p (down occ) = {!   !}
-- absOccursLemma .(var x) A2 f x d p here = inl refl
-- absOccursLemma (abs (var .(i x))) A2 f x d p (down here) = inr refl
-- absOccursLemma (abs (app r₁ r₂)) A2 f x d p (down (left occ r₂)) with app≡inv (abs≡inv p)
-- ...    | (p1 , p2) with absOccursLemma r₁ r₂ _ (i x) (dec↑ d) p1 occ
-- ... | inl lft = {!   !}
-- ... | inr rgt = {!   !}
-- absOccursLemma (abs (app r₁ r₂)) A2 f x d p (down (right r₁ occ)) = {!   !}

-- with decΛ (dec↑ (dec↑ d) (i x)) r₁
-- ... | inl yes with app≡inv (abs≡inv p)
-- ...    | p2  = {!   !}
-- absOccursLemma (abs (app r₁ r₂)) A2 f x d p (down (left occ .r₂)) | inr no = exfalso (no occ)
-- absOccursLemma (abs (app r₁ r₂)) A2 f x d p (down (right .r₁ occ)) | inr no = {!   !}

-- ... | inl yes = ?
-- ... ∣ inr no  = ?
-- absOccursLemma (abs (app r₁ r₂)) A2 f x d p (down occ) with app≡inv (abs≡inv p)
-- absOccursLemma (abs (app r₁ r₂)) A2 f x d p (down (left occ .r₂)) | lhs , rhs with absOccursLemma r₁ r₂ _ (i x) (dec↑ d) lhs occ
-- -- ... | q = {! bind (λ x₁ → io (Λ→ i) (var o) (↑→ f x₁)) (var (i x ))  !}
-- ... | q = {! bind (λ x₁ → io (Λ→ i) (var o) (↑→ f x₁)) (abs (var (i (i x ))))  !}
-- absOccursLemma (abs (app r₁ r₂)) A2 f x d p (down (right .r₁ occ)) | lhs , rhs = {!   !}
-- absOccursLemma (abs (app r₁ r₂)) A2 f (i x) d p (down (left occ .r₂)) | lhs , rhs | inl r1var = {!   !}
-- absOccursLemma (abs (app r₁ r₂)) A2 f o d p (down (left occ .r₂)) | lhs , rhs | inl r1var = {!   !}
-- ... | inr r1abs with abs≡inv (ext (bind (λ x₁ → io (Λ→ i) (var o) (↑→ f x₁))) (~ r1abs) ! lhs )
-- absOccursLemma (abs (app r₁ r₂)) A2 f (i x) d p (down (left occ .r₂)) | lhs , rhs | inr r1abs | q = {!   !}
-- absOccursLemma (abs (app r₁ r₂)) A2 f o d p (down (left occ .r₂)) | lhs , rhs | inr r1abs | q = {!   !}
-- absOccursLemma (abs (app r₁ r₂)) A2 f x d p (down (right .r₁ occ)) | lhs , rhs = {!   !}

bindLemma1 : ∀ {X} (t : Λ X) (f : X → Λ X) → (∀ (x : X) → x ∈ t → f x ≡ var x) → bind f t ≡ t
bindLemma1 (var x) f h = h x here
bindLemma1 (app t t₁) f h = app≡ (bindLemma1 t f λ x oc → h x (left oc t₁ ) ) (bindLemma1 t₁ f λ x oc → h x (right t oc) )
bindLemma1 (abs t) f h = abs≡ (bindLemma1 t (Λ↑ ∘ ↑→ f) λ { o → λ y → refl ; (i x) → λ y → ext (Λ→ i) (h x (down y)) } )

mapKeepTermLength : ∀ {X Y : Set} (M : Λ X) {N : Nat} (f : X → Y) → lenTerm M ≡ N → lenTerm (Λ→ f M) ≡ N
mapKeepTermLength (var x) f p = p
mapKeepTermLength (app M M₁) f refl = ext S (tran++ (~ (mapKeepsLength f M)) (~ (mapKeepsLength f M₁)))
mapKeepTermLength (abs M) f refl = ext S (~ (mapKeepsLength _ _)) 

lercherEq2No : ∀ {X} (A1 : Λ (↑ (↑ X))) (B : Λ X) (f : ↑ (↑ X) → Λ (↑ X)) (x : ↑ (↑ X)) → dec X → ¬ (x ∈ A1) → (∀ z → z ∈ A1 → z ≡ x ⊔ lenTerm (f z) ≡ O)  → lenTerm (bind f A1) ≡ lenTerm A1
lercherEq2No (var y) B f x d nocc p = case (λ {refl → exfalso (nocc here)}) id (p y here)
lercherEq2No (app A1 A2) B f x d nocc p = 
   let r1 = lercherEq2No A1 B f x d (λ z → nocc (left z A2)) λ z z₁ → p z (left z₁ A2)
       r2 = lercherEq2No A2 B f x d (λ x₁ → nocc (right A1 x₁)) λ z z₁ → p z (right A1 z₁)
    in ext S (tran++ r1 r2)
lercherEq2No (abs A1) B f x d nocc p = ext S (lercherEq2No A1 (f x) _ (i x) (dec↑ d) (λ q → nocc (down q)) λ {o → _; (i o) → λ q → case (λ {refl → inl refl}) (λ q → inr (mapKeepTermLength (f o) i q)) (p o (down q)); (i (i o)) → λ q → case (λ {refl → inl refl}) (λ q → inr (mapKeepTermLength (f (i o)) i q)) (p (i o) (down q)) ; (i (i (i x))) → λ q → case (λ {refl → inl refl}) (λ q → inr (mapKeepTermLength (f (i (i x))) i q)) (p (i (i x)) (down q))})

lercherEq2 : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X) → dec X → A1 [ B ] ≡ abs (app A1 A2) → A1 ≡ var o
-- lercherEq2 A1 A2 B d p -- = lercherEq2' _ _ (io var B) p
lercherEq2 (var o) A2 B d p = refl
lercherEq2 (abs (var (i o))) A2 (app (abs (var (i x))) B₁) d p = exfalso (equalTermsEqualLengths _ _ (dec↑ d) (_×_.fst (app≡inv (abs≡inv p))) refl)
lercherEq2 (abs (var (i o))) A2 (app (abs (var o)) B₁) d p = exfalso (equalTermsEqualLengths _ _ (dec↑ d) (_×_.fst (app≡inv (abs≡inv p))) refl)
-- lercherEq2 (abs (app A1 A3)) A2 B d p with decΛ (decAti o decAto) A1
-- ... | inl here =
--   let (lhs , rhs) = app≡inv (abs≡inv p)
--    in {!   !}
-- ... | inl (down yes) = {!   !}
-- ...                                         | inr no  = {!   !}
lercherEq2 {X} (abs (app A1 A3)) A2 B d p =
  let (lhs , rhs) = app≡inv (abs≡inv p)
      f : ↑ (↑ X) → Λ (↑ X)
      f = (Λ↑ ∘ ↑→ (io var B))
      g : ↑ (↑ X) → Λ (↑ X)
      g = λ {(o) → var o ; (i o) → Λ→ i B ; (i (i x)) → var (i x) }
      f≃g : f ≃ g
      f≃g = λ {(o) → refl ; (i (i x)) → refl ; (i o) → refl }
      aux : i o ∈ A1 ⊔ ¬ (i o ∈ A1) → ⊥
      aux = (λ { (inl yes) → {!  down yes !} ;
                  (inr no) → let 
                  c1 = lercherEq2No A1 B f (i o) d no ((λ { o → λ _ → inr refl ; (i o) → λ _ → inl refl ; (i (i x)) → λ _ → inr refl }))
                  c2 = ext lenTerm lhs
                  in numbersDontAdd2 _ _ _ refl ((~ c1) ! c2) })
      -- r = {! occurs  !}
      -- e = bind-ext  (λ {(o) → {!   !} ; (i x) → {!   !} }) A1
      -- recCall = lercherEq2 A1 A3 (io (Λ↑ ∘ i) (Λ→ i B) o ) (dec↑ d) (e  ! lhs)
  in exfalso (aux (decΛ (decAti o (decAto)) A1))

--   with decΛ decAto A1
-- -- If o not in A, then A [ B ] = A contraction on length.
-- -- Although, how do you formulate this as a lemma?
-- ...      | inr no =  exfalso (equalLength _ _ (_×_.fst (app≡inv (abs≡inv p))) {!   !} )
-- ...      | inl yes with occursLemma' (λ x → io (Λ→ i) (var o) (↑→ (io var B) x)) A1 o yes
-- ...             | inr nonvarcase = exfalso (nonvarcase (occursLemma {!   !}
--                     (bind (λ z → io (Λ→ i) (var o) (↑→ (io var B) z)) A1) o {!   !}
--                       (symm (bind-law (λ z → io (Λ→ i) (var o) (↑→ (io var B) z)) {!   !} ) A1 ! {!   !} )) ) -- exfalso (nonvarcase (occursLemmaLen {!   !} _ o {!   !} {!   !})) -- Whats Going on Here?
-- ...             | inl refl = exfalso (equalLength _ _ (_×_.fst (app≡inv (abs≡inv p))) (λ ())) -- Contradiction on length
-- --    → bind (bind g ∘ f) ≃ (bind g ∘ bind f)

-- occursLemmaAbs' : ∀ {X} (A1 : Λ (↑ X)) (A2 : Λ (↑ (↑ X))) → A1 ≡ abs (app (Λ→ (↑→ i) A1) A2) → ⊥
-- -- occursLemmaAbs' : ∀ {X Y} (A1 : Λ (↑ X)) (A2 : Λ (↑ Y)) (f : ↑ X → Λ Y) → bind f A1 ≡ abs (app (Λ↑ ∘ ↑→ f) A1) A2) → ⊥
-- -- occursLemmaAbs' : ∀ {X Y} (A1 : Λ (↑ X)) (A2 : Λ (↑ Y)) (f : ↑ X → Λ Y) → bind f A1 ≡ abs (app (Λ→ ()) A1) A2) → ⊥
-- occursLemmaAbs' (abs (app A1 A3)) A2 p =
--   let (lhs , rhs) = app≡inv (abs≡inv p)
--    in equalLength _ _ lhs λ q → (numbersDontAdd2 _ _ _ (mapKeepsLength (↑→ (↑→ i)) A1) q)

implications : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X) (f : (↑ X) → Λ X) → dec X → bind f A1 ≡ abs (app A1 A2) → A1 ≡ abs (app (Λ→ (↑→ i) A1) (Λ→ i A2))
implications (var x) A2 B f d p1 with f x
...                             | var y = exfalso (equalLength _ _ p1 (λ ()))
...                             | app M N  = exfalso (equalTermsEqualLengths _ _ d p1 refl)
...                             | abs M = exfalso {!   !}
implications (abs (var (i x))) A2 B f d p1 with f x
...                             | var y = exfalso (equalLength _ _ p1 (λ ()))
...                             | app M N  = {!   !}
...                             | abs M = exfalso (equalTermsEqualLengths _ _ (dec↑ d) (abs≡inv p1) refl)
implications (abs (app A1 A3)) A2 B f d p1 =
  let (lhs , rhs) = app≡inv (abs≡inv p1)
      r1 = implications A1 A3 ((Λ→ i B)) _ (dec↑ d) lhs
  in exfalso (equalLength _ _ r1 (λ q → numbersDontAdd2 _ _ _ (mapKeepsLength _ A1) q))

lercherEq2⊥ : ∀ (A1 A2 : Λ (↑ ⊥)) (B : Λ ⊥) → A1 [ B ] ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2⊥ A1 A2 B p1 = exfalso (occursLemmaAbs' A1 (Λ→ i A2) (implications A1 A2 B (io var B) dec⊥ p1))

lercherHelper : ∀ (P1 P2 : Λ (↑ ⊥)) (Q : Λ ⊥) → P1 ≡ var o → P2 ≡ var o ⊔ P2 ≡ Λ→ i Q → (app P1 P2) [ Q ] ≡ app (abs (app P1 P2)) Q → abs (app P1 P2) ≡ ω × Q ≡ ω
lercherHelper .(var o) .(var o) Q refl (inl refl) p3 = refl , _×_.fst (app≡inv p3)
lercherHelper .(var o) .(Λ→ i Q) Q refl (inr refl) p3 =
  let qPrf = _×_.fst (app≡inv p3)
  in exfalso (equalLength _ _ qPrf (λ q → numbersDontAdd (mapKeepsLength i Q) q))

lercher : ∀ (P : Λ (↑ ⊥)) (Q : Λ ⊥) → P [ Q ] ≡ app (abs P) Q → abs P ≡ ω × Q ≡ ω
lercher (var (i x)) q prf = exfalso x
lercher (var o) q prf = exfalso (<-irrefl lt (<-eq (<<S lt) (ext (lenTerm) (~ prf)))) where lt = lenTerm q
lercher (app P1 P2) Q prf =
   let (lhs , rhs) = app≡inv prf
       l1 = lercherEq2 _ _ _ dec⊥ lhs
       l2 = lercherEq3 Q P2 rhs
   in lercherHelper _ _ _ l1 l2 prf


-- module CycleStuff where


--   data pre2cycle {X : Set} : Λ X → Set where
--     red2 : ∀ (P : Λ (↑ X)) (Q : Λ X) → (P [ Q ] ⟶ app (abs P) Q) → pre2cycle (app (abs P) Q)

--   -- data CycleEnum : Set where
--   --   case1 :

--   Qterm : ∀ {X} → Λ X
--   Qterm = Λ→ ex_falso (abs (abs (app (app (var o) (var (i o))) (var o))))

--   -- Qcyc : ∀ {X} → ∀ (P : Λ X) → pre2cycle (app (abs (app (app (var o) (Λ→ i P)) (var o))) (Qterm {X}))
--   -- Qcyc P = red2 (app (app (var o) (Λ→ i P)) (var o)) Qterm (appL→
--   --     (⟶≡ (redex (abs (app (app (var o) (var (i o))) (var o)))
--   --           (bind (io var (abs (abs (app (app (var o) (var (i o))) (var o)))))  (Λ→ i P)) )
--   --         {! bind-ext ? ? (abs (app (app (var o) (var (i o))) (var o)))  !} ) )

--             -- bind-ext : ∀ {X Y : Set} {f g : X → Λ Y} → f ≃ g → bind f ≃ bind g
  