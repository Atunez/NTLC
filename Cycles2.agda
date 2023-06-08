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



-- lercherEq2No : ∀ {X} (A1 : Λ (↑ (↑ X))) (B : Λ X) (f : ↑ (↑ X) → Λ (↑ X)) (x : ↑ (↑ X)) → dec X → ¬ (x ∈ A1) → (∀ z → z ∈ A1 → z ≡ x ⊔ lenTerm (f z) ≡ O)  → lenTerm (bind f A1) ≡ lenTerm A1
-- lercherEq2No (var y) B f x d nocc p = case (λ {refl → exfalso (nocc here)}) id (p y here)
-- lercherEq2No (app A1 A2) B f x d nocc p =
--    let r1 = lercherEq2No A1 B f x d (λ z → nocc (left z A2)) λ z z₁ → p z (left z₁ A2)
--        r2 = lercherEq2No A2 B f x d (λ x₁ → nocc (right A1 x₁)) λ z z₁ → p z (right A1 z₁)
--     in ext S (tran++ r1 r2)
-- lercherEq2No (abs A1) B f x d nocc p = ext S (lercherEq2No A1 (f x) _ (i x) (dec↑ d) (λ q → nocc (down q)) λ {o → _; (i o) → λ q → case (λ {refl → inl refl}) (λ q → inr (mapKeepTermLength (f o) i q)) (p o (down q)); (i (i o)) → λ q → case (λ {refl → inl refl}) (λ q → inr (mapKeepTermLength (f (i o)) i q)) (p (i o) (down q)) ; (i (i (i x))) → λ q → case (λ {refl → inl refl}) (λ q → inr (mapKeepTermLength (f (i (i x))) i q)) (p (i (i x)) (down q))})

-- case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
-- case x of f = f x

-- lercherEq2Yes : ∀ {X : Set} (A1 A3 : Λ (↑ (↑ X))) (B : Λ X) (f : ↑ (↑ X) → Λ (↑ X)) (x : ↑ (↑ X)) → (d : dec X) → x ∈ A1 → (∀ z → z ∈ A1 → z ≡ x × (f z) ≡ (Λ→ i B) ⊔ ¬ (z ≡ x) × Λ→ i (f z) ≡ var z) →  equalityOfTerms (bind f A1) (abs (app A1 A3)) (dec↑ d) ≡ True → ⊥
-- lercherEq2Yes (var (i (i x))) A3 B f .(i (i x)) d here fn p with f (i (i x))
-- ... | abs (app M N) = case {!   !} {!   !} (fn (i (i x)) here)
-- lercherEq2Yes (var (i o)) A3 B f .(i o) d here fn p = {!   !}
-- lercherEq2Yes (var o) A3 B f .o d here fn p = {!   !}
-- -- with f x
-- -- ... | abs (app M M₁) = case (λ {(lhs , rhs) → {!   !}}) (λ {(lhs , rhs) → lhs refl}) (fn x here)
-- lercherEq2Yes (abs r) A3 B f x d (down occ) fn p = {!   !}


-- --- NEED TO REWORD THESE LEMMAS.
-- ≡fromEquality : ∀ {X : Set} (M N : Λ X) (d : dec X) → equalityOfTerms M N d ≡ True → M ≡ N
-- ≡fromEquality (var x) (var y) d p = case {!   !} {!   !} (d x y)
-- ≡fromEquality (app M M₁) (app N N₁) d p = app≡ {!   !} {!   !}
-- ≡fromEquality (abs M) (abs N) d p = abs≡ (≡fromEquality M N (dec↑ d) p)

-- -- Given two terms, that are equal, then if there is a term in M but not N, then an issue happened...
-- oNotIn : ∀ {X : Set} (M : Λ X) (N : Λ (↑ X)) → Λ→ i M ≡ N → o ∈ N → ⊥
-- oNotIn M N p occ = {!   !}

-- ioLemma : ∀ {X : Set} (A1 : Λ (↑ (↑ (↑ X)))) (A3 : Λ (↑ (↑ X))) (B : Λ X) (f : ↑ (↑ X) → Λ (↑ X)) x → (d : dec X) → f x ≡ Λ→ i B → (i x) ∈ A1 → equalityOfTerms (bind (Λ↑ ∘ ↑→ f) A1) (app (abs A1) A3) (dec↑ (dec↑ d)) ≡ True → ⊥ 
-- ioLemma (var x₁) A3 B f x d p occ eq = {!   !}
-- ioLemma (app A1 A2) A3 B f x d p occ eq = {! down occ  !}

-- lercherEq2Yesio : ∀ {X : Set} (A1 A3 : Λ (↑ (↑ X))) (B : Λ X) (f : ↑ (↑ X) → Λ (↑ X)) x → (d : dec X) → x ∈ A1 → (∀ z → z ∈ A1 → z ≡ x × (f z) ≡ (Λ→ i B) ⊔ ¬ (z ≡ x)) →  equalityOfTerms (bind f A1) (abs (app A1 A3)) (dec↑ d) ≡ True → ⊥
-- lercherEq2Yesio {X} (var x₁) A3 B f .x₁ d here h p = {!   !}
-- lercherEq2Yesio {X} (abs A1) A3 B f x d (down occ) h p = case (λ {(refl , rhs) → {!   !}}) (λ z → z refl) (h x (down occ))
-- {-
-- lercherEq2Yesio (var (i o)) A3 B f x d here fn p =
--  let FB = ≡fromEquality (f (i o)) _ (dec↑ d) p
--      c1 = λ {(lhs , rhs) → oNotIn _ _ ((~ rhs) ! FB) (down (left here A3))}
--  in case c1 (λ z → _×_.fst z refl) (fn (i o) here)
-- -- Incorrect Generalization?
-- lercherEq2Yesio (abs r) A3 B f x d (down occ) fn p =
--  let FB = ≡fromEquality (bind (Λ↑ ∘ ↑→ f) r) (app (abs r) A3) (dec↑ (dec↑ d)) p
--  in ?
--  -- in case (λ {(lhs , rhs) → {!   !}}) (λ z → _×_.fst z ?) (fn (i o) (down occ))
-- -}

-- breakBool : ∀ (b : Bool) → b ≡ True ⊔ b ≡ False
-- breakBool True = inl refl
-- breakBool False = inr refl

-- notEqEquals : ∀ {X} (M N : Λ X) (d : dec X) → M ≡ N → equalityOfTerms M N d ≡ False → ⊥
-- notEqEquals (var x) .(var x) d refl p2 with d x x
-- ... | inr x₁ = x₁ refl
-- notEqEquals (app M M₁) .(app M M₁) d refl p2 = case (λ q → notEqEquals M M d refl q) (λ q → notEqEquals M₁ M₁ d refl q) (∧-elim (equalityOfTerms M M d) (equalityOfTerms M₁ M₁ d) p2)
-- notEqEquals (abs M) .(abs M) d refl p2 = notEqEquals M M (dec↑ d) refl p2

-- lercherEq2lemma :  ∀ {X} (A1 A2 : Λ (↑ X)) (f : ↑ X → Λ X) (x : ↑ X) → x ∈ A1 → dec X → bind f A1 ≡ abs (app A1 A2) → A1 ≡ var o
-- lercherEq2lemma {X} (var (i x)) A2 f .(i x) here d eq = {!   !}
-- lercherEq2lemma {X} (var o) A2 f .o here d eq = refl
-- lercherEq2lemma {X} (abs A1) A2 f x occ d eq = {!   !}


data §Λ (X : Set) : Set where
  varS : X → §Λ X
  absS : §Λ (↑ X) → §Λ X

Λto§Λ : ∀ {X : Set} (M : Λ X) → §Λ X
Λto§Λ (var x) = varS x
Λto§Λ (app M M₁) = Λto§Λ M
Λto§Λ (abs M) = absS (Λto§Λ M)

§ΛtoΛ : ∀ {X : Set} (M : §Λ X) → Λ X
§ΛtoΛ (varS x) = var x
§ΛtoΛ (absS M) = abs (§ΛtoΛ M)

-- Spine of a term is the number of abstractions on the left
lenSTerm : ∀ {X : Set} (M : §Λ X) → Nat
lenSTerm (varS x) = O
lenSTerm (absS M) = S (lenSTerm M)

Λ≡to§Λ≡ : ∀ {X : Set} (M N : Λ X) → M ≡ N → Λto§Λ M ≡ Λto§Λ N
Λ≡to§Λ≡ M N refl = refl

lenSTerm§≡ : ∀ {X : Set} (M N : §Λ X) → M ≡ N → lenSTerm M ≡ lenSTerm N
lenSTerm§≡ M N refl = refl

-- -- Spine Path: the number of abstractions + first variable observed!
-- spinePathOfTerm : ∀ {X : Set} (M : Λ X) → Λ X
-- spinePathOfTerm (var x) = var x
-- spinePathOfTerm (app M M₁) = spinePathOfTerm M
-- spinePathOfTerm (abs M) = abs (spinePathOfTerm M)

-- -- Given two Terms, decide if they equal or not using their spines.
-- decSpinePath : ∀ {X : Set} (M N : Λ X) → dec X → (spinePathOfTerm M) ≡ (spinePathOfTerm N) ⊔ ¬ ((spinePathOfTerm M) ≡ (spinePathOfTerm N))
-- decSpinePath M N d = {!   !}

-- -- Lemma 1: If two terms have different spine lengths, they can't be equal
-- ≡spineLength : ∀ {X : Set} (M N : Λ X) → ¬ (spineLengthOfTerm M ≡ spineLengthOfTerm N) → M ≡ N → ⊥
-- ≡spineLength M _ neq refl = neq refl 

S→ : ∀ {X Y : Set} → (X → Y) → §Λ X → §Λ Y
S→ f (varS x)     = varS (f x)
S→ f (absS M)     = absS (S→ (↑→ f) M)

S↑ : ∀ {X : Set} → ↑ (§Λ X) → §Λ (↑ X)
S↑ = io (S→ i) (varS o)

bindS : ∀ {X Y : Set} → (X → §Λ Y) → §Λ X → §Λ Y
bindS f (varS x) = f x
bindS f (absS M) = absS (bindS (S↑ ∘ ↑→ f) M)

spineSub : ∀ {X} (M : §Λ (↑ X)) (N : §Λ X) → §Λ X
spineSub M N = bindS (io varS N) M

dec§Λ : ∀ {X} {x} → (decAt X x) → (t : §Λ X)  → x ∈ (§ΛtoΛ t) ⊔ ¬ (x ∈ (§ΛtoΛ t))
dec§Λ d (varS x) with d x
... | inl refl = inl here
... | inr y = inr λ {here → y refl}
dec§Λ {X} {x} d (absS t) with dec§Λ (decAti x d) t
... | inl y = inl (down y)
... | inr y = inr λ {(down occ) → y occ}

mapKeepsSLength : ∀ {X Y : Set} → (f : X → Y) → (M : §Λ X) → lenSTerm M ≡ lenSTerm (S→ f M)
mapKeepsSLength f (varS x) = refl
mapKeepsSLength f (absS M) = ext S (mapKeepsSLength (↑→ f) M)

absS≡ : ∀ {X : Set} {M N : §Λ (↑ X)} → M ≡ N → absS M ≡ absS N
absS≡ refl = refl 

absS≡inv : ∀ {X : Set} {M N : §Λ (↑ X)} → absS M ≡ absS N → M ≡ N
absS≡inv refl = refl


noSubWithNoDecide : ∀ {X : Set} (M : §Λ (↑ X)) (N : §Λ X) (f : ↑ X → §Λ X) (x : ↑ X) → ¬ (x ∈ §ΛtoΛ M) →  (∀ (z : ↑ X) → z ∈ (§ΛtoΛ M) → (z ≡ x × f x ≡ N) ⊔ lenSTerm (f z) ≡ O) → lenSTerm (bindS f M) ≡ lenSTerm M
noSubWithNoDecide (varS y) N f x nocc fn = case (λ {(refl , rhs) → exfalso (nocc here)}) id (fn y here)
noSubWithNoDecide (absS M) N f x nocc fn = ext S (noSubWithNoDecide M (S→ i N) _ (i x) (λ z → nocc (down z)) 
 λ {o → λ _ → inr refl; 
 (i o) → λ q → case (λ {(refl , rhs) → inl ((refl , exfalso (nocc (down q))))}) (λ q2 → inr ((~(mapKeepsSLength i (f o))) ! q2)) (fn o (down q)); 
 (i (i x)) → λ q → case (λ {(refl , rhs) → inl ((refl , exfalso (nocc (down q))))}) (λ q2 → inr ((~(mapKeepsSLength i (f (i x)))) ! q2)) (fn (i x) (down q))})  




isInj : ∀ {X Y : Set} → (X → Y) → Set
isInj f = ∀ {x1 x2} → f x1 ≡ f x2 → x1 ≡ x2

iInj : ∀ {X} → isInj (i {X})
iInj refl = refl

notoccursΛ→  : ∀ {X Y} (f : X → Y) (y : Y) → (∀ x → ¬ (f x ≡ y) ) → ∀ t → ¬ (y ∈ Λ→ f t)
notoccursΛ→ f .(f x) h (var x) here = h x refl
notoccursΛ→ f y h (app t1 t2) (left occ .(Λ→ f t2)) = notoccursΛ→ f y h t1 occ
notoccursΛ→ f y h (app t1 t2) (right .(Λ→ f t1) occ) = notoccursΛ→ f y h t2 occ
notoccursΛ→ f y h (abs t0) (down occ) = notoccursΛ→ (↑→ f) (i y) h' t0 occ
  where h' : ∀ x → ¬ (↑→ f x ≡ i y)
        h' o ()
        h' (i x) e = h x (iInj e)

o∉Λ→i : ∀ {X} (s : Λ X) → ¬ (o ∈ Λ→ i s)
o∉Λ→i s = notoccursΛ→ i o (λ x → λ {()} ) s


notoccursS→  : ∀ {X Y} (f : X → Y) (y : Y) → (∀ x → ¬ (f x ≡ y) ) → ∀ t → ¬ (y ∈ §ΛtoΛ (S→ f t))
notoccursS→ f .(f x) h (varS x) here = h x refl
notoccursS→ f y h (absS t) (down occ) = notoccursS→ (↑→ f) (i y) h' t occ
  where h' : ∀ x → ¬ (↑→ f x ≡ i y)
        h' o ()
        h' (i x) e = h x (iInj e)

o∉S→i : ∀ {X} (s : §Λ X) → ¬ (o ∈ §ΛtoΛ (S→ i s))
o∉S→i s = notoccursS→ i o (λ x → λ {()} ) s

-- Unsure how to make this better
-- Show that weakening can't give an O
weakingHasNoO : ∀ {X : Set} (M : §Λ X) (N : §Λ (↑ X)) → o ∈ (§ΛtoΛ N) → S→ i M ≡ N → ⊥
weakingHasNoO M .(S→ i M) occ refl = (o∉S→i M) occ

bindS-ext : ∀ {X Y : Set} (M : §Λ X) (f g : X → §Λ Y) → f ≃ g → bindS f M ≡ bindS g M
bindS-ext (varS x) f g p = p x
bindS-ext (absS M) f g p = absS≡ (bindS-ext M _ _ λ {o → refl; (i x) → ext (S→ i) (p x)})

-- -- extract variable from §Λ
-- extract : ∀ {X : Set} (M : §Λ X) → §Λ (↑ X)
-- extract (varS x) = varS (i x)
-- extract (absS M) = extract M

-- NOT TRUE STATEMENT
-- -- Formulate using bind...
-- -- No need? M can only contain one variable. In the case of a variable, is bound to be (i o).
-- shuffleSubAndAbs : ∀ {X : Set} (M : §Λ (↑ (↑ (↑ X)))) (N : §Λ X) → (i o) ∈ (§ΛtoΛ M) → spineSub (absS (absS M)) N ≡ absS (spineSub (absS M) (S→ i N))  
-- shuffleSubAndAbs M N occ = absS≡ (absS≡ (bindS-ext M _ _ (λ {o → refl; (i (i (i x))) → refl; (i (i x)) → {!   !}
--                                                                                            ; (i o) → {!   !}})))


ioInSpinePath : ∀ {X : Set} (M : §Λ (↑ (↑ X))) (N : §Λ X) (x : ↑ (↑ X)) → x ∈ (§ΛtoΛ M) → (spineSub (absS M) N) ≡ absS (absS M) → ⊥
ioInSpinePath (varS (i o)) N .(i o) here p = weakingHasNoO _ _ (down here) (absS≡inv p)
ioInSpinePath (absS M) (varS x₁) x (down occ) p = {!   !} -- p implies that LHS < RHS 
ioInSpinePath (absS M) (absS (varS y)) x (down occ) p = {!   !} -- How to get the contradiction?
ioInSpinePath (absS M) (absS (absS N)) x (down occ) p = {!   !} -- p implies that LHS > RHS

-- ioInSpinePath (absS M) N (i (i x)) (down occ) p = ioInSpinePath M (S→ i N) (i (i (i x))) occ {!  absS≡inv (absS≡inv p) !}
-- ioInSpinePath (absS M) N (i o) (down occ) p = 
--   let c = absS≡inv (absS≡inv p)
--       f = (λ x → S↑ (↑→ (λ x₁ → S↑ (↑→ (io varS N) x₁)) x))
--       g = λ {o → varS o; (i o) → varS (i o); (i (i o)) → S→ i (S→ i N); (i (i (i x))) → varS (i (i x))}
--       f≃g : f ≃ g
--       f≃g = λ {o → refl; (i o) → refl; (i (i o)) → refl; (i (i (i x))) → refl}
--   in ioInSpinePath M (S→ i N) (i (i o)) occ {! absS≡inv (absS≡inv p)   !}
-- ioInSpinePath (absS M) N o (down occ) p = 
--   let c = absS≡inv (absS≡inv p)
--   in ioInSpinePath M (S→ i N) (i o) occ {! down occ  !}

addI : ∀ {X Y : Set} (M : Λ X) (N : §Λ X) → Λto§Λ M ≡ N → (f : X → Y) → Λto§Λ (Λ→ f M) ≡ S→ f N
addI (var x) .(varS x) refl f = refl
addI (app M M₁) .(Λto§Λ M) refl f = addI M (Λto§Λ M) refl f
addI (abs M) .(absS (Λto§Λ M)) refl f = absS≡ (addI M (Λto§Λ M) refl (↑→ f))

-- The Spine of M [ N ] is equal to the Spine of (spine M) [ (spine N) ]
-- Need a better formulation... Probably with Bind
bindAndBindS : ∀ {X : Set} (M : Λ (↑ X)) (N : Λ X) (f : ↑ X → Λ X) (g : ↑ X → §Λ X) → (∀ (z : ↑ X) → z ∈ M → Λto§Λ (f z) ≡ g z) → Λto§Λ (bind f M) ≡ bindS g (Λto§Λ M)
bindAndBindS (var x) N f g fn = fn x here
bindAndBindS (app M M₁) N f g fn = bindAndBindS M N f g (λ z z₁ → fn z (left z₁ M₁))
bindAndBindS (abs M) N f g fn = absS≡ (bindAndBindS M (Λ→ i N) _ _ λ {o → λ _ → refl; (i o) → λ q → addI (f o) (g o) (fn o (down q)) i; (i (i x)) → λ q → addI (f (i x)) (g (i x)) (fn (i x) (down q)) i})

subWithSpines : ∀ {X : Set} (M : Λ (↑ X)) (N : Λ X) → Λto§Λ (M [ N ]) ≡ spineSub (Λto§Λ M) (Λto§Λ N)
subWithSpines (var (i x)) N = refl
subWithSpines (var o) N = refl
subWithSpines (app M M₁) N = subWithSpines M N
subWithSpines (abs M) N = absS≡ (bindAndBindS M (Λ→ i N) _ _ λ {o → λ _ → refl; (i o) → λ q → addI N (Λto§Λ N) refl i; (i (i x)) → λ _ → refl})

lercherEq2Occ : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X) → dec X → A1 [ B ] ≡ abs (app A1 A2) → o ∈ A1 → A1 ≡ var o
lercherEq2Occ .(var o) A2 B d p here = refl
-- All (i o)s in R become weaking of B
-- RHS: abs (app (abs r) A2), the length of the "spine" is spine(r) + 2
-- LHS: abs (r [Λ→ i B]), the length of the spine is spine(r [Λ→ i B]) + 1
-- Once a var is reached, the spine calculation is done.
-- On the left path of R, if there is no (i o)s, then the spines can't be equal in length, because no substitution occurs
-- If B is var, then spine doesn't change
-- If B is app B1 B2, then the spine is spine(B1).
-- If B is abs B1, then spine is spine(B1) + 1.
-- Regardless, if there is something happening at the end of the spine path, then the original spine path must contain an (i o)/o at the end
-- However, Λ→ i B can't contain o. Thus, the spines can't be equal.
lercherEq2Occ (abs r) A2 B d p (down occ) = 
  let spinePathOfR = Λto§Λ r
      spineOfB = Λto§Λ B
      equalSpines = Λ≡to§Λ≡ _ _ p
      equalSpineLengths = lenSTerm§≡ _ _ equalSpines
      subbedSpines = subWithSpines (abs r) B
      lenOfSubbedSpines = lenSTerm§≡ _ _ subbedSpines
      -- if (i o) is in the path of R
      c1 = λ q → exfalso (ioInSpinePath spinePathOfR spineOfB (i o) q (~ subbedSpines ! equalSpines))
      -- if (i o) isn't in the path of R, then no substiution occurs.
      -- Namely, I am given that LHS ≡ RHS, need to show that no subs occurs on LHS, then done using lemma 
      c2 = λ q → 
           -- Show the fact that the spine of abs r [ B ] is the same as abs r. (OR their lengths?)
           -- Show that the lengths of abs r and abs (app (abs r) A2) isn't equal.
           let noSub = noSubWithNoDecide (absS spinePathOfR) spineOfB (io varS spineOfB) o (λ {(down q2) → q q2}) λ {o → λ _ → inl (refl , refl); (i x) → λ _ → inr refl}
               issueNumber = ~ noSub ! ~ lenOfSubbedSpines ! equalSpineLengths
           in exfalso (numbersDontAdd3 refl issueNumber)
  in case c1 c2 (decΛ (decAti o decAto) (§ΛtoΛ spinePathOfR))


bindOnNoVar : ∀ {X} (M : Λ (↑ X)) (N : Λ X) (f : ↑ X → Λ X) x → ¬ (x ∈ M) → (∀ (z : ↑ X) → z ∈ M → (z ≡ x × f x ≡ N) ⊔ lenTerm (f z) ≡ O) → lenTerm (bind f M) ≡ lenTerm M
bindOnNoVar (var x) N f y nocc fn = case ((λ { (refl , rhs) → exfalso (nocc here)})) id (fn x here)
bindOnNoVar (app M M₁) N f y nocc fn = ext S (tran++ (bindOnNoVar M N f y (λ z → nocc (left z M₁)) λ z z₁ → fn z (left z₁ M₁)) (bindOnNoVar M₁ N f y (λ z → nocc (right M z)) λ z z₁ → fn z (right M z₁)))
bindOnNoVar (abs M) N f y nocc fn = ext S (bindOnNoVar M (Λ→ i N) _ (i y) (λ q → nocc (down q)) 
      λ {o → λ q → inr refl; 
        (i o) → λ q → case (λ {(refl , rhs) → exfalso (nocc (down q))}) (λ q → inr (~(mapKeepsLength i (f o)) ! q)) (fn o (down q)); 
        (i (i x)) → λ q → case (λ {(refl , rhs) → exfalso (nocc (down q))}) (λ q → inr (~(mapKeepsLength i (f (i x))) ! q)) (fn (i x) (down q))})


lercherEq2' : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X) → dec X → A1 [ B ] ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2' A1 A2 B d p with decΛ decAto A1
... | inr no = 
       let noSub = bindOnNoVar A1 B (io var B) o no λ {o → λ _ → inl (refl , refl) ; (i x) → λ _ → inr refl}  
       in exfalso (equalLength (bind (io var B) A1) (abs (app A1 A2)) p λ q → numbersDontAdd2 (lenTerm A1) (lenTerm A1) (lenTerm A2) refl (~ noSub ! q))
... | inl yes = lercherEq2Occ A1 A2 B d p yes



lercherEq2 : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X) → dec X → A1 [ B ] ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2 A1 A2 B d p = lercherEq2' A1 A2 B d p
-- lercherEq2 (var o) A2 B d p = refl
-- lercherEq2 (abs (var (i o))) A2 (app (abs (var (i x))) B₁) d p = exfalso (equalTermsEqualLengths _ _ (dec↑ d) (_×_.fst (app≡inv (abs≡inv p))) refl)
-- lercherEq2 (abs (var (i o))) A2 (app (abs (var o)) B₁) d p = exfalso (equalTermsEqualLengths _ _ (dec↑ d) (_×_.fst (app≡inv (abs≡inv p))) refl)
-- -- lercherEq2 (abs (app A1 A3)) A2 B d p with decΛ (decAti o decAto) A1
-- -- ... | inl here =
-- --   let (lhs , rhs) = app≡inv (abs≡inv p)
-- --    in {!   !}
-- -- ... | inl (down yes) = {!   !}
-- -- ...                                         | inr no  = {!   !}
-- lercherEq2 {X} (abs (app A1 A3)) A2 B d p =
--   let (lhs , rhs) = app≡inv (abs≡inv p)
--       f : ↑ (↑ X) → Λ (↑ X)
--       f = (Λ↑ ∘ ↑→ (io var B))
--       g : ↑ (↑ X) → Λ (↑ X)
--       g = λ {(o) → var o ; (i o) → Λ→ i B ; (i (i x)) → var (i x) }
--       f≃g : f ≃ g
--       f≃g = λ {(o) → refl ; (i (i x)) → refl ; (i o) → refl }
--       aux : i o ∈ A1 ⊔ ¬ (i o ∈ A1) → ⊥
--       aux = (λ { (inl yes) → let
--                   c1 = λ q → {!   !} -- lercherEq2Yesio A1 A3 B _ d yes (λ {o → λ q → inr (((λ ()) , inl refl)) ; (i o) → λ _ → inl (refl , refl) ; (i (i x)) → λ _ → inr ((λ ()) , inr refl)}) q
--                   c2 = λ q → notEqEquals _ _ (dec↑ d) lhs q
--                   in case c1 c2 (breakBool (equalityOfTerms (bind f A1) (abs (app A1 A3)) (dec↑ d))) ;
--                   (inr no) → let
--                   c1 = lercherEq2No A1 B f (i o) d no ((λ { o → λ _ → inr refl ; (i o) → λ _ → inl refl ; (i (i x)) → λ _ → inr refl }))
--                   c2 = ext lenTerm lhs
--                   in numbersDontAdd2 _ _ _ refl ((~ c1) ! c2) })
--       -- r = {! occurs  !}
--       -- e = bind-ext  (λ {(o) → {!   !} ; (i x) → {!   !} }) A1
--       -- recCall = lercherEq2 A1 A3 (io (Λ↑ ∘ i) (Λ→ i B) o ) (dec↑ d) (e  ! lhs)
--   -- in exfalso (aux (decΛ (decAti o (decAto)) A1))
--   in {!   !}

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
            