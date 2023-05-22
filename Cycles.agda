module Cycles where

open import Lambda public

-- open import Agda.Builtin.Sigma

postulate
  em : ∀ (A : Set) → A ⊔ ¬ A

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
-- decΛ (var (i x)) = inr (λ {()})
-- decΛ (var o) = inl here
-- decioΛ (abs t₀) with decAti (i o)
-- ...                | (inl p) = {!   !}
-- ...                | (inr p) = {!   !}

-- decΛ : ∀ {X} → dec X → dec (Λ X)
-- decΛ {X} eq (var x) (var y) with eq x y
-- ...                            | inl q = inl (ext var q)
-- ...                            | inr q = inr f where f : var x ≡ var y → ⊥
--                                                      f refl = q refl
-- decΛ {X} eq (app s₁ s₂) (app t₁ t₂) = {!   !}
-- decΛ {X} eq (abs s₀) (abs t₀) = {!   !}
-- decΛ {X} eq s t  = inr {!   !}

occursLemma2 : ∀ {X : Set} (M : Λ (↑ X)) (N : Λ X) (x : X) → (i x) ∈ M → M ≡ var (i x) ⊔ lenTerm N < lenTerm (M [ N ])
occursLemma2 .(var (i x)) n x here = inl (refl)
occursLemma2 (app s t) N x (left prf t) = inr (case c1 c2 (occursLemma2 s N x prf)) where
  f = λ x → S (lenTerm (bind (io var N) x) ++ lenTerm (bind (io var N) t))
  c1 = λ q → <-eq {!   !} (ext f (~ q))
  c2 = λ q → tran< _ _ _ q (add>S _ _)
occursLemma2 (app s t) n x (right s prf) = inr (case c1 c2 (occursLemma2 t n x prf)) where
  c1 = {!   !}
  c2 = λ q → tran< _ _ _ q (add<S _ _)
occursLemma2 (abs r) n x (down prf) = inr (case c1 c2 (occursLemma2 r ((Λ→ i n)) (i x) prf)) where
  f = λ x → S ( lenTerm (bind (λ y → Λ↑ (↑→ (io var n) y)) x))
  c1 = λ q → <-eq ({!   !}) (ext f (~ q))
  c2 = {!   !}

mapKeepsLength : ∀ {X Y : Set} → (f : X → Y) → (M : Λ X) → lenTerm M ≡ lenTerm (Λ→ f M)
mapKeepsLength f (var x) = refl
mapKeepsLength f (app M₁ M₂) = ext S (tran++ (mapKeepsLength f M₁)  (mapKeepsLength f M₂) )
mapKeepsLength f (abs M₀) = ext S (mapKeepsLength (↑→ f) M₀ )

liftingKeepsLength : ∀ {X : Set} (M : Λ X) → lenTerm M ≡ lenTerm (Λ→ i M)
liftingKeepsLength N = mapKeepsLength i N

occursLemma1 : ∀ {X : Set} (M : Λ (↑ X)) (N : Λ X) → o ∈ M → M ≡ var o ⊔ lenTerm N < lenTerm (M [ N ])
occursLemma1 .(var o) N here = inl refl
occursLemma1 (app s t) N (left p t) = inr (case c1 c2 (occursLemma1 s N p) ) where
  f = λ x → S ( lenTerm (bind (io var N) x) ++ lenTerm (bind (io var N) t) )
  c1 = λ q → <-eq (add>S (lenTerm N) _) (ext f (~ q))
  c2 = λ q → tran< _ _ _ q (add>S _ _)
occursLemma1 (app s t) N (right s p) = inr (case c1 c2 (occursLemma1 t N p)) where
  f = λ x → S ( lenTerm (bind (io var N) s) ++ lenTerm (bind (io var N) x) )
  c1 = λ q → <-eq (add<S (lenTerm N) _) (ext f (~ q))
  c2 = λ q → tran< _ _ _ q (add<S _ _)
occursLemma1 (abs r) N (down p) = inr {!   !}
 --
 -- inr (case c1 c2 (occursLemma2 r (Λ→ i N) o p)) where
 --  f = λ x → S ( lenTerm (bind (λ y → Λ↑ (↑→ (io var N) y)) x))
 --  c1 = λ q → <-eq (<S-eq (<S _) (liftingKeepsLength N)) (ext f (~ q))
 --  c2 = λ q → {!   !} -- <-deq q (~ (liftingKeepsLength N)) {!   !}


occursDec : ∀ {X} → ∀ (x : X) (t : Λ X) → x ∈ t ⊔ ¬ (x ∈ t)
occursDec x t = {!   !}

ω : Λ ⊥
ω = abs (app (var o) (var o))

app≡inv : ∀ {X} (M M' N N' : Λ X) → app M N ≡ app M' N' → M ≡ M' × N ≡ N'
app≡inv M .M N .N refl = ( refl , refl )

abs≡inv : ∀ {X} (M M' : Λ (↑ X)) → abs M ≡ abs M' → M ≡ M'
abs≡inv M M' = eqAbs

bind-occurs : ∀ {X Y : Set} (f g : X → Λ Y) (t : Λ X)
                → (∀ x → x ∈ t → f x ≡ g x) → bind f t ≡ bind g t
bind-occurs = {!   !}

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
      e3 : ∀ C → C ≡ bind var C
      e3 = {!   !}
   in (e3 A) !  (e2 ! (e1 A ! ext (Λ→ i) h  ) )

-- occurs-map : ∀ {X} (A : Λ (↑ X)) (B C : Λ X) → A [ B ] ≡ C → ¬ (o ∈ A) → A ≡ Λ→ i C
-- occurs-map A B C h nocc = {!   !}
--

-- occurs-map (var (i x)) B C e nocc = ext (Λ→ i) e
-- occurs-map (var o) B C e nocc = exfalso (nocc here)
-- occurs-map (app A₁ A₂) B (app C₁ C₂) e nocc =
--   let (p1 , p2) = app≡inv _ _ _ _ e
--    in app≡ (occurs-map A₁ B C₁ p1 λ q → nocc (left q A₂ ) )
--            ((occurs-map A₂ B C₂ p2 λ q → nocc (right A₁ q ) ))
-- occurs-map (abs A) B (abs C) e nocc =
--   let p = abs≡inv _ _ e
--    in abs≡ {!   !}
  -- occurs-map (A) {!   !} {!   !} refl (λ q → nocc (down {!   !}))
  --  in abs≡ {!   !}

occursLemmaLen : ∀ {X} {Y} (f : X → Λ Y) (A : Λ X) (x : X) → x ∈ A → lenTerm (bind f A) ≤ lenTerm (f x) → A ≡ var x
occursLemmaLen f .(var x) x here l = refl
occursLemmaLen f (app s t) x (left occ t) l =
  let x1 = occursLemmaLen f s x occ
      x2 = add>S (lenTerm (bind f s)) (lenTerm (bind f t))
      x3 = x1 (lelte x2 l)
      x4 = ≤-eq {l = lenTerm (bind f s)} l (ext lenTerm (~ ext (bind f) x3))
   in exfalso (lestrict x2 x4)
occursLemmaLen f .(app s _) x (right s occ) l = {!   !}
occursLemmaLen f (abs r) x (down occ) l =
  let x1 = occursLemmaLen (Λ↑ ∘ ↑→ f) r (i x) occ
      x2 = mapKeepsLength i (f x)
      x3 = lelte (<S _) (≤-eq l x2)
      x4 = x1 x3
      x5 = ≡≤ (ext S (x2 ! ext lenTerm (ext (bind (Λ↑ ∘ ↑→ f)) (~ x4)) ) ) l
   in exfalso (lestrict (<S (lenTerm (f x))) x5)


occursLemma : ∀ {X} {Y} (f : X → Λ Y) (A : Λ X) (x : X) → x ∈ A → bind f A ≡ f x → A ≡ var x
occursLemma f A x occ eq = occursLemmaLen f A x occ (≤≡ {!   !} )
-- occursLemma f (var x) x here eq = refl
-- -- occursLemma f (app s t) x (left occ t) eq rewrite ~ eq
-- -- ...                                             | p = ?
-- occursLemma f (app s t) x (left occ t) eq with f x | eq
-- ...                                          | app f1 f2 | refl = {!   !}
--   -- let p1 = occursLemma (λ x → ?) s x occ
--   --  in {!   !}
-- occursLemma f (app s t) x (right s occ) eq = {!   !}
-- occursLemma f (abs r) x (down occ) eq = {!   !}

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
-- occursLemma f .(var x) x here = inl refl
-- occursLemma f .(app _ t) x (left occ t) = inr {!   !}
-- occursLemma f .(app s _) x (right s occ) = {!   !}
-- occursLemma f .(abs _) x (down occ) = {!   !}

lercherEq3 : ∀ {X} (A : Λ X) (B : Λ (↑ X)) → B [ A ] ≡ A → B ≡ var o ⊔ B ≡ Λ→ i A
lercherEq3 A B e with decΛ decAto B
...                 | inr no  = inr (occurs-map B A e no )
...                 | inl yes with occursLemma' (io var A) B o yes
...                              | inl yesvar = inl yesvar
...                              | inr notvar = exfalso (notvar e)
-- ...                 | inl here        = inl refl
-- ...                 | inl (left p t)  = inr {!   !}
-- ...                 | inl (right t p) = {!   !}
-- ...                 | inl (down p)    = {!   !}

-- lercherEq3 A (var (i x)) p = inr (ext (Λ→ i) p)
-- lercherEq3 A (var o) p = inl refl
-- lercherEq3 (app A₁ A₂) (app B₁ B₂) p =
--   let (p1 , p2) = app≡inv _ _ _ _ p
--       -- (q1 , q2) = (lercherEq3 A₁ B₁ {!   !} , lercherEq3 A₂ B₂ ?)
--    in inr {!   !}
--   --  -- inr (app≡ {! p1  !} {! p2   !} ! ext (Λ→ i) p)
-- lercherEq3 A (abs B) p =
--   {!   !}


_∧_ : ∀ (X Y : Bool) → Bool
True ∧ Y = Y
False ∧ Y = False

IfThenElse : ∀ {X : Set} → (V : Bool) → (A B : X) → X
IfThenElse True a b = a
IfThenElse False a b = b

∧-elim : ∀ (X Y : Bool) → X ∧ Y ≡ False → X ≡ False ⊔ Y ≡ False
∧-elim True Y prf = inr prf
∧-elim False Y prf = inl refl

compareWeird : ∀  {X : Set} (x y : X) → Bool
compareWeird x y = io (λ z → True) False (i x)

compareDoubleLifted : ∀ {X : Set} (x y : ↑ (↑ X)) → Bool
compareDoubleLifted x y = {!   !}

-- Structural Equality, Assumes X == X for all X
literalEquality : ∀ {X : Set} (M N : Λ X) → Bool
-- Slightly a hack, need a proper fix :(
literalEquality (var x) (var x₁) = False
literalEquality (var x) (app N N₁) = False
literalEquality (var x) (abs N) = False
literalEquality (app M M₁) (var x) = False
literalEquality (app M M₁) (app N N₁) = literalEquality M N ∧ literalEquality M₁ N₁
literalEquality (app M M₁) (abs N) = False
literalEquality (abs M) (var x) = False
literalEquality (abs M) (app N N₁) = False
literalEquality (abs M) (abs N) = literalEquality M N

-- If two terms are ≡, then they should be literallyEqual too...
statement : ∀ {X : Set} (M N : Λ X) → M ≡ N → literalEquality M N ≡ False → ⊥
statement (var x) .(var x) refl p2 = {!   !}
statement (app M M₁) .(app M M₁) refl p2 = case c1 c2 (∧-elim (literalEquality M M) (literalEquality M₁ M₁) p2) where
 c1 = λ x → statement M M refl x
 c2 = λ x → statement M₁ M₁ refl x
statement (abs M) .(abs M) refl p2 = statement M M refl p2

-- A [ B ] == A in length if B = var.
lengthStaysOnVarChange : ∀ {X : Set} (M : Λ (↑ X)) (x : X) → lenTerm M ≡ lenTerm (M [ var x ])
lengthStaysOnVarChange (var (i x)) y = refl
lengthStaysOnVarChange (var o) y = refl
lengthStaysOnVarChange (app M M₁) y = ext S (tran++ (lengthStaysOnVarChange M y) (lengthStaysOnVarChange M₁ y))
lengthStaysOnVarChange (abs M) y = ext S (lengthStaysOnVarChange M (i y) ! ext lenTerm {!   !})

improper : ∀ {X : Set} (A1 : Λ (↑ (↑ X))) (x : X) → lenTerm A1 ≡ lenTerm (bind (λ y → Λ↑ (↑→ (io var (var x)) y)) A1)
improper (var (i (i x₁))) x = refl
improper (var (i o)) x = refl
improper (var o) x = refl
improper (app A1 A2) x = ext S (tran++ (improper A1 x) (improper A2 x))
improper (abs A1) x = ext S (improper A1 (i x) ! {!   !})

lercherEq2 : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X) → A1 [ B ] ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2 (var o) A2 B prf = refl
lercherEq2 (abs (var (i o))) A2 (app (abs (var (i x))) B₁) prf = exfalso (statement (abs (var (i (i x)))) (abs (var (i o))) (_×_.fst(eqParts (eqAbs prf))) refl)
lercherEq2 (abs (var (i o))) A2 (app (abs (var o)) B₁) prf = exfalso (statement (abs (var o)) (abs (var (i o))) (_×_.fst(eqParts (eqAbs prf))) refl)
lercherEq2 (abs (app A1 A3)) A2 (var x) prf = exfalso (<-irrefl (lenTerm A1) (<-eq  (<-eq (add>S (lenTerm A1) (S (lenTerm A3))) (ext S (S++ _ _))) (~ (improper A1 x ! (ext (lenTerm) (_×_.fst (eqParts (eqAbs prf))))))))
lercherEq2 (abs (app A1 A3)) A2 B prf = {!   !}
-- exfalso (<-irrefl (lenTerm A1) {!   !})
-- lengthStaysOnVarChange A1 (i x) !
-- ~ (ext (lenTerm) (_×_.fst (eqParts (eqAbs prf))))


easiest : ∀ {X : Set} (M : Λ (↑ X)) (N : Λ X) → (o ∈ M) → (M ≡ var o) ⊔ lenTerm M < lenTerm (M [ N ])
easiest m N p = {!   !}

-- Consider M [ N ], if M contains o, and N isn't var.
-- then | M | < | M [ N ] | (PS, in our case, N is abs)
easyCase : ∀ (q : Λ (↑ (↑ ⊥))) (l : Λ ⊥)  → (o ∈ q) → lenTerm l < lenTerm (bind (io var l) (abs q))
easyCase q l op = {! easiest q (Λ↑ (i l)) op  !}

check : ∀ {X : Set} (M : Λ (↑ (↑ X))) → ¬ (o ∈ (abs M)) → ¬ (o ∈ M)
check .(var o) op here = {!   !}
check .(app _ t) op (left n t) = {!   !}
check .(app s _) op (right s n) = {!   !}
check .(abs _) op (down n) = {!   !}

notPresent : ∀ {X : Set} (M : Λ (↑ X)) (N : Λ X) → ¬ (o ∈ M) → lenTerm M ≡ lenTerm (M [ N ])
notPresent (var (i x)) N prf = refl
notPresent (var o) N prf = exfalso (prf here)
notPresent (app M M₁) N prf = ext S {!   !}
notPresent {X} (abs M) N prf = ext S (notPresent M (Λ↑ (i N)) (check M prf) ! ext lenTerm {!  !})

work : ∀ (q : Λ (↑ (↑ ⊥))) (l : Λ ⊥) → app (var o) (abs q) [ l ] ≡ app (abs (app (var o) (abs q))) l → o ∈ q → ⊥
work q l prf qp = {!   !} where
  lhs = (_×_.fst (eqParts prf))
  rhs = (_×_.snd (eqParts prf))
  left,right = eqParts prf

fl : ∀ {X : Set} {N M : Λ X} → N ≡ M → lenTerm M ≡ lenTerm N
fl refl = refl

impossibleProof : ∀ {X : Set} (N M : Λ X) → lenTerm N < lenTerm M ⊔ lenTerm M < lenTerm N → ¬ (M ≡ N)
impossibleProof M .M (inl x) refl = <-irrefl (lenTerm M) x
impossibleProof N .N (inr x) refl = <-irrefl (lenTerm N) x

impossible2 : ∀ {X : Set} {N M Q : Λ X} → M ≡ N → N ≡ Q → ¬ (M ≡ Q) → ⊥
impossible2 refl refl q = q refl

lercher : ∀ (P : Λ (↑ ⊥)) (Q : Λ ⊥) → P [ Q ] ≡ app (abs P) Q → abs P ≡ ω × Q ≡ ω
lercher (var (i x)) q prf = exfalso x
lercher (var o) q prf = exfalso (<-irrefl lt (<-eq (<<S lt) (ext (lenTerm) (~ prf)))) where lt = lenTerm q
lercher (app (var o) (var o)) l prf = refl , _×_.fst (eqParts prf)
-- Given: l = abs (app o (abs q))
-- And l = (abs q) [l]
-- Either q has o or not, if it does:
  -- Then, l isn't consistent... since l = abs l {at the least}
lercher (app (var o) (abs q)) l prf = exfalso (case (λ t → work q l prf t) c2 (em (o ∈ q))) where
  -- prf states: app l (abs q [l]) = app (abs ...) l
  -- then: l = abs ...
  -- and:  l = (abs q) [l]
  -- AND q contains o...
  -- c1 = λ t -> exfalso (<-irrefl (lenTerm l) {! lenPart   !})
    -- lenPart = easyCase q {! abs (app (var o) (abs q)) !} {! t  !}}

  c2 = λ t → {!   !}
-- lercher (app (abs p) q) l prf = {!   !}
lercher (app (var (i x)) (app q q₁)) l prf = exfalso x
lercher (app (var o) (app q q₁)) l prf = {!   !}
lercher (app (var o) (abs (var (i (i x))))) l prf = exfalso x
lercher (app (var o) (abs (var (i o)))) l prf = exfalso (<-irrefl (lenTerm l) (<-eq (<-eq (<S (lenTerm l)) (ext S (liftingKeepsLength l))) (ext (lenTerm) (_×_.snd (eqParts prf)))))
lercher (app (var o) (abs (app (var (i (i x))) q₁))) l prf = exfalso x
lercher (app (var o) (abs (app (var (i o)) q₁))) l prf = {!   !}
lercher (app (var o) (abs (app (var o) (var (i (i x)))))) l prf = exfalso x
lercher (app (var o) (abs (app (var o) (var (i o))))) l prf = exfalso (<-irrefl (lenTerm l) (<-eq (<-eq (<<S (lenTerm l)) (ext S (ext S (liftingKeepsLength l)))) (ext (lenTerm) (_×_.snd (eqParts prf)))))
lercher (app (var o) (abs (app (var o) (abs q₁)))) l prf = {!   !}
lercher (app (abs p) q) l prf = {!   !}

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
