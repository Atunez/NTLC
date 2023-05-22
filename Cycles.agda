module Cycles where

open import Lambda public

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


liftingKeepsLength : ∀ {X : Set} (M : Λ X) → lenTerm M ≡ lenTerm (Λ→ i M)
liftingKeepsLength N = {!   !}

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
occursLemma1 (abs r) N (down p) = inr (case c1 c2 (occursLemma2 r (Λ→ i N) o p)) where
  f = λ x → S ( lenTerm (bind (λ y → Λ↑ (↑→ (io var N) y)) x))
  c1 = λ q → <-eq (<S-eq (<S _) (liftingKeepsLength N)) (ext f (~ q))
  c2 = λ q → {!   !} -- <-deq q (~ (liftingKeepsLength N)) {!   !}

ω : Λ ⊥
ω = abs (app (var o) (var o))

app≡inv : ∀ {X} (M M' N N' : Λ X) → app M N ≡ app M' N' → M ≡ M' × N ≡ N'
app≡inv M .M N .N refl = ( refl , refl )

-- lercherEq3 : ∀ {X} (A : Λ X) (B : Λ (↑ X)) → B [ A ] ≡ A → B ≡ var o ⊔ B ≡ Λ→ i A
-- lercherEq3 A (var (i x)) p = inr (ext (Λ→ i) p)
-- lercherEq3 A (var o) p = inl refl
-- lercherEq3 (app A₁ A₂) (app B₁ B₂) p =
--   let (p1 , p2) = app≡inv _ _ _ _ p
--       -- (q1 , q2) = (lercherEq3 A₁ B₁ {!   !} , lercherEq3 A₂ B₂ ?)
--    in inr {!   !}
--    -- inr (app≡ {! p1  !} {! p2   !} ! ext (Λ→ i) p)
-- lercherEq3 A (abs B) p =
--   {!   !}

data Bool : Set where
  True : Bool
  False : Bool



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
lercherEq2 (abs (app A1 A3)) A2 B prf = exfalso (<-irrefl (lenTerm A1) {!   !})
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
-- lercher (app (var o) (abs q)) l prf = exfalso (case (λ t → work q l prf t) c2 (em (o ∈ q))) where
--   -- prf states: app l (abs q [l]) = app (abs ...) l
--   -- then: l = abs ...
--   -- and:  l = (abs q) [l]
--   -- AND q contains o...
--   c1 = λ t -> exfalso (<-irrefl (lenTerm l) {! lenPart   !})  
--     -- lenPart = easyCase q {! abs (app (var o) (abs q)) !} {! t  !}}
    
--   c2 = λ t → {!   !}
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
    