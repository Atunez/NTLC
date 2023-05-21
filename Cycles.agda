module Cycles where

-- open import Agda.Builtin.Sigma
-- open import Data.Product
open import Lambda

O++ : ∀ m → m ≡ m ++ O
O++ O = refl
O++ (S m) = ext S (O++ m)

S++ : ∀ m n → m ++ S n ≡ S (m ++ n)
S++ O n = refl
S++ (S m) n = ext S (S++ m n)

comm++ : ∀ n m → n ++ m ≡ m ++ n
comm++ O m = O++ m
comm++ (S n) m = (ext S (comm++ n m) ) ! (~ (S++ m n) )


-- \| is ∣
∣_∣  : ∀ {X : Set} → Λ X → Nat
∣ var x ∣ = O
∣ abs r ∣ = S ∣ r ∣
∣ app s t ∣ = S (∣ s ∣  ++ ∣ t ∣)

data _<_ : Nat → Nat → Set where
  O< : ∀ n → O < S n
  S< : ∀ n m → n < m → S n < S m

<-eq : ∀ n m l → n < m → m ≡ l → n < l
<-eq n m l p (refl) = p

<-irrefl : ∀ n → n < n → ⊥
<-irrefl (S n) (S< n .n p) = <-irrefl n p

tran< : ∀ l n m → l < m → m < n → l < n
-- tran< l n m p q = ?
tran< .O .(S m) .(S n) (O< .n) (S< n m q) = O< m
tran< .(S n₁) .(S m) .(S n) (S< n₁ .n p) (S< n m q) = S< _ _ (tran< _ _ _ p q)

<S : ∀ n → n < S n
<S O = O< O
<S (S n) = S< n (S n) (<S n)

add<S : ∀ n m → n < (S m ++ n)
add<S n O = <S n
add<S n (S m) = tran< n _ _ (add<S n m) (<S _)

add>S : ∀ n m → n < S (n ++ m)
add>S O m = O< m
add>S (S n) m = S< _ _ (add>S n m)

abs< : ∀ {X} (s : Λ (↑ X)) → ∣ s ∣ < ∣ abs s ∣
abs< s = <S ∣ s ∣

app<L : ∀ {X} (s t : Λ X) → ∣ s ∣ < ∣ app s t ∣
app<L s t =  <-eq (∣ s ∣) _ _ (add<S (∣ s ∣) (∣ t ∣)) (ext S (comm++ ∣ t ∣ ∣ s ∣ ) )

app<R : ∀ {X} (s t : Λ X) → ∣ t ∣ < ∣ app s t ∣
app<R s t =  add<S (∣ t ∣) (∣ s ∣)

data _∈_ {X : Set} (x : X) : Λ X → Set where
  here  : x ∈ var x
  left  : ∀ {s : Λ X} → (x ∈ s) → (t : Λ X) → x ∈ app s t
  right : ∀ (s : Λ X) → {t : Λ X} → (x ∈ t) → x ∈ app s t
  down  : ∀ {r : Λ (↑ X)} → (i x ∈ r) → (x ∈ abs r)

-- occursLemma1 : ∀ {X : Set} (M : Λ (↑ X)) (N : Λ X) → o ∈ M → M ≡ var o ⊔ ∣ N ∣ < ∣ M [ N ] ∣
-- occursLemma1 .(var o) N here = inl refl
-- occursLemma1 (app s t) N (left p t) = inr (case c1 c2 (occursLemma1 s N p) ) where
--   f = λ x → S (∣ bind (io var N) x ∣ ++ ∣ bind (io var N) t ∣)
--   c1 = λ q → <-eq _ _ _ (add>S ∣ N ∣ _ ) (ext f (~ q))
--   c2 = λ q → tran< _ _ _ q (add>S _ _)
-- occursLemma1 .(app s _) N (right s p) = {!   !}
-- occursLemma1 (abs r) N (down p) = {! inr (case c1 c2 (occursLemma1 r (Λ→ i N) ))  !}

-- -- occursLemma2 : ∀ {X : Set} (M : Λ (↑ X)) (N : Λ X) (x : X) → x ∈ M → M ≡ var x ⊔ ∣ N ∣ < ∣ M [ N ] ∣

-- ω : Λ ⊥
-- ω = abs (app (var o) (var o))

-- app≡inv : ∀ {X} (M M' N N' : Λ X) → app M N ≡ app M' N' → M ≡ M' × N ≡ N'
-- app≡inv M .M N .N refl = ( refl , refl )

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

-- -- lercherEq2 : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X) → A [ B ] ≡ abs (app A1 A2) → A1 ≡ var o
-- -- lercherEq2 = ?

-- -- lercher : ∀ (P : Λ (↑ ⊥)) (Q : Λ ⊥) → P [ Q ] ≡ app (abs P) Q → abs P ≡ ω × Q ≡ ω
-- -- lercher (var (i x)) Q p = ex x falso
-- -- lercher (var o) Q p = ex_falso (<-irrefl (∣ Q ∣) (<-eq _ _ _ (app<R (abs (var o)) Q) (ext ∣_∣ (~ p) ) ) )
-- -- lercher (app P₁ P₂) Q p =
-- --   let (p1 , p2) = app≡inv _ _ _ _ p
-- --    in {!   !}

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
