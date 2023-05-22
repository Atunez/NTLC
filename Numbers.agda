module Numbers where

open import Equality

data Nat : Set where
    O : Nat
    S : Nat → Nat

_++_ : Nat → Nat → Nat
O ++ m = m
S n ++ m = S (n ++ m)

O++ : ∀ m → m ≡ m ++ O
O++ O = refl
O++ (S m) = ext S (O++ m)

S++ : ∀ m n → m ++ S n ≡ S (m ++ n)
S++ O n = refl
S++ (S m) n = ext S (S++ m n)

comm++ : ∀ n m → n ++ m ≡ m ++ n
comm++ O m = O++ m
comm++ (S n) m = (ext S (comm++ n m) ) ! (~ (S++ m n) )

tran++ : ∀ {n m p q} → n ≡ m → p ≡ q → n ++ p ≡ m ++ q
tran++ refl refl = refl

data _<_ : Nat → Nat → Set where
  O< : ∀ n → O < S n
  S< : ∀ n m → n < m → S n < S m


<-eq : ∀ {n m l} → n < m → m ≡ l → n < l
<-eq p (refl) = p

<-irrefl : ∀ n → n < n → ⊥
<-irrefl (S n) (S< n .n p) = <-irrefl n p

tran< : ∀ l n m → l < m → m < n → l < n
tran< .O .(S m) .(S n) (O< .n) (S< n m q) = O< m
tran< .(S n₁) .(S m) .(S n) (S< n₁ .n p) (S< n m q) = S< _ _ (tran< _ _ _ p q)

<S : ∀ n → n < S n
<S O = O< O
<S (S n) = S< n (S n) (<S n)

<S-eq : ∀ {m n : Nat} → n < S n → n ≡ m → n < S m
<S-eq p refl = p

add<S : ∀ n m → n < (S m ++ n)
add<S n O = <S n
add<S n (S m) = tran< n _ _ (add<S n m) (<S _)

add>S : ∀ n m → n < S (n ++ m)
add>S O m = O< m
add>S (S n) m = S< _ _ (add>S n m)

<-deq : ∀ {m n p q} → p ≡ m → m < n → n ≡ q → p < q
<-deq refl l refl = l

<<S : ∀ n → n < S (S n)
<<S O = O< (S O)
<<S (S n) = S< n (S (S n)) (<<S n)

data _≤_ : Nat → Nat → Set where
  O≤ : ∀ {n} → O ≤ n
  S≤ : ∀ {n m} → n ≤ m → S n ≤ S m

≡≤ : ∀ {k l m} → k ≡ l → l ≤ m → k ≤ m
≡≤ refl le = le

lelte : ∀ {m n l : Nat} → n < m → m ≤ l → n ≤ l
lelte (O< n) q = O≤
lelte (S< n m p) (S≤ q) = S≤ (lelte p q)

ltele : ∀ {n m l : Nat} → n < m → m ≤ l → n < l
ltele (O< n) (S≤ q) = O< _
ltele (S< n m p) (S≤ q) = S< n _ (ltele p q)

≤-eq : ∀ {m n l : Nat} → n ≤ m → m ≡ l → n ≤ l
≤-eq p refl = p

≤S : ∀ (n : Nat) → n ≤ n
≤S O = O≤
≤S (S n) = S≤ (≤S n)

≤≡ : ∀ {m n : Nat} → m ≡ n → m ≤ n
≤≡ refl = ≤S _

≤++ : ∀ {n m n' m'} → n ≤ m → n' ≤ m' → (n ++ n') ≤ (m ++ m')
≤++ O≤ O≤ = O≤
≤++ O≤ (S≤ p2) = ≤-eq (S≤ (≤++ O≤ p2)) (~ S++ _ _)
≤++ (S≤ p1) p2 = S≤ (≤++ p1 p2)

lestrict : ∀ {m} {n} → m < n → n ≤ m → ⊥
lestrict mn nm = <-irrefl _ (ltele mn nm )