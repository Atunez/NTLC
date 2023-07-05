module Numbers where

open import BasicLogic

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

_≡≤_ : ∀ {l m n} → l ≡ m → m ≤ n → l ≤ n
refl ≡≤ p = p

lelte : ∀ {m n l : Nat} → n < m → m ≤ l → n ≤ l
lelte (O< n) q = O≤
lelte (S< n m p) (S≤ q) = S≤ (lelte p q)

ltele : ∀ {n m l : Nat} → n < m → m ≤ l → n < l
ltele (O< n) (S≤ q) = O< _
ltele (S< n m p) (S≤ q) = S< n _ (ltele p q)

≤-eq : ∀ {m n l : Nat} → n ≤ m → m ≡ l → n ≤ l
≤-eq p refl = p

≤refl : ∀ (n : Nat) → n ≤ n
≤refl O = O≤
≤refl (S n) = S≤ (≤refl n)

≤S : ∀ {n m : Nat} → n ≤ m → n ≤ S m
≤S O≤ = O≤
≤S (S≤ nm) = S≤ (≤S nm)

≤++ : ∀ {n m n' m'} → n ≤ m → n' ≤ m' → (n ++ n') ≤ (m ++ m')
≤++ O≤ O≤ = O≤
≤++ O≤ (S≤ p2) = ≤-eq (S≤ (≤++ O≤ p2)) (~ S++ _ _)
≤++ (S≤ p1) p2 = S≤ (≤++ p1 p2)

lestrict : ∀ {m} {n} → m < n → n ≤ m → ⊥
lestrict mn nm = <-irrefl _ (ltele mn nm )

++≤ : ∀ {m n s} → (m ++ n) ≤ s → (n ++ m) ≤ s
++≤ {m} {n} p = (comm++ n m) ≡≤ p

++S≤ : ∀ {m n s} → S (m ++ n) ≤ s → S (n ++ m) ≤ s
++S≤ {m} {n} (S≤ p) = S≤ ((comm++ n m) ≡≤ p)  

numbersDontAdd : ∀ {m n} → m ≡ n → m ≡ S (S n) → ⊥
numbersDontAdd refl ()

numbersDontAdd3 : ∀ {m n} → m ≡ n → m ≡ (S n) → ⊥
numbersDontAdd3 refl ()

lemmaNum : ∀ (m q : Nat) → m < S (S (m ++ q))
lemmaNum O q = O< (S q)
lemmaNum (S m) q = S< m (S (S (m ++ q))) (lemmaNum m q)

numbersDontAdd2 : ∀ (m n q : Nat) → m ≡ n → m ≡ S (S (n ++ q)) → ⊥
numbersDontAdd2 m n q refl o = lestrict (lemmaNum _ _) ((~ o) ≡≤ ≤refl m)


_≡+≡_ : ∀ {m1 m2 n1 n2} → m1 ≡ m2 → n1 ≡ n2 → m1 ++ n1 ≡ m2 ++ n2
refl ≡+≡ refl = refl

zero≤ : ∀ {m : Nat} → O ≤ m
zero≤ {m} = O≤

tran≤ : ∀ {l m n : Nat} → l ≤ m → m ≤ n → l ≤ n
tran≤ O≤ mn = O≤
tran≤ (S≤ lm) (S≤ mn) = S≤ (tran≤ lm mn)


¬S≤ : ∀ {m : Nat} → ¬ (S m ≤ m)
¬S≤ {S m} (S≤ le) = ¬S≤ le 

asym≤ : ∀ {m n : Nat} → m ≤ n → n ≤ m → m ≡ n
asym≤ O≤ O≤ = refl
asym≤ (S≤ mn) (S≤ nm) = ext S (asym≤ mn nm)

_≤≡_ : ∀ {l m n} → l ≤ m → m ≡ n → l ≤ n
p ≤≡ refl = p


_≤+≤_ : ∀ {m1 m2 n1 n2} → m1 ≤ m2 → n1 ≤ n2 → (m1 ++ n1) ≤ (m2 ++ n2)
O≤ ≤+≤ O≤ = O≤
S≤ p1 ≤+≤ O≤ = S≤ (p1 ≤+≤ O≤)
O≤ ≤+≤ S≤ p2 = S≤  (O≤ ≤+≤ p2) ≤≡ (~ S++ _ _)
S≤ p1 ≤+≤ S≤ p2 = S≤ (p1 ≤+≤ S≤ p2)

++≤L : ∀ l m → l ≤ (l ++ m)
++≤L O m = O≤
++≤L (S l) m = S≤ (++≤L l m)

++≤LN : ∀ {l m} n → l ≤ m → l ≤ (m ++ n)
++≤LN n O≤ = O≤
++≤LN n (S≤ p) = S≤ (++≤LN n p)

++≤R : ∀ l m → m ≤ (l ++ m)
++≤R l O = O≤
++≤R l (S m) = S≤ (++≤L m l) ≤≡ comm++ (S m) l 

¬S4 : ∀ {m n} → m ≡ n → m ≡ S (S (S (S n))) → ⊥
¬S4 refl () 

¬S< : ∀ {m n} → m ≡ n → m < n → ⊥
¬S< refl p = <-irrefl _ p

¬S≤4 : ∀ {m : Nat} → ¬ (S (S (S (S m))) ≤ m)
¬S≤4 {S m} (S≤ le) = ¬S≤4 le

¬S4≤ : ∀ {m n} → m ≤ n → m ≡ S (S (S (S n))) → ⊥
¬S4≤ p refl = ¬S≤4 p

¬S≤3 : ∀ {m : Nat} → ¬ ((S (S (S m))) ≤ m)
¬S≤3 {S m} (S≤ le) = ¬S≤3 le

¬S3≤ : ∀ {m n} → m ≤ n → m ≡ S (S (S n)) → ⊥
¬S3≤ p refl = ¬S≤3 p
 