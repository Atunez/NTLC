module Cycles23 where

open import Lambda public
open import Cycles public
open import Length public
open import Cycles2 public
open import Decidability public
-- open import Bicycles public

-- cheat : ∀ {X} → ¬ TwoCycleSolutions {X}
-- cheat = {!   !}

appVar : ∀ {X} (P1 P2 : Λ X) x → app P1 P2 ≡ var x → ⊥
appVar P1 P2 x ()

absApp : ∀ {X} (P1 P2 : Λ X) P3 → abs P3 ≡ app P1 P2 → ⊥
absApp P1 P2 P3 ()

eq21Helper : ∀ {X} (M : Λ (↑ (↑ X))) (N : Λ X) → bind (io var (Λ→ i N)) M ≡ var o → M ≡ var (i o)
eq21Helper (var (i o)) N p = refl
eq21Helper (var o) N p = exfalso ((o∉Λ→i N) (var∈≡ (Λ→ i N) o p))

NoBindOnNoO : ∀ {X} (M : Λ (↑ X)) (Q P : Λ X)  → ¬ (o ∈ M) → M [ Q ]ₒ ≡ P → M ≡ Λ→ i P
NoBindOnNoO M Q P nocc e = occurs-map M P Q e nocc

NoBindOnNoO2 : ∀ {X} (M : Λ (↑ (↑ X))) (Q P R : Λ X) → ¬ (i o ∈ M) → ¬ (o ∈ M) → (M [ Λ→i P ]ₒ) [ Q ]ₒ ≡ R → M ≡ Λ→ i (Λ→ i R)
NoBindOnNoO2 M Q P R nio no p =
   let topLevel = occurs-map (M [ Λ→i P ]ₒ) R Q p (∉[∈] M nio (io var (Λ→ i P)) (λ {(i (i x)) → λ _ ()
                                                                                  ; (i o) → λ z _ → nio z
                                                                                  ; o → λ z _ → no z}))
   in occurs-map M (Λ→ i R) (Λ→ i P) topLevel no

NBOWLemma : ∀ {X} (P Q : Λ X) (f : ↑ X → Λ X) (g : X → ↑ X) → (∀ x → x ∈ P → f (g x) ≡ var x) → (Λ→ g P) [ f ] ≡ P
NBOWLemma (var x) Q f g fn = fn x here
NBOWLemma (app P P₁) Q f g fn = app≡ (NBOWLemma P Q f g (λ x z → fn x (left z P₁))) (NBOWLemma P₁ Q f g (λ x z → fn x (right P z)))
NBOWLemma (abs P) Q f g fn = abs≡ (NBOWLemma P (Λ→ i Q) (lift f) (↑→ g) λ {(i x) → λ q → ext (Λ→ i) (fn x (down q))
                                                                         ; o → λ _ → refl})

NoBindOnWeaking : ∀ {X} (P Q : Λ X) → (Λ→ i P) [ Q ]ₒ ≡ P
NoBindOnWeaking P Q = NBOWLemma P Q (io var Q) i (λ x _ → refl)


eq21L3L : ∀ {X} (L3 : Λ (↑ (↑ X))) (Q : Λ (↑ X)) (f : ↑ (↑ X) → Λ (↑ X)) (x : ↑ X) → f (i x) ≡ var x → (i x) ∈ L3 → L3 [ f ] ≡ Q → x ∈ Q
eq21L3L (var (i y)) Q f .y e here p = transp (λ t → y ∈ t) (~ e ! p) here
eq21L3L (app L3 L4) (app Q Q₁) f x e (left occ .L4) p = left (eq21L3L L3 Q f x e occ (_×_.fst (app≡inv p))) Q₁
eq21L3L (app L3 L4) (app Q Q₁) f x e (right .L3 occ) p = right Q (eq21L3L L4 Q₁ f x e occ (_×_.snd (app≡inv p)))
eq21L3L (abs L3) (abs Q) f x e (down occ) p = down (eq21L3L L3 Q (lift f) (i x) (ext (Λ→i) e) occ (abs≡inv p))

-- If L3[Q, P] = Q, then either L3 is y or L3[y, x] = L3[x], ie y ∉ L3
eq21L3 : ∀ {X} (L3 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (io var (Λ→ i P)) L3) ≡ Q → L3 ≡ var (i o) ⊔ ¬ ((i o) ∈ L3)
eq21L3 L3 P Q p with lercherEq3 (L3 [ Λ→ i P ]ₒ) _ p
eq21L3 (var (i o)) P Q p | inl x = inl refl
eq21L3 (var o) P Q p | inl x = exfalso (o∉Λ→i P (transp (λ t → o ∈ t) (~ x) here))
... | inr x = inr λ q → o∉Λ→i Q (eq21L3L L3 (Λ→ i Q) (io var (Λ→ i P)) o refl q x)

-- This should be true...?
-- If L2 contained more than 1 o, then more occurences of P would be on the LHS than the RHS
-- If L2 was an abstraction, then, all instances of i o, get replaced with P, but then the top level of the RHS would be abs
-- But, that isn't the case.
eq24L2Lemma :  ∀ {X} (L2 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (bind (io var Q) ∘ io var (Λ→ i P)) L2 ≡ P → o ∈ L2 → L2 ≡ var o
eq24L2Lemma L2 P Q p occ = bind-rec L2  (bind (io var Q) ∘ io var (Λ→ i P)) occ (p !~ NoBindOnWeaking P Q )

eq24L2 : ∀ {X} (L2 : Λ (↑ (↑ X))) (P Q : Λ X) → bind (io var Q) (bind (io var (Λ→ i P)) L2) ≡ P → L2 ≡ var o ⊔ ¬ (o ∈ L2)
eq24L2 L2 P Q p with decTop L2
... | inl yes = inl yes
... | inr no = inr λ q → no (eq24L2Lemma L2 P Q (bind-law (io var (Λ→ i P)) (io var Q) L2  ! p) q )

eq24 : ∀ {X} (L12 : Λ (↑ (↑ X))) (P Q : Λ X) → dec X → (L12 [ Λ→i P ]ₒ) [ Q ]ₒ ≡ app (abs (abs (app L12 (var (i o))))) P → pure (app (app (abs (abs (app L12 (var (i o))))) P) Q) → ⊥
-- L12 = y: then Q = (\y.\x.xx)P, Thus QQ -> wQ -> QQ, but this isn't pure...
eq24 (var (i o)) P .(app (abs (abs (app (var (i o)) (var (i o))))) P) d refl np with np (contr _ (appL→ (redex _ P))) (contr _ (appR→ (redex _ P)))
... | ()
-- L12 = x: P [ Q ] = ... P ... << Infinite term
eq24 (var o) P Q d p np with ~ NoBindOnWeaking P Q ! p
... | ()
-- L12 = L1 L2, then with P get that:
eq24 (app L1 L2) P Q d p np with app≡inv p
-- p1 -> L1 [ x=P, y=Q ] = L1 L2 y
-- p2 -> L2 [ x=P, y=Q ] = P <-- From finitness: Either L2 is x, or x isn't in L2
... | (p1 , p2) with eq24L2 L2 P Q p2
-- This is eq28
-- All cases lead to something...
-- eq24 (app L1 .(var o)) P Q d p np | p1 , p2 | inl refl = {!   !} -- exfalso (cheat (pure1 {!   !} ) )
-- Real Solution
eq24 (app (var (i o)) .(var o)) P Q d p np | p1 , p2 | inl refl = {!   !} -- exfalso (cheat (pure1 {!   !} ) )
-- This is a contradiction, due to purity
eq24 (app (var o) .(var o)) P Q d p np | p1 , p2 | inl refl = {!   !}
-- This has an infinite term
eq24 (app (abs L1) .(var o)) P Q d p np | p1 , p2 | inl refl = {!   !}
-- This is eq29 {Following 3 statements}
-- This is a real solution, assuming L2[Q] is in NF
-- impure solution
eq24 (app (var (i o)) L2) P Q d p np | p1 , p2 | inr L2hasnoX = {!   !}
-- This is a contradiction, since you get a term with 2 redexes
-- Impure...
eq24 (app (var o) L2) P Q d p np | p1 , p2 | inr L2hasnoX = {!   !}
eq24 (app (abs L1) L2) P Q d p np | p1 , p2 | inr L2hasnoX with np (contr ((app (app (abs (abs (app (L1 [ L2 ]ₒ) (var (i o))))) P) Q)) (appL→ (appL→ (abs→ (abs→ (appL→ (redex L1 L2)))))))
                                                                   (contr _ (appL→ (redex (abs (app (app (abs L1) L2) (var (i o)))) P)))
... | ()

fP : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → (L [ lift (io var P) ]) [ io var Q ] ≡ L [ io (io var P) Q ]
fP (var (i (i x))) P Q = refl
fP (var (i o)) P Q = {!   !}
fP (var o) P Q = refl
fP (app L L₁) P Q = {!   !}
fP (abs L) P Q = {!   !}


eq21check2 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → app (app (abs (abs L)) P ) Q ⇒ ((L [ io var (Λ→ i Q) ]) [ io var P ])
eq21check2 L P Q = 
  let step1 = appL→ {Z = Q} (redex (abs L) P)
      step2 : app (abs L [ P ]ₒ) Q ⇒ ((L [ lift (io var P) ]) [ io var Q ])
      step2 = c* (redex _ _) (ε* (bind (io var Q) (bind (lift (io var P)) L)))
      total = c* step1 {!   !}
  in {!   !}

eq21check : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → app (app (abs (abs L)) P ) Q ⇒ (L [ io (io var P) Q ])
eq21check L P Q =
  let step1 = appL→ {Z = Q} (redex (abs L) P)
      step2 : app (abs L [ P ]ₒ) Q ⇒ bind (io var Q) (bind (lift (io var P)) L)
      step2 = c* (redex _ _ ) (ε* (bind (io var Q) (bind (lift (io var P)) L)) )
      -- step2 = c* step1 (c* redex (ε* ? ))
      e = λ {  o → refl ; (i o) → NoBindOnWeaking P Q ; (i (i x)) → refl }
      eq : bind (io var Q) (bind (lift (io var P)) L) ≡  (L [ io (io var P) Q ])
      eq = ((~ bind-law ((lift (io var P))) ((io var Q)) L ))  ! bind-ext e L
      s = {!   !}
    in transp (λ z → app (app (abs (abs L)) P) Q ⇒ z) eq (c* step1 step2)

eq21 : ∀ {X} (L : Λ (↑ (↑ X))) (P Q : Λ X) → dec X → (L [ Λ→i P ]ₒ) [ Q ]ₒ ≡ app (app (abs (abs L)) P) Q → pure (app (app (abs (abs L)) P) Q) → ⊥
-- eq21 L P Q d p np = {! app (app (abs (abs L)) P ) Q  !}
-- L = free var, then, proof provided is false
eq21 (var (i (i x))) P Q d () np
-- L = y: then with p, we get an infinit term {Q contains itself}.
eq21 (var (i o)) P Q d () np
-- L = x:, then p states that P [ Q ] = I P Q, which is impossible...
eq21 (var o) P Q d p np with ~ NoBindOnWeaking P Q ! p
... | ()
-- L = L12 L3: then with p we get that
-- L12 [ x=P, y=Q ] = (L12 L3) P
-- L3 [ x=P, y=Q ] = Q <-- From finitness: Either L3 is y, or y isn't in L3.
eq21 (app L12 L3) P Q d p np with app≡inv p
... | (p1 , p2) with eq21L3 L3 P Q p2
-- L3 is Var, leads to eq24
... | inl refl = {!   !} -- eq24 L12 P Q d p1 np
-- L3 doesn't contain y. Leads to eq32
eq21 (app (var (i o)) L3) P .(app (abs (abs (app (var (i o)) L3))) P) d p np | refl , p2 | inr L3hasnoY with np (contr _ (appL→ (redex _ P))) (contr _ (appR→ (redex _ P)))
... | ()
-- This generates an infinite term
eq21 (app (var o) L3) P Q d p np | p1 , p2 | inr L3hasnoY with ~ NoBindOnWeaking P Q ! p1
... | ()
eq21 (app L12@(app L1 L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY with app≡inv p1
-- From P1:
-- L1 [ x=P, y=Q ] = L1 L2 y
-- L2 [ x=P, y=Q ] = P <-- From finitness: Either L2 is x, or x isn't in L2
-- These are 33, 34.
-- Applying line 35:
-- L1 = y, then we do case on L3 and where x occures
-- We can case L3 into 3 cases: L3 = x, L3 doesn't have x, or x ∈ L3 ≢ ≡ x.
eq21 (app (app (var (i o)) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p11 , p12 with decΛ ((dec↑ (dec↑ d)) o) L3
-- If x is in L3, then either L3 = x {Case 1}, or not {Case 3}.
... | inl oInL3 with decTop L3
-- L3 = x {Case 1}
-- We now check on L2, either it is x or x isn't in it.
... | inl refl = case (λ {refl → {!   !}}) {!   !} (eq24L2 L2 P Q p12)
-- L3 doesn't contain x {Case 3}
... | inr L3isNotVar = {!   !}
-- L3 doesn't contain x {Case 2}  We get an infinite term.
-- Agda can't figure out what to expand ... with sometimes
eq21 (app (app (var (i o)) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p11 , p12 | inr oNotInL3 with NoBindOnNoO2 _ _ _ _ L3hasnoY oNotInL3 p2
... | refl = len≡≠ _ _ p11 λ q → ¬S4≤ (zero≤ ≤+≤ ≡≤≡ (~ len→ i Q ! ~ len→ i (Λ→ i Q))) q
-- L1 = x > leads to impure solution, line 36
eq21 (app (app (var o) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p11 , p12 = {!   !}
-- L1 = \z.? -> Impure solution
eq21 (app (app (abs L1) L2) L3) P Q d p np | p1 , p2 | inr L3hasnoY | p11 , p12 with np (contr _ (appL→ (redex (abs (app (app (abs L1) L2) L3)) P)))
                                                                                        (contr _ (appL→ (appL→ (abs→ (abs→ (appL→ (redex L1 L2)))))))
... | ()

-- -- If you walk along the following path:
-- -- M≡(\x.\y.L[x,y])PQ → (\y.L[P,y])Q → L[P,Q]≡M
-- -- Then, Q ≡ \xy.yxy OR P ≡ Q × (P ≡ \xy.yxx OR \xy.yyx) OR Q ≡ \xy.y?y where ? doesn't contain b as the LHS of App
PA2 : ∀ (L : Λ (↑ (↑ ⊥))) (P Q t1 t2 : Λ ⊥) → app (app (abs (abs L)) P) Q ⟶ t1 → t1 ≡ app ((abs L) [ P ]ₒ) Q → app ((abs L) [ P ]ₒ) Q ⟶ t2 → t2 ≡ L [ Λ→i P ]ₒ [ Q ]ₒ → ⊥
PA2 L P Q .(app (abs L [ P ]ₒ) Q) .(bind (lift (io var P)) L [ Q ]ₒ) (appL→ (redex .(abs L) .P)) p1 (redex .(bind (lift (io var P)) L) .Q) p2 = {!   !}
PA2 L P Q .(app (abs L [ P ]ₒ) Q) .(app _ Q) (appL→ (redex .(abs L) .P)) p1 (appL→ r2) p2 = {!   !}
PA2 L P Q .(app (abs L [ P ]ₒ) Q) .(app (abs L [ P ]ₒ) _) (appL→ (redex .(abs L) .P)) p1 (appR→ r2) p2 = {!   !}
