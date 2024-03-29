module Cycles where

open import Lambda public
open import Length

bind-rec : ∀ {X Y : Set} (A : Λ X) (f : X → Λ Y) {x : X}
             → x ∈ A → (A [ f ] ≡ f x) → A ≡ var x
bind-rec (var x) f here eq = refl
bind-rec (app A1 A2) f (left occ .A2)  eq = exfalso (¬S≤ {len (A1 [ f ]) ++ len (A2 [ f ])}
               (ext len eq ≡≤ tran≤ (len∈bind f A1 occ) (++≤L _ _) ) )
bind-rec (app A1 A2) f (right .A1 occ) eq = exfalso (¬S≤ {len (A1 [ f ]) ++ len (A2 [ f ])}
               (ext len eq ≡≤ tran≤ (len∈bind f A2 occ) (++≤R _ _) ) )
bind-rec (abs A0) f (down occ) eq = exfalso (¬S≤ {len (bind (lift f) A0)}
               (ext len eq ≡≤ ((~ (len→ i (f _) )) ≡≤ len∈bind (lift f) A0 occ) ))

occurs-map-gen2 : ∀ {X} (A : Λ (↑ (↑ X))) (B : Λ X) (f : ↑ (↑ X) → Λ (↑ X)) → (∀ x → (i x) ∈ A → x ∈ f (i x)) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → A [ f ] ≡ Λ→ i B → ¬ (i o ∈ A) → ¬ (o ∈ A) → A ≡ Λ→i (Λ→ i B)
occurs-map-gen2 A B f fn1 fn2 e nocc1 nocc2 =
  let e0 : ∀ x → x ∈ A → var x ≡ (Λ→ i ∘ f) x
      e0 = λ {(i (i x)) → λ q → ~ ext Λ→i (fn2 (i x) (fn1 (i x) q))
            ; (i o) → λ q → exfalso (nocc1 q)
            ; o → λ q → exfalso (nocc2 q)}
      e1 = symm (bind-nat1 i f)
      e2 = bind-occurs (var) (Λ→ i ∘ f) A e0
  in ((~ bind-unit1 A ! e2) ! e1 A) ! ext (Λ→i) e

occurs-map-gen : ∀ {X} (A : Λ (↑ X)) (B : Λ X) (f : ↑ X → Λ X) → (∀ x → (i x) ∈ A → x ∈ f (i x)) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → A [ f ] ≡ B → ¬ (o ∈ A) → A ≡ Λ→i B
occurs-map-gen A B f fn1 fn2 e nocc =
  let e0 : ∀ x → x ∈ A → var x ≡ (Λ→ i ∘ f) x
      e0 = λ {(i x) → λ q → ~ ext Λ→i (fn2 x (fn1 x q))
            ; o → λ q → exfalso (nocc q)}
      e1 = symm (bind-nat1 i f)
      e2 = bind-occurs (var) (Λ→ i ∘ f) A e0
  in ((~ bind-unit1 A ! e2) ! e1 A) ! ext (Λ→i) e

occurs-map : ∀ {X} (A : Λ (↑ X)) (B C : Λ X) → A [ C ]ₒ ≡ B → ¬ (o ∈ A) → A ≡ Λ→ i B
occurs-map A B C h nocc = occurs-map-gen A B (io var C) (λ x _ → here) (λ x _ → refl) h nocc

decTop : ∀ {X} (A : Λ (↑ X)) → A ≡ var o ⊔ ¬ (A ≡ var o)
decTop (var (i x)) = inr (λ { () })
decTop (var o) = inl refl
decTop (app A1 A2) = inr (λ { () })
decTop (abs A0) = inr (λ { () })

lercherEq3 : ∀ {X} (A : Λ (↑ X)) (B : Λ X) → A [ B ]ₒ ≡ B → A ≡ var o ⊔ A ≡ Λ→ i B
lercherEq3 A B e with decTop A
... | inl yes = inl yes
... | inr no  = inr (occurs-map A B B e o∉A)
  where o∉A = λ occ → no (bind-rec A (io var B) occ e)

lercherEq2gen : ∀ {X} (A1 A2 : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → bind f A1 ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2gen (var (i x)) A2 f fn p with ~ (fn x (down (left here A2) ∈≡ (~ p))) ! p
... | ()
lercherEq2gen (var o) A2 f fn p = refl
lercherEq2gen (abs (var (i (i x)))) A2 f fn p with abs≡inv p
... | M with  fn x (occIni (f (i x)) (left (down here) A2 ∈≡ (~ M)))
... | t with ~ (ext (Λ→ i) t) ! M
... | ()
lercherEq2gen (abs (var (i o))) A2 f fn p with abs≡inv p
...   | M = exfalso (o∉Λ→i (f o) (left (down here) A2 ∈≡ (~ M)))
lercherEq2gen (abs (app A1 A3)) A2 f fn p with app≡inv (abs≡inv p)
...         | (p1 , p2) = let g = lift f
                              gn = λ {o → λ q → exfalso (o∉Λ→i (f o) q); (i x) → λ q → ext (Λ→ i) (fn x (occIni (f (i x)) q))}
                              f' = (λ x → io (Λ→ i) (var o) (↑→ f x))
                              rec = lercherEq2gen A1 A3 g gn p1
                            in ~ p1 ! ext (bind g) rec

lercherEq2 : ∀ {X} (A1 A2 : Λ (↑ X)) (B : Λ X)→ A1 [ B ]ₒ ≡ abs (app A1 A2) → A1 ≡ var o
lercherEq2 A1 A2 B p = lercherEq2gen A1 A2 (io var B) (λ x _ → refl) p

lercherHelper : ∀ (P1 P2 : Λ (↑ ⊥)) (Q : Λ ⊥) → P1 ≡ var o → P2 ≡ var o ⊔ P2 ≡ Λ→ i Q → (app P1 P2) [ Q ]ₒ ≡ app (abs (app P1 P2)) Q → abs (app P1 P2) ≡ ω × Q ≡ ω
lercherHelper .(var o) .(var o) Q refl (inl refl) p3 = refl , _×_.fst (app≡inv p3)
lercherHelper .(var o) .(Λ→ i Q) Q refl (inr refl) p3 =
  let qPrf = _×_.fst (app≡inv p3)
      A = abs (app (var o) (var (i o)))
      br = bind-rec A (io var Q) {o} (down (right (var o) here) ) (~ qPrf)
      contra : ∀ r → abs r ≡ var o → ⊥
      contra = λ { r () }
  in exfalso (contra _ br)

lercher : ∀ (P : Λ (↑ ⊥)) (Q : Λ ⊥) → P [ Q ]ₒ ≡ app (abs P) Q → abs P ≡ ω × Q ≡ ω
lercher (var (i x)) q prf = exfalso x
lercher (var o) q prf with prf
... | p =
  let A = app (abs (var o)) (var o)
      br = bind-rec A (io var q) {o} (right (abs (var o)) here) (~ p)
      contra : ∀ {r1 r2} → app r1 r2 ≡ var o → ⊥
      contra = λ { () }
      in exfalso (contra br)
lercher (app P1 P2) Q prf =
   let (lhs , rhs) = app≡inv prf
       l1 = lercherEq2 _ _ _ lhs
       l2 = lercherEq3 P2 Q rhs
   in lercherHelper _ _ _ l1 l2 prf
