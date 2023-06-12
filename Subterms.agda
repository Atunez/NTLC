module Subterms where

open import Lambda

-- The type of subterms
-- ⊑ is \squb=
infix 17 _⊑_
data _⊑_ {X : Set} : Λ X → Λ X → Set where
  Here  : ∀ {M} → M ⊑ M
  Left  : ∀ {M N1} → M ⊑ N1 → (N2 : Λ X) → M ⊑ app N1 N2
  Right : ∀ {M} N1 {N2 : Λ X} → M ⊑ N2  → M ⊑ app N1 N2
  Down  : ∀ {M} {N : Λ (↑ X)} → Λ→i M ⊑ N → M ⊑ abs N

{- Comment 6.12
This definition is broken; the weakening in the abstraction case
precludes antisymmetry from being provable by induction.
If var o is a subterm of t,
there is no way to express that it's also a subterm of abs t.
Perhaps the types of M and N in M ⊑ N should be over different index sets,
related by a function.
-}

_≡⊑_ : ∀ {X} {s t u : Λ X} → s ≡ t → t ⊑ u → s ⊑ u
refl ≡⊑ tu = tu

⊑→ : ∀ {X Y} {s t : Λ X} → s ⊑ t → (f : X → Y) → Λ→ f s ⊑ Λ→ f t
⊑→ Here f = Here
⊑→ (Left st N2) f = Left (⊑→ st f) (Λ→ f N2)
⊑→ (Right N1 st) f = Right (Λ→ f N1) (⊑→ st f)
⊑→ (Down st) f =
  let rc = ⊑→ st (↑→ f)
      eq = tran (symm (Λ-func i f)) (tran (λ z → refl ) (Λ-func (↑→ f) i))
  in Down (eq _ ≡⊑ rc)

tran⊑ : ∀ {X} {r s t : Λ X} → r ⊑ s → s ⊑ t → r ⊑ t
tran⊑ rs Here = rs
tran⊑ rs (Left st N2) = Left (tran⊑ rs st) N2
tran⊑ rs (Right N1 st) = Right N1 (tran⊑ rs st)
tran⊑ rs (Down st) = Down (tran⊑ (⊑→ rs i) st )

⊑inv : ∀ {X} (M : Λ X) (sub : M ⊑ M) → sub ≡ Here
⊑inv (var x) Here = refl
⊑inv (app M1 M2) Here = refl
⊑inv (app M1 M2) (Left sub .M2) with Left {_} {M1} {M1} Here M2 | ⊑inv M1 (tran⊑ (Left Here M2) sub)
... | p | q = {! tran⊑ (Left Here M2) sub   !}
⊑inv (app M1 M2) (Right .M1 sub) = {!   !}
⊑inv (abs M0)  sub = {!   !}

-- ⊑inv2 : ∀ {X} (M N : Λ X) (sub : M ⊑ N) → ¬ (sub ≡ Here) → ¬ (M ≡ N)
-- ⊑inv2 M N sub ne eq = ?

¬app≡L : ∀ {X} (M N : Λ X) → ¬ (app M N ≡ M)
¬app≡L M N ()

¬app≡R : ∀ {X} (M N : Λ X) → ¬ (app M N ≡ N)
¬app≡R M N ()

¬absLemma : ∀ {X} (M : Λ (↑ X)) (f : X → ↑ X) → isInj f → Λ→ f (abs M) ≡ M → ∀ x → x ∉ M
¬absLemma (abs M) f fi p x (down occ) with abs≡inv p
... | q = ¬absLemma M (↑→ f) (↑→Inj f fi) q (i x) occ

¬abs≡ : ∀ {X} (M : Λ (↑ X)) → ¬ (Λ→i (abs M) ≡ M)
¬abs≡ (abs M) p with abs≡inv p
... | q = ¬abs≡ M (abs≡ (map-occurs (↑→ i) (↑→ (↑→ i)) M eq) ! q)
          where eq = (λ x xinM → exfalso (¬absLemma M (↑→ i) (↑→Inj i iInj ) q x xinM ) )

¬abs⊑Lemma : ∀ {X} (M : Λ (↑ X)) (f : X → ↑ X) → isInj f → (Λ→i (abs M) ⊑ M) → ∀ x → x ∉ Λ→i (abs M)
¬abs⊑Lemma M f fi sub x occ = {!   !}

¬app⊑L : ∀ {X} (M N : Λ X) → ¬ (app M N ⊑ M)
¬app⊑R : ∀ {X} (M N : Λ X) → ¬ (app M N ⊑ N)
¬abs⊑ : ∀ {X} (M : Λ (↑ X)) → ¬ (Λ→i (abs M) ⊑ M)

¬app⊑L (app M1 M2) N (Left sub .M2) = ¬app⊑L M1 M2 (tran⊑ (Left Here N) sub)
¬app⊑L (app M1 M2) N (Right .M1 sub) = ¬app⊑R M1 M2 (tran⊑ (Left Here N ) sub )
¬app⊑L (abs M0) N (Down sub) = ¬abs⊑ M0 (tran⊑ (Left Here (Λ→ i N) ) sub)

¬app⊑R M (app N1 N2) (Left mn .N2) = ¬app⊑L N1 N2 (tran⊑ (Right M Here) mn )
¬app⊑R M (app N1 N2) (Right .N1 mn) = ¬app⊑R N1 N2 (tran⊑ (Right M Here) mn )
¬app⊑R M (abs N) (Down mn) = ¬abs⊑ N (tran⊑ (Right (Λ→ i M) Here) mn  )

abs⊑dec : ∀ {X} M (N : Λ (↑ X)) → M ⊑ abs N → M ≡ abs N ⊔ (Λ→i M ⊑ N)
abs⊑dec .(abs N) N Here = inl refl
abs⊑dec M N (Down mn) = inr mn

¬abs⊑ = {!   !}
-- ¬abs⊑ (app M1 M2) (Left sub .M2) = ¬app⊑L M1 M2 (tran⊑ (Down {!   !} ) sub )
-- ¬abs⊑ (app M1 M2) (Left sub .M2) = ¬app⊑L M1 M2 (tran⊑ (Down Here ) {!   !} )
-- ¬abs⊑ (app M1 M2) (Right .M1 sub) = {!   !}
-- ¬abs⊑ (abs M) sub with abs⊑dec _ _ sub
-- ... | inl p = {! p   !}
-- ... | inr sub' = ¬abs⊑ M (tran⊑ (Down {!   !} ) sub' )

bind-rec : ∀ {X Y : Set} (A : Λ X) (f : X → Λ Y) {x : X}
             → x ∈ A → (A [ f ]) ⊑ f x → A ≡ var x
bind-rec (var x) f here sub = refl
bind-rec (app A1 A2) f (left occ .A2) sub with bind-rec A1 f occ (tran⊑ (Left Here (bind f A2) ) sub)
bind-rec (app (var x) A2) f (left here .A2) sub | refl = {!   !}
bind-rec (app A1 A2) f (right .A1 occ) sub = {!   !}
bind-rec (abs A0) f occ sub = {!   !}

-- ¬app⊑L (app M1 M2) N (Left sub .M2) = ¬app⊑L M1 M2 (tran⊑ (Left Here N ) sub )
-- ¬app⊑L (app M1 M2) N (Right .M1 sub) = ¬app⊑R M1 M2 (tran⊑ (Left Here N ) sub )
-- ¬app⊑L (abs M0) N sub = {!   !}
--
-- ¬app⊑R M N sub = {!   !}
--
asym⊑ : ∀ {X} {s t : Λ X} → s ⊑ t → t ⊑ s → s ≡ t
asym⊑ {X} {.(var x)} {var x} Here ts = refl
asym⊑ {X} {.(app t1 t2)} {app t1 t2} Here ts = refl
-- asym⊑ {X} {s} {app t1 t2} (Left Here .t2) ts = {!   !} -- ~ asym⊑ ts (Left Here t2)
asym⊑ {X} {s} {app t1 t2} (Left st .t2)  ts with asym⊑ (tran⊑ ts st) (Left Here t2)
... | ()
asym⊑ {X} {s} {app t1 t2} (Right .t1 st) ts with asym⊑ (tran⊑ ts st) (Right t1 Here)
... | ()
asym⊑ {X} {.(abs t0)} {abs t0} Here ts = refl
asym⊑ {X} {s} {abs t0} (Down st) ts with asym⊑ (tran⊑ (⊑→ ts i) st) (Down {!    !} )
... | p = exfalso (¬abs≡ t0 p)                         -- Need: o ∉ t0.  Not provable.
