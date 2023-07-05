module Subterms where

open import Lambda

-- The type of contains
-- ⊑ is \squb=
data contains {X Y : Set} : (f : X → Y) → Λ X → Λ Y → Set where
  Here  : ∀ {f} {M} → contains f M (Λ→ f M)
  Left  : ∀ {f} {M N1} → contains f N1 M → (N2 : Λ X) → contains f (app N1 N2) M -- M ⊑ app N1 N2
  Right : ∀ {f} {M} N1 {N2 : Λ X} → contains f N2 M  → contains f (app N1 N2) M -- M ⊑ app N1 N2
  Down  : ∀ {f} {M : Λ Y} {N : Λ (↑ X)} → contains f N M → contains (f ∘ i) (abs N) M -- M ⊑ abs N

I : ∀ {X} → Λ X
I = abs (var o)

-- o is in i
ContainsIO : ∀ {X} → contains i (I {X}) (var o)
ContainsIO = Down (Here {f = id})

ContainsIII : ∀ {X} → contains {X} id (app I I) I
ContainsIII {X} = Left Here I

-- extentionality of contains on f
-- ⊏-ext : ∀ {X Y} {f g : X → Y} {M : Λ X} {N : Λ Y} → f ≃ g → contains f M N → contains g M N
-- ⊏-ext {g = g} fg (Here {x = x}) = transp (λ z → contains g (var x) (var z)) (~ fg x) Here
-- ⊏-ext fg (Left c N2) = Left (⊏-ext fg c) N2
-- ⊏-ext fg (Right N1 c) = Right N1 (⊏-ext fg c)
-- -- ⊏-ext fg (Down c) = {!   !}


nat0⊏ : ∀ {X Y Z} (f : X → Y) (g : Y → Z) {M : Λ X} {N : Λ Y} → contains f M N → contains {X} {Z} (g ∘ f) M (Λ→ g N)
nat0⊏ {X} {Y} {Z} f g {M = M} Here = transp (λ z → contains (g ∘ f) M z) (Λ-func g f M) Here
nat0⊏ f g (Left c N2) = Left (nat0⊏ f g c) N2
nat0⊏ f g (Right N1 c) = Right N1 (nat0⊏ f g c)
nat0⊏ .(f ∘ i) g (Down {f} c) = Down (nat0⊏ f g c)
 
nat1⊏ : ∀ {X Y Z} (f : X → Y) (g : Y → Z) {M : Λ X} {N : Λ Y} {Q : Λ Z} → contains g (Λ→ f M) Q → contains (g ∘ f) M Q
nat1⊏ f g {var x} Here = Here
nat1⊏ f g {app M M₁} Here = transp ((λ z → contains (g ∘ f) (app M M₁) (app z (Λ→ g (Λ→ f M₁))))) (Λ-func g f M) w where w = transp ((λ q → contains (g ∘ f) (app M M₁) (app (Λ→ (g ∘ f) M) q))) (Λ-func g f M₁) Here
nat1⊏ {X} {Y} {Z} f g {app M M₁} {N} {Q} (Left c .(Λ→ f M₁)) = Left (nat1⊏ {X} {Y} {Z} f g {M} {N} {Q} c) M₁
nat1⊏ f g {app M M₁} {N} {Q} (Right .(Λ→ f M) c) = Right M (nat1⊏ f g {M₁} {N} {Q} c)
nat1⊏ f g {abs M} Here = transp (λ z → contains (g ∘ f) (abs M) (abs z)) (Λ-ext (↑-func g f) M ! Λ-func (↑→ g) (↑→ f) M) Here
nat1⊏ f g@.(f₁ ∘ i) {abs M} {N} {Q} (Down {f₁} c) = Down (nat1⊏ (↑→ f) f₁ {M} {Λ→i N} {Q} c)


trans⊏ : ∀ {X Y Z} {f : X → Y} {g : Y → Z} {M : Λ X} {N : Λ Y} {Q : Λ Z} →
          contains {X} {Y} f M N → contains {Y} {Z} g N Q → contains (g ∘ f) M Q
trans⊏ {X} {Y} {Z} {f = f} {g = g} {M} {N} {Q} Here c2 = nat1⊏ f g {M} {N} {Q} c2
trans⊏ (Left c1 N2) c2 = Left (trans⊏ c1 c2) N2
trans⊏ (Right N1 c1) c2 = Right N1 (trans⊏ c1 c2)
trans⊏ (Down c1) c2 = Down (trans⊏ c1 c2)

-- -- if M ≡ N them, if M contains Q, N contains Q
-- ≡⊏ : ∀ {X Y} {f : X → Y} {M N : Λ X} {Q : Λ Y} → M ≡ N → contains f M Q → contains f N Q
-- ≡⊏ refl c = c

var≡⊏ : ∀ {X Y} {x : X} {y : Y} {f : X → Y} → contains f (var x) (var y) → f x ≡ y
var≡⊏ Here = refl

asym⊏Lemma : ∀ {X} {M : Λ X} {N : Λ X} → contains id M N → contains id N M → M ≡ N  
asym⊏Lemma {X} {var x} {.(Λ→ id (var x))} Here Here = refl
asym⊏Lemma {X} {app M M₁} {.(Λ→ id (app M M₁))} Here c2 = app≡ {!   !} {!   !}
asym⊏Lemma {X} {app M M₁} {N} (Left c1 .M₁) c2 = {!   !}
asym⊏Lemma {X} {app M M₁} {N} (Right .M c1) c2 = {!   !}
asym⊏Lemma {X} {abs M} {app N N₁} c1 c2 = {!   !}
asym⊏Lemma {X} {abs M} {abs N} c1 c2 = {!   !}

asymX⊏ : ∀ {X} (M N : Λ X) (f : X → X) → contains f M N → contains f N M → M ≡ N
asymX⊏ (var x) (var x₁) f c1 c2 = {! trans⊏ c1 c2   !}
asymX⊏ (app M M₁) N f c1 c2 = {!   !}
asymX⊏ (abs M) N f c1 c2 = {!   !}    

asym⊏ : ∀ {X Y} {M : Λ X} {f : X → Y} {g : Y → X} {N : Λ Y} → contains f M N → contains g N M → (∀ x → x ∈ M → (g ∘ f) x ≡ x) 
asym⊏ {X} {Y} {var x} {f} {g} {var x₁} c1 c2 .x here = var≡⊏ (nat0⊏ f g c1) ! var≡⊏ c2
asym⊏ {X} {Y} {app M M₁} {f} {g} {N} c1 c2 = {!   !}
asym⊏ {X} {Y} {abs M} {f} {g} {app N N₁} c1 c2 y (down occ) = {!   !}
asym⊏ {X} {Y} {abs M} {f} {g} {abs N} c1 c2 y (down occ) = {! asym⊏  (i y) occ  !}


bind-rec : ∀ {X Y : Set} (A : Λ X) (f : X → Λ Y) {x : X}
             → x ∈ A → contains id (f x) (A [ f ]) → A ≡ var x
bind-rec (var x₁) f {.x₁} here c = refl
bind-rec (app A A₁) f {x} (left occ .A₁) c = {!   !}
bind-rec (app A A₁) f {x} (right .A occ) c = {!   !}
bind-rec (abs A) f {x} (down occ) c = {!  bind-rec A (lift f) occ  !}

-- ⊑→ : ∀ {X Y} {s t : Λ X} → s ⊑ t → (f : X → Y) → Λ→ f s ⊑ Λ→ f t
-- ⊑→ Here f = Here
-- ⊑→ (Left st N2) f = Left (⊑→ st f) (Λ→ f N2)
-- ⊑→ (Right N1 st) f = Right (Λ→ f N1) (⊑→ st f)
-- ⊑→ (Down st) f =
--   let rc = ⊑→ st (↑→ f)
--       eq = tran (symm (Λ-func i f)) (tran (λ z → refl ) (Λ-func (↑→ f) i))
--   in Down (eq _ ≡⊑ rc)

-- tran⊑ : ∀ {X} {r s t : Λ X} → r ⊑ s → s ⊑ t → r ⊑ t
-- tran⊑ rs Here = rs
-- tran⊑ rs (Left st N2) = Left (tran⊑ rs st) N2
-- tran⊑ rs (Right N1 st) = Right N1 (tran⊑ rs st)
-- tran⊑ rs (Down st) = Down (tran⊑ (⊑→ rs i) st )

-- ⊑inv : ∀ {X} (M : Λ X) (sub : M ⊑ M) → sub ≡ Here
-- ⊑inv (var x) Here = refl
-- ⊑inv (app M1 M2) Here = refl
-- ⊑inv (app M1 M2) (Left sub .M2) with Left {_} {M1} {M1} Here M2 | ⊑inv M1 (tran⊑ (Left Here M2) sub)
-- ... | p | q = {! tran⊑ (Left Here M2) sub   !}
-- ⊑inv (app M1 M2) (Right .M1 sub) = {!   !}
-- ⊑inv (abs M0)  sub = {!   !}

-- -- ⊑inv2 : ∀ {X} (M N : Λ X) (sub : M ⊑ N) → ¬ (sub ≡ Here) → ¬ (M ≡ N)
-- -- ⊑inv2 M N sub ne eq = ?

-- ¬app≡L : ∀ {X} (M N : Λ X) → ¬ (app M N ≡ M)
-- ¬app≡L M N ()

-- ¬app≡R : ∀ {X} (M N : Λ X) → ¬ (app M N ≡ N)
-- ¬app≡R M N ()

-- ¬absLemma : ∀ {X} (M : Λ (↑ X)) (f : X → ↑ X) → isInj f → Λ→ f (abs M) ≡ M → ∀ x → x ∉ M
-- ¬absLemma (abs M) f fi p x (down occ) with abs≡inv p
-- ... | q = ¬absLemma M (↑→ f) (↑→Inj f fi) q (i x) occ

-- ¬abs≡ : ∀ {X} (M : Λ (↑ X)) → ¬ (Λ→i (abs M) ≡ M)
-- ¬abs≡ (abs M) p with abs≡inv p
-- ... | q = ¬abs≡ M (abs≡ (map-occurs (↑→ i) (↑→ (↑→ i)) M eq) ! q)
--           where eq = (λ x xinM → exfalso (¬absLemma M (↑→ i) (↑→Inj i iInj ) q x xinM ) )

-- ¬abs⊑Lemma : ∀ {X} (M : Λ (↑ X)) (f : X → ↑ X) → isInj f → (Λ→i (abs M) ⊑ M) → ∀ x → x ∉ Λ→i (abs M)
-- ¬abs⊑Lemma M f fi sub x occ = {!   !}

-- ¬app⊑L : ∀ {X} (M N : Λ X) → ¬ (app M N ⊑ M)
-- ¬app⊑R : ∀ {X} (M N : Λ X) → ¬ (app M N ⊑ N)
-- ¬abs⊑ : ∀ {X} (M : Λ (↑ X)) → ¬ (Λ→i (abs M) ⊑ M)

-- ¬app⊑L (app M1 M2) N (Left sub .M2) = ¬app⊑L M1 M2 (tran⊑ (Left Here N) sub)
-- ¬app⊑L (app M1 M2) N (Right .M1 sub) = ¬app⊑R M1 M2 (tran⊑ (Left Here N ) sub )
-- ¬app⊑L (abs M0) N (Down sub) = ¬abs⊑ M0 (tran⊑ (Left Here (Λ→ i N) ) sub)

-- ¬app⊑R M (app N1 N2) (Left mn .N2) = ¬app⊑L N1 N2 (tran⊑ (Right M Here) mn )
-- ¬app⊑R M (app N1 N2) (Right .N1 mn) = ¬app⊑R N1 N2 (tran⊑ (Right M Here) mn )
-- ¬app⊑R M (abs N) (Down mn) = ¬abs⊑ N (tran⊑ (Right (Λ→ i M) Here) mn  )

-- abs⊑dec : ∀ {X} M (N : Λ (↑ X)) → M ⊑ abs N → M ≡ abs N ⊔ (Λ→i M ⊑ N)
-- abs⊑dec .(abs N) N Here = inl refl
-- abs⊑dec M N (Down mn) = inr mn

-- ¬abs⊑ = {!   !}
-- -- ¬abs⊑ (app M1 M2) (Left sub .M2) = ¬app⊑L M1 M2 (tran⊑ (Down {!   !} ) sub )
-- -- ¬abs⊑ (app M1 M2) (Left sub .M2) = ¬app⊑L M1 M2 (tran⊑ (Down Here ) {!   !} )
-- -- ¬abs⊑ (app M1 M2) (Right .M1 sub) = {!   !}
-- -- ¬abs⊑ (abs M) sub with abs⊑dec _ _ sub
-- -- ... | inl p = {! p   !}
-- -- ... | inr sub' = ¬abs⊑ M (tran⊑ (Down {!   !} ) sub' )

-- bind-rec : ∀ {X Y : Set} (A : Λ X) (f : X → Λ Y) {x : X}
--              → x ∈ A → (A [ f ]) ⊑ f x → A ≡ var x
-- bind-rec (var x) f here sub = refl
-- bind-rec (app A1 A2) f (left occ .A2) sub with bind-rec A1 f occ (tran⊑ (Left Here (bind f A2) ) sub)
-- bind-rec (app (var x) A2) f (left here .A2) sub | refl = {!   !}
-- bind-rec (app A1 A2) f (right .A1 occ) sub = {!   !}
-- bind-rec (abs A0) f occ sub = {!   !}

-- -- ¬app⊑L (app M1 M2) N (Left sub .M2) = ¬app⊑L M1 M2 (tran⊑ (Left Here N ) sub )
-- -- ¬app⊑L (app M1 M2) N (Right .M1 sub) = ¬app⊑R M1 M2 (tran⊑ (Left Here N ) sub )
-- -- ¬app⊑L (abs M0) N sub = {!   !}
-- --
-- -- ¬app⊑R M N sub = {!   !}
-- --
-- asym⊑ : ∀ {X} {s t : Λ X} → s ⊑ t → t ⊑ s → s ≡ t
-- asym⊑ {X} {.(var x)} {var x} Here ts = refl
-- asym⊑ {X} {.(app t1 t2)} {app t1 t2} Here ts = refl
-- -- asym⊑ {X} {s} {app t1 t2} (Left Here .t2) ts = {!   !} -- ~ asym⊑ ts (Left Here t2)
-- asym⊑ {X} {s} {app t1 t2} (Left st .t2)  ts with asym⊑ (tran⊑ ts st) (Left Here t2)
-- ... | ()
-- asym⊑ {X} {s} {app t1 t2} (Right .t1 st) ts with asym⊑ (tran⊑ ts st) (Right t1 Here)
-- ... | ()
-- asym⊑ {X} {.(abs t0)} {abs t0} Here ts = refl
-- asym⊑ {X} {s} {abs t0} (Down st) ts with asym⊑ (tran⊑ (⊑→ ts i) st) (Down {!    !} )
-- ... | p = exfalso (¬abs≡ t0 p)                         -- Need: o ∉ t0.  Not provable.
          