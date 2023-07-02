module Length where

open import Lambda

len : ∀ {X} → Λ X → Nat
len (var x) = O
len (app s t) = S (len s ++ len t)
len (abs r) = S (len r)

len→ : ∀ {X Y} (f : X → Y) (t : Λ X) → len (Λ→ f t) ≡ len t
len→ f (var x) = refl
len→ f (app t1 t2) = ext S ((len→ f t1) ≡+≡ (len→ f t2))
len→ f (abs t0) = ext S (len→ (↑→ f) t0)

len∈bind : ∀ {X Y} (f : X → Λ Y) t {x} → x ∈ t → len (f x) ≤ len (t [ f ])
len∈bind f (var x) here = ≤refl (len (f x))
len∈bind f (app s t) (left occ t) = ≤S (tran≤ (len∈bind f s occ) (++≤L (len (bind f s)) (len (bind f t)) ) )
len∈bind f (app s t) (right s occ) = ≤S (tran≤ (len∈bind f t occ) (++≤R (len (bind f s)) (len (bind f t)) ) )
len∈bind f (abs r) (down occ) = ≤S ((~ (len→ i (f _))) ≡≤ len∈bind (lift f) r occ)
 
len∉bind : ∀ {X} (M : Λ (↑ X)) (N : Λ X) (f : ↑ X → Λ X) x → ¬ (x ∈ M) → (∀ (z : ↑ X) → z ∈ M → (z ≡ x × f x ≡ N) ⊔ len (f z) ≡ O) → len (bind f M) ≡ len M
len∉bind (var x₁) N f x nocc fn = case (λ {(refl , e1) → exfalso (nocc here)}) id (fn x₁ here)
len∉bind (app M M₁) N f x nocc fn = ext S (tran++ (len∉bind M N f x (λ z → nocc (left z M₁)) (λ z z₁ → fn z (left z₁ M₁))) 
                                                  (len∉bind M₁ N f x (λ z → nocc (right M z)) (λ z z₁ → fn z (right M z₁))))
len∉bind (abs M) N f x nocc fn = ext S (len∉bind M (Λ→ i N) (lift f) (i x) (λ z → nocc (down z)) 
                    λ {(i x) → λ p → case (λ (q1 , q2) → inl (ext i q1 , ext Λ→i q2)) (λ q → inr (len→ i (f x) ! q)) (fn x (down p)); o → λ _ → inr refl})

len≡≠ : ∀ {X} (M N : Λ X) → M ≡ N → ¬ (len M ≡ len N) → ⊥
len≡≠ M .M refl p = p refl