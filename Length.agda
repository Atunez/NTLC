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
 

 
len≡≠ : ∀ {X} (M N : Λ X) → M ≡ N → ¬ (len M ≡ len N) → ⊥
len≡≠ M .M refl p = p refl