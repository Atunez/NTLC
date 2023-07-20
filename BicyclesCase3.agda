module BicyclesCase3 where

open import Lambda public
open import Cycles public
open import Length public
open import Decidability public
open import Bicycles public

data Bool : Set where
  true : Bool
  false : Bool

isVarO : ∀ {X} (M : Λ (↑ X)) → Bool
isVarO (var o) = true
isVarO _ = false

containsI : ∀ {X} (M : Λ X) → Bool
containsI (var x) = false
containsI (app M M₁) with containsI M
... | true = true
... | false = containsI M₁
containsI (abs M) with isVarO M
... | true = true
... | false = containsI M

CCG : ∀ {X} (N1 N2 : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → bind f N2 ≡ abs (app N1 N2) → N2 ≡ var o
CCG N1 (var (i x)) f fn p with ~ fn x (transp (λ z → x ∈ z) (~ p) (down (right N1 here))) ! p
... | ()
CCG N1 (var o) f fn p = refl
CCG N1 (abs (var (i (i x)))) f fn p with abs≡inv p
... | M with fn x (occIni (f (i x)) (transp (λ z → (i x) ∈ z) (~ M) (right N1 (down here))))
... | t with ~ ext (Λ→i) t ! M
... | ()
CCG N1 (abs (var (i o))) f fn p with abs≡inv p
... | M = exfalso (o∉Λ→i (f o) (transp (λ z → o ∈ z) (~ M) (right N1 (down here))))
CCG N1 (abs (app N2 N3)) f fn p with app≡inv (abs≡inv p)
... | (p1 , p2) = 
  let rec = CCG N2 N3 (lift f) (λ {(i x) → λ q → ext (Λ→i) (fn x (occIni (f (i x)) q))
                                 ; o → λ q → exfalso (o∉Λ→i (f o) q)}) p2
  in ~ p2 ! ext (bind (lift f)) rec

CCG2 : ∀ {X} (N1 N2 N3 : Λ (↑ X)) (f : ↑ X → Λ X) → (∀ x → x ∈ f (i x) → f (i x) ≡ var x) → bind f N2 ≡ abs (app N1 (app N2 N3)) → N2 ≡ var o
CCG2 N1 (var (i x)) N3 f fn p with ~ fn x (transp (λ z → x ∈ z) (~ p) (down (right N1 (left here N3)))) ! p
... | ()
CCG2 N1 (var o) N3 f fn p = refl
CCG2 N1 (abs (var (i (i x)))) N3 f fn p with abs≡inv p
... | M with fn x (occIni (f (i x)) (transp (λ z → (i x) ∈ z) (~ M) (right N1 (left (down here) N3))))
... | t with ~ ext (Λ→i) t ! M
... | ()
CCG2 N1 (abs (var (i o))) N3 f fn p with abs≡inv p
... | M = exfalso (o∉Λ→i (f o) (transp (λ z → o ∈ z) (~ M) (right N1 (left (down here) N3))))
CCG2 N1 (abs (app N2 (var (i (i x))))) N3 f fn p with app≡inv (abs≡inv p)
... | p1 , p2 with ~ ext (Λ→i) (fn x (occIni (f (i x)) (transp (λ z → (i x) ∈ z) (~ p2) (left (down (right N2 here)) N3)))) ! p2
... | ()
CCG2 N1 (abs (app N2 (var (i o)))) N3 f fn p with app≡inv (abs≡inv p)
... | p1 , p2 = exfalso (o∉Λ→i (f o) (transp (λ z → o ∈ z) (~ p2) (left (down (right N2 here)) N3)))
CCG2 N1 (abs (app N2 (app N4 N5))) N3 f fn p with app≡inv (abs≡inv p)
... | p1 , p2 with app≡inv p2
... | p3 , p4 = 
   let rec = CCG2 N2 N4 N5 _ (λ {(i x) → λ q → ext (Λ→i) (fn x (occIni (f (i x)) q))
                                 ; o → λ q → exfalso (o∉Λ→i (f o) q)}) p3
   in ~ p3 ! ext (bind (lift f)) rec

AgdaCheck : ∀ {X} (N2 : Λ (↑ (↑ X))) → (bind (lift (io var (abs (app (abs (app (var o) N2)) (var o))))) N2) ≡ (var o) → N2 ≡ var o
AgdaCheck (var (i (i x))) ()
AgdaCheck (var (i o)) ()
AgdaCheck (var o) p = refl

case3 : ∀ {X} (N P : Λ (↑ X)) → dec X → N [ (P [ abs N ]ₒ) ]ₒ ≡ app (abs (app (var o) P)) (abs N) → pure (app (abs (app (var o) P)) (abs N)) → TwoCycleSolutions {X}
case3 (var o) (var (i x)) d () np
case3 (var o) (var o) d () np
case3 (var o) (app P1 P2) d e np with app≡inv e
... | (e1 , e2) with decΛ ((dec↑ d) o) P1
... | inl x with CCG2 (var o) P1 P2 _ (λ x _ → refl) e1
case3 (var o) (app .(var o) P2) d e np | () , e2 | inl x | refl
case3 (var o) (app P1 P2) d e np | e1 , e2 | inr x with occurs-map P1 _ _ e1 x
... | m with lercherEq3 P2 I e2
-- Not sure how to fill these either...
... | inl refl = inf (inf10 (app≡ (~ occurs-map P1 _ I e1 x) refl) m)
... | inr refl = inf (inf11 (app≡ (~ occurs-map P1 _ I e1 x) refl) m)
case3 (app N1 N2) P d e np with app≡inv e
case3 (app (var o) N2) P d e np | e1 , e2 with decΛ ((dec↑ d) o) P
... | inl yes with decTop P
case3 (app (var o) .(var o)) .(var o) d e np | refl , e2 | inl yes | inl refl = pure0 e
-- Should this map to a solution?
case3 (app (var o) N2) P d e np | e1 , e2 | inl yes | inr notVar = exfalso (notVar (CCG (var o) P _ (λ x _ → refl) e1))
case3 (app (var o) N2) P d e np | e1 , e2 | inr no with occurs-map P _ _ e1 no
... | m with CCG (var o) N2 _ (λ x _ → refl) e2
... | p with decΛ ((dec↑ d) o) N2
case3 (app (var o) .(var o)) P d e np | e1 , e2 | inr no | m | refl | inl x = exfalso (len≡≠ _ _ m λ q → ¬S< q (<-deq refl (<<S (len P)) (ext (S ∘ S) (~ len→ (↑→ i) P))))
... | inr x with occurs-map N2 _ _ e2 x
-- Not sure how to get this hole, but you should be able to get an infinite solution...
... | m2 = inf (inf13 (app≡ (~ occurs-map P _ _ e1 no) (~ occurs-map N2 _ _ e2 x)) m m2)
-- Can get exfalso, but how to get a cycle?
-- From the paper M = (\x.xP)N@(\y.(\z.zN1)N2) -> NP -> M = (\z.zN1[P/y])N2[P/y]
-- So, only a two cycle if: P = N1[P/y] and N2[P/y] = N. 
case3 (app (abs N1) N2) P d e np | e1 , e2 with CCG (abs N1) N2 _ (λ x _ → refl) e2
... | refl with abs≡inv e1
... | e3 with lercherEq3 P _ e2 
case3 (app (abs (var (i (i x)))) .(var o)) .(var o) d e np | e1 , e2 | refl | () | inl refl
case3 (app (abs (var (i o))) .(var o)) .(var o) d e np | e1 , e2 | refl | () | inl refl
case3 (app (abs (app (var (i (i x))) N2)) .(var o)) .(var o) d e np | e1 , e2 | refl | () | inl refl
case3 (app (abs (app (var (i o)) N2)) .(var o)) .(var o) d e np | e1 , e2 | refl | () | inl refl
case3 (app (abs (app (var o) N2)) .(var o)) .(var o) d e np | e1 , e2 | refl | e3 | inl refl with AgdaCheck N2 (_×_.snd (app≡inv e3))
... | refl = imp2 e
case3 (app (abs (var N1)) .(var o)) P d e np | e1 , e2 | refl | e3 | inr l with np (contr (app (abs (app (var o) P)) (abs ((var N1) [ var o ]ₒ) )) (appR→ (abs→ (redex (var N1) (var o))))) 
                                                                                   (contr ((app (var o) P) [ abs (app (abs (var N1)) (var o)) ]ₒ) (redex (app (var o) P) (abs (app (abs (var N1)) (var o)))))
... | ()
case3 (app (abs (app N1 N2)) .(var o)) P d e np | e1 , e2 | refl | e3 | inr l with np (contr (app (abs (app (var o) P)) (abs ((app N1 N2) [ var o ]ₒ) ))  (appR→ (abs→ (redex (app N1 N2) (var o)))))
                                                                                      (contr ((app (var o) P) [ abs (app (abs (app N1 N2)) (var o)) ]ₒ) (redex (app (var o) P) (abs (app (abs (app N1 N2)) (var o)))))
... | ()
