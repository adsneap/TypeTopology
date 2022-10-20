
```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
open import Integers.Integers
open import Integers.Addition renaming (_+_ to _ℤ+_;  _-_ to _ℤ-_)
open import Integers.Negation renaming (-_ to ℤ-_ )
open import Integers.Order
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Quotient
open import UF.Powerset hiding (𝕋)

module Todd.Approximations
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
 where

open import Todd.RationalsDyadic fe renaming (1/2ℤ[1/2] to 1/2)
open import Todd.DyadicReals pe pt fe
open import Todd.TBRFunctions pt fe pe sq
open import Todd.TernaryBoehmReals pt fe pe sq hiding (ι ; _≤_≤_)
open import Todd.TBRDyadicReals pt fe pe sq
open PropositionalTruncation pt

open OrderProperties DyOrPr
open DyadicProperties Dp renaming (_ℤ[1/2]+_ to _+_ ; ℤ[1/2]-_ to -_ ; _ℤ[1/2]-_ to _-_ ; _ℤ[1/2]*_ to _*_)
                                    
open import Naturals.Order renaming (max to ℕmax) hiding (≤-refl ; ≤-trans)

𝔻 = ℤ[1/2]

is-odcs : (ℤ → ℤ[1/2] × ℤ[1/2]) → 𝓤₀  ̇  
is-odcs ζ = ((n : ℤ) → pr₁ (ζ n) ≤ℤ[1/2] pr₂ (ζ n))
          × ((ϵ : 𝔻) → Σ n ꞉ ℤ , ((pr₂ (ζ n) - pr₁ (ζ n)) ≤ℤ[1/2] ϵ))
          × ((n : ℤ) → (pr₁ (ζ n) ≤ℤ[1/2] pr₁ (ζ (succℤ n)))
                     × (pr₂ (ζ (succℤ n)) ≤ℤ[1/2] pr₂ (ζ n)))

is-odcs-c₃-lemma-ns : (ζ : (ℤ → ℤ[1/2] × ℤ[1/2])) → ((c₁ , c₂ , c₃) : is-odcs ζ)
                    → (n₁ n₂ : ℤ) → (k : ℕ) → n₁ ℤ+ pos k ＝ n₂ → (pr₁ (ζ n₁) ≤ℤ[1/2] pr₁ (ζ n₂)) × (pr₂ (ζ n₂) ≤ℤ[1/2] pr₂ (ζ n₁))
is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ n₂ 0        e = transport (λ - → pr₁ (ζ n₁) ≤ pr₁ (ζ -)) e (≤-refl (pr₁ (ζ n₁)))
                                                      , transport (λ - → pr₂ (ζ -) ≤ pr₂ (ζ n₁)) e (≤-refl (pr₂ (ζ n₁)))
is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ n₂ 1 e = transport (λ - → pr₁ (ζ n₁) ≤ pr₁ (ζ -)) e (pr₁ (c₃ n₁))
                                               , transport (λ - → pr₂ (ζ -) ≤ pr₂ (ζ n₁)) e (pr₂ (c₃ n₁)) 
is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ n₂ (succ (succ k)) e with (is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ (predℤ n₂) (succ k) (predsuccℤ (succℤ (n₁ +pos k)) ⁻¹ ∙ ap predℤ e))
... | (l₁ , l₂) = trans' (pr₁ (ζ n₁)) (pr₁ (ζ (predℤ n₂))) (pr₁ (ζ n₂)) l₁ (transport (λ - → pr₁ (ζ (predℤ n₂)) ≤ℤ[1/2] pr₁ (ζ -)) (succpredℤ n₂) (pr₁ (c₃ (predℤ n₂))))
                , trans' (pr₂ (ζ n₂)) (pr₂ (ζ (predℤ n₂))) (pr₂ (ζ n₁)) (transport (λ - → pr₂ (ζ -) ≤ℤ[1/2] pr₂ (ζ (predℤ n₂))) (succpredℤ n₂) (pr₂ (c₃ (predℤ n₂)))) l₂

is-odcs-c₃-lemma : (ζ : (ℤ → ℤ[1/2] × ℤ[1/2])) → ((c₁ , c₂ , c₃) : is-odcs ζ)
                 → (n₁ n₂ : ℤ) → n₁ ≤ n₂ → (pr₁ (ζ n₁) ≤ℤ[1/2] pr₁ (ζ n₂)) × (pr₂ (ζ n₂) ≤ℤ[1/2] pr₂ (ζ n₁))
is-odcs-c₃-lemma ζ c n₁ n₂ (k , e) = is-odcs-c₃-lemma-ns ζ c n₁ n₂ k e

postulate
 ℤ[1/2]-ordering-property : (a b c d : ℤ[1/2]) → (a - b) < (c - d) → (a < c) ∔ (d < b)
 
⦅_⦆ : Σ is-odcs → ℝ-d
⦅ ζ , (c₁ , c₂ , c₃) ⦆
 = (L , R)
 , inhabited-l , inhabited-r
 , rounded-l   , rounded-r
 , is-disjoint , is-located
 where
  L R : 𝓟 ℤ[1/2]
  L p = (∃ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n))) , ∃-is-prop
  R q = (∃ n ꞉ ℤ , (pr₂ (ζ n) <ℤ[1/2] q)) , ∃-is-prop
  inhabited-l : inhabited-left L
  inhabited-l = ∣ (pr₁ (ζ (pos 0)) - 1ℤ[1/2])
              , ∣ pos 0 , ℤ[1/2]<-neg (pr₁ (ζ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  inhabited-r : inhabited-right R
  inhabited-r = ∣ (pr₂ (ζ (pos 0)) + 1ℤ[1/2])
             , ∣ pos 0  , ℤ[1/2]<-+ (pr₂ (ζ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  rounded-l : rounded-left L
  rounded-l p = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n)) → ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n')))
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n)) → Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n')))
      I (n , p<ζn) = let (p' , p<p' , p'<ζn) = dense p (pr₁ (ζ n)) p<ζn
                     in p' , (p<p' , ∣ n , p'<ζn ∣)
    rtl : ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n)))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n))
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n)))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n))
      I (p' , p<p' , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n)) → Σ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n))
        II (n  , p'<ζn) = n , (trans p p' (pr₁ (ζ n)) p<p' p'<ζn)
      
  rounded-r : rounded-right R
  rounded-r q = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , pr₂ (ζ n) < q → ∃ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , pr₂ (ζ n) < q → Σ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
      I (n , ζn<q) = let (q' , ζn<q' , q'<q) = dense (pr₂ (ζ n)) q ζn<q
                     in q' , (q'<q , ∣ n , ζn<q' ∣)
    rtl : ∃ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
      I (q' , q'<q , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (pr₂ (ζ n) < q') → Σ n ꞉ ℤ , (pr₂ (ζ n) <ℤ[1/2] q)
        II (n , ζ<q') = n , (trans (pr₂ (ζ n)) q' q ζ<q' q'<q)
  
  is-disjoint : disjoint L R
  is-disjoint p q (tp<x , tx<q) = ∥∥-rec (<ℤ[1/2]-is-prop p q) I (binary-choice tp<x tx<q)
   where
    I : (Σ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n))) × (Σ n' ꞉ ℤ , (pr₂ (ζ n') <ℤ[1/2] q))
      → p <ℤ[1/2] q
    I ((n , p<l) , (n' , r<q)) with ℤ-dichotomous n n'
    ... | inl n≤n' = let p<l' = ℤ[1/2]<-≤ p (pr₁ (ζ n)) (pr₁ (ζ n')) p<l (pr₁ (is-odcs-c₃-lemma ζ (c₁ , c₂ , c₃) n n' n≤n'))
                         l<q' = ℤ[1/2]≤-< (pr₁ (ζ n')) (pr₂ (ζ n')) q (c₁ n') r<q
                     in trans p (pr₁ (ζ n')) q p<l' l<q'
    ... | inr n'≤n = let p<r' = ℤ[1/2]<-≤ p (pr₁ (ζ n)) (pr₂ (ζ n)) p<l (c₁ n)
                         r<q' = ℤ[1/2]≤-< (pr₂ (ζ n)) (pr₂ (ζ n')) q (pr₂ (is-odcs-c₃-lemma ζ (c₁ , c₂ , c₃) n' n n'≤n)) r<q
                     in trans p (pr₂ (ζ n)) q p<r' r<q'
 
  is-located : located L R
  is-located p q p<q = I (c₂ (1/2 * (q - p)))
   where
    0<ε : 0ℤ[1/2] < (1/2 * (q - p))
    0<ε = <-pos-mult' 1/2 (q - p) 0<1/2ℤ[1/2] (diff-positive p q p<q)
    I : (Σ n ꞉ ℤ , ((pr₂ (ζ n) - pr₁ (ζ n)) ≤ℤ[1/2] (1/2 * (q - p)))) → (L p holds) ∨ (R q holds)
    I (n , l₁) = II (ℤ[1/2]-ordering-property (pr₂ (ζ n)) (pr₁ (ζ n)) q p l₂)
     where
      l₂ :(pr₂ (ζ n) - pr₁ (ζ n)) < (q - p)
      l₂ = ℤ[1/2]≤-< (pr₂ (ζ n) - pr₁ (ζ n)) (1/2 * (q - p)) (q - p) l₁ (ℤ[1/2]-1/2-< (q - p) (diff-positive p q p<q))
      II : pr₂ (ζ n) < q ∔ p < pr₁ (ζ n) → (L p holds) ∨ (R q holds)
      II (inl ζ<q) = ∣ inr ∣ n , ζ<q ∣ ∣
      II (inr p<ζ) = ∣ inl ∣ n , p<ζ ∣ ∣

η η⁺² : ℤ × ℤ → ℤ[1/2]
η   = normalise
η⁺² (k , p) = normalise (k +pos 2 , p)

η[_,_] : ℤ → ℤ → ℤ[1/2] × ℤ[1/2]
η[ k , p ] = η (k , p) , η⁺² (k , p)

```
