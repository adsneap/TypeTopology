Andrew Sneap, 17 February 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Type
open import Dyadics.Order
open import Integers.Type
open import Integers.Multiplication
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Order
open import Integers.Parity
open import Naturals.Exponentiation
open import Notation.Order
open import UF.Base hiding (_≈_)
open import UF.Subsingletons

module Dyadics.Negation where

-_ : ℤ[1/2] → ℤ[1/2]
- ((z , n) , _) = normalise-pos (ℤ- z , n)

infix 31 -_

ℤ[1/2]-minus-zero : - 0ℤ[1/2] ＝ 0ℤ[1/2]
ℤ[1/2]-minus-zero = refl

minus-normalise-pos : (p : ℤ) (a : ℕ)
                    → - normalise-pos (p , a) ＝ normalise-pos (ℤ- p , a)
minus-normalise-pos p a = γ
 where
  p' = (pr₁ ∘ pr₁) (normalise-pos (p , a))
  a' = (pr₂ ∘ pr₁) (normalise-pos (p , a))
  α = pr₂ (normalise-pos (p , a))

  I : (p , a) ≈' (p' , a')
  I = ≈'-normalise-pos (p , a)

  II : (ℤ- p' , a') ≈' (ℤ- p , a)
  II = (ℤ- p') * pos (2^ a)  ＝⟨ negation-dist-over-mult' p' (pos (2^ a)) ⟩
        ℤ- p' * pos (2^ a)   ＝⟨ ap ℤ-_ (I ⁻¹) ⟩
        ℤ- p * pos (2^ a')   ＝⟨ negation-dist-over-mult' p (pos (2^ a')) ⁻¹ ⟩
        (ℤ- p) * pos (2^ a') ∎

  γ : - normalise-pos (p , a) ＝ normalise-pos (ℤ- p , a)
  γ = - normalise-pos (p , a)    ＝⟨ refl ⟩
      - ((p' , a') , α)          ＝⟨ refl ⟩
      normalise-pos (ℤ- p' , a') ＝⟨ ≈'-to-＝ (ℤ- p' , a') (ℤ- p , a) II ⟩
      normalise-pos (ℤ- p , a)   ∎

ℤ[1/2]-minus-minus : (p : ℤ[1/2]) → p ＝ - (- p)
ℤ[1/2]-minus-minus ((z , n) , α) = γ
 where
  I : (z , n) , α ≈ normalise-pos (z , n)
  I = ≈-normalise-pos ((z , n) , α)

  γ : (z , n) , α ＝ - (- ((z , n) , α))
  γ = (z , n) , α                   ＝⟨ i    ⟩
      normalise-pos (z , n)         ＝⟨ ii   ⟩
      normalise-pos (ℤ- (ℤ- z) , n) ＝⟨ iii  ⟩
      - normalise-pos (ℤ- z , n)    ＝⟨ refl ⟩
      - (- ((z , n) , α))           ∎
   where
    i   = ≈-to-＝ ((z , n) , α) (normalise-pos (z , n)) I
    ii  = ap (λ - → normalise-pos (- , n)) (minus-minus-is-plus z ⁻¹)
    iii = minus-normalise-pos (ℤ- z) n ⁻¹

ℤ[1/2]≤-swap : (p q : ℤ[1/2]) → p ≤ q → - q ≤ - p
ℤ[1/2]≤-swap ((p , a) , α) ((q , b) , β) l = γ
 where
  I : ℤ- (q * pos (2^ a)) ≤ ℤ- (p * pos (2^ b))
  I = ℤ≤-swap (p * pos (2^ b)) (q * pos (2^ a)) l

  II : ℤ- q * pos (2^ a) ＝ (ℤ- q) * pos (2^ a)
  II = negation-dist-over-mult' q (pos (2^ a)) ⁻¹

  III : ℤ- p * pos (2^ b) ＝ (ℤ- p) * pos (2^ b)
  III = negation-dist-over-mult' p (pos (2^ b)) ⁻¹

  IV : (ℤ- q) * pos (2^ a) ≤ (ℤ- p) * pos (2^ b)
  IV = transport₂ _≤_ II III I

  γ : normalise-pos (ℤ- q , b) ≤ normalise-pos (ℤ- p , a)
  γ = normalise-pos-≤ (ℤ- q , b) (ℤ- p , a) IV

ℤ[1/2]<-swap : (p q : ℤ[1/2]) → p < q → - q < - p
ℤ[1/2]<-swap p q l = γ (ℤ[1/2]≤-split (- q) (- p) I)
 where
  l' : p ≤ q
  l' = ℤ[1/2]<-coarser-than-≤ p q l

  I : (- q) ≤ (- p)
  I = ℤ[1/2]≤-swap p q l'
  
  γ : (- q) < (- p) ∔ ((- q) ＝ (- p)) → - q < - p
  γ (inl l) = l
  γ (inr e) = 𝟘-elim (ℤ[1/2]<-not-itself p III)
   where
    II : q ＝ p
    II = q       ＝⟨ ℤ[1/2]-minus-minus q    ⟩
         - (- q) ＝⟨ ap -_ e                 ⟩
         - (- p) ＝⟨ ℤ[1/2]-minus-minus p ⁻¹ ⟩
         p       ∎
         
    III : p < p
    III = transport (p <_) II l

ℤ≤-swap' : (p q : ℤ[1/2]) → - p ≤ - q → q ≤ p
ℤ≤-swap' p q l = γ
 where
  I : - (- q) ≤ - (- p)
  I = ℤ[1/2]≤-swap (- p) (- q) l

  II : - (- q) ＝ q
  II = ℤ[1/2]-minus-minus q ⁻¹

  III : - (- p) ＝ p
  III = ℤ[1/2]-minus-minus p ⁻¹

  γ : q ≤ p
  γ = transport₂ _≤_ II III I

\end{code}
