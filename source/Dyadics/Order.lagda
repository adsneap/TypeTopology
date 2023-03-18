Andrew Sneap, 17 February 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Exponentiation
open import Dyadics.Type
open import Integers.Type
open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Integers.Exponentiation
open import Integers.Multiplication
open import Integers.Order
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Notation.Order
open import UF.Base
open import UF.Subsingletons

module Dyadics.Order where

_ℤ[1/2]<'_ _ℤ[1/2]≤'_ : ℤ × ℕ → ℤ × ℕ → 𝓤₀ ̇
(x , m) ℤ[1/2]<' (y , n) = x * pos (2^ n) < y * pos (2^ m)
(x , m) ℤ[1/2]≤' (y , n) = x * pos (2^ n) ≤ y * pos (2^ m)

_ℤ[1/2]<_ _ℤ[1/2]≤_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇
(p , _) ℤ[1/2]< (q , _) = p ℤ[1/2]<' q
(p , _) ℤ[1/2]≤ (q , _) = p ℤ[1/2]≤' q

instance
 Order-ℤ[1/2]-ℤ[1/2] : Order ℤ[1/2] ℤ[1/2]
 _≤_ {{Order-ℤ[1/2]-ℤ[1/2]}} = _ℤ[1/2]≤_

 Strict-Order-ℤ[1/2]-ℤ[1/2] : Strict-Order ℤ[1/2] ℤ[1/2]
 _<_ {{Strict-Order-ℤ[1/2]-ℤ[1/2]}} = _ℤ[1/2]<_

 Order-ℤℕ-ℤℕ : Order (ℤ × ℕ) (ℤ × ℕ)
 _≤_ {{Order-ℤℕ-ℤℕ}} = _ℤ[1/2]≤'_

 Strict-Order-ℤℕ-ℤℕ : Strict-Order (ℤ × ℕ) (ℤ × ℕ)
 _<_ {{Strict-Order-ℤℕ-ℤℕ}} = _ℤ[1/2]<'_

ℤ[1/2]<'-is-prop : (p q : ℤ × ℕ) → is-prop (p < q)
ℤ[1/2]<'-is-prop (p , a) (q , b) = γ
 where
  γ : is-prop (p * pos (2^ b) < q * pos (2^ a))
  γ = ℤ<-is-prop (p * pos (2^ b)) (q * pos (2^ a))

ℤ[1/2]<-is-prop : (p q : ℤ[1/2]) → is-prop (p < q)
ℤ[1/2]<-is-prop (p , _) (q , _) = ℤ[1/2]<'-is-prop p q

ℤ[1/2]≤'-is-prop : (p q : ℤ × ℕ) → is-prop (p ≤ q)
ℤ[1/2]≤'-is-prop (p , a) (q , b) = γ
 where
  γ : is-prop ((p , a) ≤ (q , b))
  γ = ℤ≤-is-prop (p * pos (2^ b)) (q * pos (2^ a))

ℤ[1/2]≤-is-prop : (p q : ℤ[1/2]) → is-prop (p ≤ q)
ℤ[1/2]≤-is-prop (p , _) (q , _) = ℤ[1/2]≤'-is-prop p q

\end{code}

Transivity of order proof:

Since (x , a) ≤  (y , b) ≤ (z , c), we have that

1) x * pos (2^ b) < y * pos (2^ a)
2) y * pos (2^ c) < z * pos (2^ b)

Multiplication of 1) by pos (2^ c)
                  2) by pos (2^ a)

gives that x * pos (2^ b) * pos (2^ c)
            ≤ y * pos (2^ a) * pos (2^ c)
             ≤ z * pos (2^ b) * pos (2^ a).

It follows by transitivity of integer order and multiplicative
cancellation that x * pos (2^ c) ≤ z * pos (2^ a).

\begin{code}

ℤ[1/2]<-trans : (x y z : ℤ[1/2]) → x < y → y < z → x < z
ℤ[1/2]<-trans ((x , a) , _) ((y , b) , _) ((z , c) , _) l₁ l₂ = γ
 where
  I : x * pos (2^ b) * pos (2^ c) < y * pos (2^ a) * pos (2^ c)
  I = positive-multiplication-preserves-order
      (x * pos (2^ b))
       (y * pos (2^ a))
        (pos (2^ c))
         (exponents-of-two-positive c) l₁

  II : y * pos (2^ c) * pos (2^ a) < z * pos (2^ b) * pos (2^ a)
  II = positive-multiplication-preserves-order
       (y * pos (2^ c))
        (z * pos (2^ b))
         (pos (2^ a))
          (exponents-of-two-positive a) l₂

  III : x * pos (2^ b) * pos (2^ c) ＝ x * pos (2^ c) * pos (2^ b)
  III = ℤ-mult-rearrangement x (pos (2^ b)) (pos (2^ c))

  IV : z * pos (2^ b) * pos (2^ a) ＝ z * pos (2^ a) * pos (2^ b)
  IV = ℤ-mult-rearrangement z (pos (2^ b)) (pos (2^ a))

  V : y * pos (2^ a) * pos (2^ c) ＝ y * pos (2^ c) * pos (2^ a)
  V = ℤ-mult-rearrangement y (pos (2^ a)) (pos (2^ c))

  VI : y * pos (2^ a) * pos (2^ c) < z * pos (2^ a) * pos (2^ b)
  VI = transport₂ _<_ (V ⁻¹) IV II

  VII : x * pos (2^ c) * pos (2^ b) < y * pos (2^ a) * pos (2^ c)
  VII = transport (_<  y * pos (2^ a) * pos (2^ c)) III I
  
  VIII : x * pos (2^ c) * pos (2^ b) < z * pos (2^ a) * pos (2^ b)
  VIII = ℤ<-trans
          (x * pos (2^ c) * pos (2^ b))
           (y * pos (2^ a) * pos (2^ c))
            (z * pos (2^ a) * pos (2^ b))
             VII VI
  
  γ : x * pos (2^ c) < z * pos (2^ a)
  γ = ordering-right-cancellable
       (x * pos (2^ c))
        (z * pos (2^ a))
         (pos (2^ b))
          (exponents-of-two-positive b)
           VIII

ℤ[1/2]≤-trans : (x y z : ℤ[1/2]) → x ≤ y → y ≤ z → x ≤ z
ℤ[1/2]≤-trans ((x , a) , _) ((y , b) , _) ((z , c) , _) l₁ l₂ = γ
 where
  I : x * pos (2^ b) * pos (2^ c) ≤ y * pos (2^ a) * pos (2^ c)
  I = positive-multiplication-preserves-order'
      (x * pos (2^ b))
       (y * pos (2^ a))
        (pos (2^ c))
         (exponents-of-two-positive c) l₁

  II : y * pos (2^ c) * pos (2^ a) ≤ z * pos (2^ b) * pos (2^ a)
  II = positive-multiplication-preserves-order'
       (y * pos (2^ c))
        (z * pos (2^ b))
         (pos (2^ a))
          (exponents-of-two-positive a) l₂

  III : x * pos (2^ b) * pos (2^ c) ＝ x * pos (2^ c) * pos (2^ b)
  III = ℤ-mult-rearrangement x (pos (2^ b)) (pos (2^ c))

  IV : z * pos (2^ b) * pos (2^ a) ＝ z * pos (2^ a) * pos (2^ b)
  IV = ℤ-mult-rearrangement z (pos (2^ b)) (pos (2^ a))

  V : y * pos (2^ a) * pos (2^ c) ＝ y * pos (2^ c) * pos (2^ a)
  V = ℤ-mult-rearrangement y (pos (2^ a)) (pos (2^ c))

  VI : y * pos (2^ a) * pos (2^ c) ≤ z * pos (2^ a) * pos (2^ b)
  VI = transport₂ _≤_ (V ⁻¹) IV II

  VII : x * pos (2^ c) * pos (2^ b) ≤ y * pos (2^ a) * pos (2^ c)
  VII = transport (_≤  y * pos (2^ a) * pos (2^ c)) III I
  
  VIII : x * pos (2^ c) * pos (2^ b) ≤ z * pos (2^ a) * pos (2^ b)
  VIII = ℤ≤-trans
          (x * pos (2^ c) * pos (2^ b))
           (y * pos (2^ a) * pos (2^ c))
            (z * pos (2^ a) * pos (2^ b))
             VII VI
  
  γ : x * pos (2^ c) ≤ z * pos (2^ a)
  γ = ℤ≤-ordering-right-cancellable
      (x * pos (2^ c))
       (z * pos (2^ a))
        (pos (2^ b))
         (exponents-of-two-positive b) VIII

\end{code}

Simple properties of dyadic order follow by reducing to properts of integers
order. For example, a proof of strict order gives a proof of inclusive order.

\begin{code}

ℤ[1/2]≤-refl : (p : ℤ[1/2]) → p ≤ p
ℤ[1/2]≤-refl ((z , a) , α)  = ℤ≤-refl (z * pos (2^ a))

ℤ[1/2]<-coarser-than-≤ : (p q : ℤ[1/2]) → p < q → p ≤ q
ℤ[1/2]<-coarser-than-≤ ((p , a) , _) ((q , b) , _) l = γ 
 where
  l' : p * pos (2^ b) < q * pos (2^ a)
  l' = l

  γ : p * pos (2^ b) ≤ q * pos (2^ a)
  γ = <-is-≤ _ _ l

ℤ[1/2]≤-split : (p q : ℤ[1/2]) → p ≤ q → (p < q) ∔ (p ＝ q)
ℤ[1/2]≤-split p q (0 , e) = inr (≈-to-＝ p q e)
ℤ[1/2]≤-split ((p , a) , α) ((q , b) , β) (succ n , e) = inl (n , γ)
 where
  γ : succℤ (p * pos (2^ b)) ℤ+ pos n ＝ q * pos (2^ a)
  γ = succℤ (p * pos (2^ b)) ℤ+ pos n ＝⟨ ℤ-left-succ (p * pos (2^ b)) (pos n) ⟩
      p * pos (2^ b) ℤ+ pos (succ n)  ＝⟨ e                                    ⟩
      q * pos (2^ a)                  ∎

normalise-pos-< : (p q : ℤ × ℕ)
                → p < q
                → normalise-pos p < normalise-pos q
normalise-pos-< (p , a) (q , b) l = I (normalise-pos-info' p a)
                                      (normalise-pos-info' q b)
 where
  p' = dnum (normalise-pos (p , a))
  a' = dden (normalise-pos (p , a))
  q' = dnum (normalise-pos (q , b))
  b' = dden (normalise-pos (q , b))
  
  I : Σ k ꞉ ℕ , (p ＝ p' * pos (2^ k))
              × (a ＝ a' ℕ+ k)
    → Σ k' ꞉ ℕ , (q ＝ q' * pos (2^ k'))
               × (b ＝ b' ℕ+ k')
    → normalise-pos (p , a) < normalise-pos (q , b)
  I (k , e₁ , e₂) (k' , e₃ , e₄) = γ
   where
    pk  = pos (2^ k)
    pk' = pos (2^ k')
    pa  = pos (2^ a)
    pb  = pos (2^ b)
    pa' = pos (2^ a')
    pb' = pos (2^ b')

    positive-result : is-pos-succ (pk * pk')
    positive-result = is-pos-succ-mult
                       pk pk'
                       (exponents-of-two-positive k)
                       (exponents-of-two-positive k')

    II : p * pb ＝ p' * pb' * (pk * pk')
    II = p * pb                         ＝⟨ i    ⟩
         p' * pk * pb                   ＝⟨ ii   ⟩
         p' * pk * pos (2^ (b' ℕ+ k'))  ＝⟨ iii  ⟩
         p' * pk * pos (2^ b' ℕ* 2^ k') ＝⟨ iv   ⟩
         p' * pk * (pb' * pk')          ＝⟨ v    ⟩
         p' * (pk * (pb' * pk'))        ＝⟨ vi   ⟩
         p' * (pk * pb' * pk')          ＝⟨ vii  ⟩
         p' * (pb' * pk * pk')          ＝⟨ viii ⟩
         p' * (pb' * (pk * pk'))        ＝⟨ ix   ⟩
         p' * pb' * (pk * pk')          ∎
     where
      ivᵢ : pos (2^ b' ℕ* 2^ k') ＝ pb' * pk'
      ivᵢ = pos-multiplication-equiv-to-ℕ (2^ b') (2^ k') ⁻¹
      
      i    = ap (_* pb) e₁
      ii   = ap (λ - → p' * pk * pos (2^ -)) e₄
      iii  = ap (λ - → p' * pk * pos -) (prod-of-powers 2 b' k' ⁻¹)
      iv   = ap (λ - → p' * pk * -) ivᵢ
      v    = ℤ*-assoc p' pk (pb' * pk')
      vi   = ap (p' *_) (ℤ*-assoc pk pb' pk') ⁻¹
      vii  = ap (λ - → p' * (- * pk')) (ℤ*-comm pk pb')
      viii = ap (p' *_) (ℤ*-assoc pb' pk pk')
      ix   = ℤ*-assoc p' pb' (pk * pk') ⁻¹

    III : q * pa ＝ q' * pa' * (pk * pk')
    III = q * pa                         ＝⟨ i    ⟩
          q' * pk' * pa                  ＝⟨ ii   ⟩
          q' * pk' * pos (2^ (a' ℕ+ k))  ＝⟨ iii  ⟩
          q' * pk' * pos (2^ a' ℕ* 2^ k) ＝⟨ iv   ⟩
          q' * pk' * (pa' * pk)          ＝⟨ v    ⟩
          q' * (pk' * (pa' * pk))        ＝⟨ vi   ⟩
          q' * (pk' * pa' * pk)          ＝⟨ vii  ⟩
          q' * (pa' * pk' * pk)          ＝⟨ viii ⟩
          q' * (pa' * (pk' * pk))        ＝⟨ ix   ⟩
          q' * pa' * (pk' * pk)          ＝⟨ x    ⟩           
          q' * pa' * (pk * pk')          ∎
     where
      ivᵢ : pos (2^ a' ℕ* 2^ k) ＝ pos (2^ a') * pos (2^ k)
      ivᵢ = pos-multiplication-equiv-to-ℕ (2^ a') (2^ k) ⁻¹
      
      i    = ap (_* pa) e₃
      ii   = ap (λ - → q' * pk' * pos (2^ -)) e₂
      iii  = ap (λ - → q' * pk' * pos -) (prod-of-powers 2 a' k ⁻¹)
      iv   = ap (λ - → q' * pk' * -) ivᵢ
      v    = ℤ*-assoc q' pk' (pa' * pk)
      vi   = ap (q' *_) (ℤ*-assoc pk' pa' pk ⁻¹)
      vii  = ap (λ - → q' * (- * pk)) (ℤ*-comm pk' pa')
      viii = ap (q' *_) (ℤ*-assoc pa' pk' pk)
      ix   = ℤ*-assoc q' pa' (pk' * pk) ⁻¹
      x    = ap (λ - → q' * pa' * -) (ℤ*-comm pk' pk)

    IV : p' * pb' * (pk * pk')
       < q' * pa' * (pk * pk')
    IV = transport₂ _<_ II III l
    
    γ : p' * pb' < q' * pa'
    γ = ordering-right-cancellable
         (p' * pb')
         (q' * pa')
         (pk * pk')
         positive-result
         IV

normalise-pos-≤ : (p q : ℤ × ℕ)
                → p ≤ q
                → normalise-pos p ≤ normalise-pos q
normalise-pos-≤ (p , a) (q , b) l = I (normalise-pos-info' p a)
                                      (normalise-pos-info' q b)
 where
  p' = dnum (normalise-pos (p , a))
  a' = dden (normalise-pos (p , a))
  q' = dnum (normalise-pos (q , b))
  b' = dden (normalise-pos (q , b))
  
  I : Σ k ꞉ ℕ , (p ＝ p' * pos (2^ k))
              × (a ＝ a' ℕ+ k)
    → Σ k' ꞉ ℕ , (q ＝ q' * pos (2^ k'))
               × (b ＝ b' ℕ+ k')
    → normalise-pos (p , a) ≤ normalise-pos (q , b)
  I (k , e₁ , e₂) (k' , e₃ , e₄) = γ
   where
    pk  = pos (2^ k)
    pk' = pos (2^ k')
    pa  = pos (2^ a)
    pb  = pos (2^ b)
    pa' = pos (2^ a')
    pb' = pos (2^ b')

    positive-result : is-pos-succ (pk * pk')
    positive-result = is-pos-succ-mult
                       pk pk'
                       (exponents-of-two-positive k)
                       (exponents-of-two-positive k')

    II : p * pb ＝ p' * pb' * (pk * pk')
    II = p * pb                         ＝⟨ i    ⟩
         p' * pk * pb                   ＝⟨ ii   ⟩
         p' * pk * pos (2^ (b' ℕ+ k'))  ＝⟨ iii  ⟩
         p' * pk * pos (2^ b' ℕ* 2^ k') ＝⟨ iv   ⟩
         p' * pk * (pb' * pk')          ＝⟨ v    ⟩
         p' * (pk * (pb' * pk'))        ＝⟨ vi   ⟩
         p' * (pk * pb' * pk')          ＝⟨ vii  ⟩
         p' * (pb' * pk * pk')          ＝⟨ viii ⟩
         p' * (pb' * (pk * pk'))        ＝⟨ ix   ⟩
         p' * pb' * (pk * pk')          ∎
     where
      ivᵢ : pos (2^ b' ℕ* 2^ k') ＝ pb' * pk'
      ivᵢ = pos-multiplication-equiv-to-ℕ (2^ b') (2^ k') ⁻¹
      
      i    = ap (_* pb) e₁
      ii   = ap (λ - → p' * pk * pos (2^ -)) e₄
      iii  = ap (λ - → p' * pk * pos -) (prod-of-powers 2 b' k' ⁻¹)
      iv   = ap (λ - → p' * pk * -) ivᵢ
      v    = ℤ*-assoc p' pk (pb' * pk')
      vi   = ap (p' *_) (ℤ*-assoc pk pb' pk') ⁻¹
      vii  = ap (λ - → p' * (- * pk')) (ℤ*-comm pk pb')
      viii = ap (p' *_) (ℤ*-assoc pb' pk pk')
      ix   = ℤ*-assoc p' pb' (pk * pk') ⁻¹

    III : q * pa ＝ q' * pa' * (pk * pk')
    III = q * pa                         ＝⟨ i    ⟩
          q' * pk' * pa                  ＝⟨ ii   ⟩
          q' * pk' * pos (2^ (a' ℕ+ k))  ＝⟨ iii  ⟩
          q' * pk' * pos (2^ a' ℕ* 2^ k) ＝⟨ iv   ⟩
          q' * pk' * (pa' * pk)          ＝⟨ v    ⟩
          q' * (pk' * (pa' * pk))        ＝⟨ vi   ⟩
          q' * (pk' * pa' * pk)          ＝⟨ vii  ⟩
          q' * (pa' * pk' * pk)          ＝⟨ viii ⟩
          q' * (pa' * (pk' * pk))        ＝⟨ ix   ⟩
          q' * pa' * (pk' * pk)          ＝⟨ x    ⟩           
          q' * pa' * (pk * pk')          ∎
     where
      ivᵢ : pos (2^ a' ℕ* 2^ k) ＝ pos (2^ a') * pos (2^ k)
      ivᵢ = pos-multiplication-equiv-to-ℕ (2^ a') (2^ k) ⁻¹
      
      i    = ap (_* pa) e₃
      ii   = ap (λ - → q' * pk' * pos (2^ -)) e₂
      iii  = ap (λ - → q' * pk' * pos -) (prod-of-powers 2 a' k ⁻¹)
      iv   = ap (λ - → q' * pk' * -) ivᵢ
      v    = ℤ*-assoc q' pk' (pa' * pk)
      vi   = ap (q' *_) (ℤ*-assoc pk' pa' pk ⁻¹)
      vii  = ap (λ - → q' * (- * pk)) (ℤ*-comm pk' pa')
      viii = ap (q' *_) (ℤ*-assoc pa' pk' pk)
      ix   = ℤ*-assoc q' pa' (pk' * pk) ⁻¹
      x    = ap (λ - → q' * pa' * -) (ℤ*-comm pk' pk)

    IV : p' * pb' * (pk * pk')
       ≤ q' * pa' * (pk * pk')
    IV = transport₂ _≤_ II III l
    
    γ : p' * pb' ≤ q' * pa'
    γ = ℤ≤-ordering-right-cancellable
         (p' * pb')
         (q' * pa')
         (pk * pk')
         positive-result
         IV

ℤ[1/2]<-not-itself : (p : ℤ[1/2]) → ¬ (p < p)
ℤ[1/2]<-not-itself ((p , a) , _) = ℤ-equal-not-less-than (p * pos (2^ a))

ℤ[1/2]<-≤ : (p q r : ℤ[1/2]) → p < q → q ≤ r → p < r
ℤ[1/2]<-≤ p q r l₁ l₂ = γ (ℤ[1/2]≤-split q r l₂) 
 where
  γ : q < r ∔ (q ＝ r) → p < r
  γ (inl l₃) = ℤ[1/2]<-trans p q r l₁ l₃
  γ (inr e)  = transport (p <_) e l₁

ℤ[1/2]≤-< : (p q r : ℤ[1/2]) → p ≤ q → q < r → p < r
ℤ[1/2]≤-< p q r l₁ l₂ = γ (ℤ[1/2]≤-split p q l₁)
 where
  γ : p < q ∔ (p ＝ q) → p < r
  γ (inl l₃) = ℤ[1/2]<-trans p q r l₃ l₂
  γ (inr e)  = transport (_< r) (e ⁻¹) l₂

\end{code}
