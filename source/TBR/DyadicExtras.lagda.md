This file defines some extras properties needed for the TBR development.  After
the development, the proofs should be disseminated into the relevant files.

```agda

{-# OPTIONS --allow-unsolved-metas --exact-split --auto-inline --without-K
            --lossy-unification #-}

module TBR.DyadicExtras where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Exponentiation
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Order
open import Integers.Type
open import Integers.Addition renaming (_-_ to _ℤ-_ ; _+_ to _ℤ+_)
open import Integers.Negation renaming (-_ to ℤ-_)
open import Dyadics.Addition
open import Dyadics.Multiplication
open import Dyadics.Negation
open import Dyadics.Type
open import Dyadics.Order
open import Notation.Order
open import UF.Base

ℤ[1/2]-is-positive : ℤ[1/2] → 𝓤₀ ̇
ℤ[1/2]-is-positive p = 0ℤ[1/2] < p

ℤ[1/2]<-neg : (x y : ℤ[1/2]) → 0ℤ[1/2] < y → x - y < x
ℤ[1/2]<-neg x y l = γ
 where
  I : - y < 0ℤ[1/2]
  I = ℤ[1/2]<-swap 0ℤ[1/2] y l

  II : x - y < x - 0ℤ[1/2]
  II = ℤ[1/2]<-addition-preserves-order' (- y) 0ℤ[1/2] x I

  III : x - 0ℤ[1/2] ＝ x
  III = x - 0ℤ[1/2] ＝⟨ refl                        ⟩
        x + 0ℤ[1/2] ＝⟨ ℤ[1/2]-zero-right-neutral x ⟩
        x           ∎

  γ : x - y < x
  γ = transport (x - y <_) III II

ℤ[1/2]-0<1 : 0ℤ[1/2] < 1ℤ[1/2]
ℤ[1/2]-0<1 = 0 , refl

ℤ[1/2]<-1/2 : (x : ℤ[1/2]) → 0ℤ[1/2] < x → 0ℤ[1/2] < 1/2ℤ[1/2] * x
ℤ[1/2]<-1/2 x l = γ
 where
  γ : 0ℤ[1/2] < 1/2ℤ[1/2] * x
  γ = ℤ[1/2]<-pos-multiplication-preserves-order 1/2ℤ[1/2] x ℤ[1/2]-0<1/2 l

ℤ[1/2]-trichotomous : (p q : ℤ[1/2]) → (p < q) ∔ (p ＝ q) ∔ (q < p)
ℤ[1/2]-trichotomous ((p , a) , α) ((q , b) , β) = γ I
 where
  I : trich-locate (p ℤ* pos (2^ b)) (q ℤ* pos (2^ a))
  I = ℤ-trichotomous (p ℤ* pos (2^ b)) (q ℤ* pos (2^ a))
  
  γ : trich-locate (p ℤ* pos (2^ b)) (q ℤ* pos (2^ a))
    → ((p , a) , α) < ((q , b) , β)
    ∔ (((p , a) , α) ＝ ((q , b) , β))
    ∔ (((q , b) , β) < (((p , a) , α)))
  γ (inl l)       = inl l
  γ (inr (inr l)) = inr (inr l)
  γ (inr (inl e)) = inr (inl γ')
   where
    γ' : (p , a) , α ＝ (q , b) , β
    γ' = ≈-to-＝ ((p , a) , α) ((q , b) , β) e

ℤ[1/2]<-addition-cancellable : (a b c : ℤ[1/2])
                             → a + b < c + b
                             → a < c
ℤ[1/2]<-addition-cancellable a b c l = γ
 where
  I : a + b - b < c + b - b
  I = ℤ[1/2]<-addition-preserves-order (a + b) (c + b) (- b) l

  II : (u v : ℤ[1/2]) → u + v - v ＝ u
  II u v = u + v - v   ＝⟨ ℤ[1/2]+-assoc u v (- v)                   ⟩
           u + (v - v) ＝⟨ ap (u +_) (ℤ[1/2]+-inverse-sum-to-zero v) ⟩
           u + 0ℤ[1/2] ＝⟨ ℤ[1/2]-zero-right-neutral u               ⟩ 
           u           ∎

  III : a + b - b ＝ a
  III = II a b

  IV : c + b - b ＝ c
  IV = II c b

  γ : a < c
  γ = transport₂ _<_ III IV I

ℤ[1/2]<-addition-cancellable' : (a b c : ℤ[1/2])
                              → b + a < b + c
                              → a < c
ℤ[1/2]<-addition-cancellable' a b c l = γ
 where
  I : b + a ＝ a + b
  I = ℤ[1/2]+-comm b a

  II : b + c ＝ c + b
  II = ℤ[1/2]+-comm b c

  III : a + b < c + b
  III = transport₂ _<_ I II l

  γ : a < c
  γ = ℤ[1/2]<-addition-cancellable a b c III

ℤ[1/2]<-adding : (a b c d : ℤ[1/2])
               → a < b
               → c < d
               → a + c < b + d
ℤ[1/2]<-adding a b c d l₁ l₂ = γ
 where
  I : a + c < b + c
  I = ℤ[1/2]<-addition-preserves-order a b c l₁

  II : b + c < b + d
  II = ℤ[1/2]<-addition-preserves-order' c d b l₂

  γ : a + c < b + d
  γ = ℤ[1/2]<-trans (a + c) (b + c) (b + d) I II

ℤ[1/2]<-swap' : (p q : ℤ[1/2]) → - p < - q → q < p
ℤ[1/2]<-swap' p q l = γ
 where
  I : - (- q) < - (- p)
  I = ℤ[1/2]<-swap (- p) (- q) l

  II : - (- q) ＝ q
  II = ℤ[1/2]-minus-minus q ⁻¹

  III : - (- p) ＝ p
  III = ℤ[1/2]-minus-minus p ⁻¹

  γ : q < p
  γ = transport₂ _<_ II III I

ℤ[1/2]-ordering-property : (a b c d : ℤ[1/2])
                         → (a - b) < (c - d)
                         → (a < c) ∔ (d < b)
ℤ[1/2]-ordering-property a b c d l₁ = Cases (ℤ[1/2]-trichotomous a c) γ₁ γ₂
 where
  γ₁ : a < c → (a < c) ∔ (d < b)
  γ₁ = inl

  γ₂ : (a ＝ c) ∔ (c < a) → (a < c) ∔ (d < b)
  γ₂ (inl e) = inr γ
   where
    I : c - b < c - d
    I = transport (λ z → z - b < c - d) e l₁

    II : (- b) < (- d)
    II = ℤ[1/2]<-addition-cancellable' (- b) c (- d) I

    III : - (- d) < - (- b)
    III = ℤ[1/2]<-swap (- b) (- d) II

    IV : - (- d) ＝ d
    IV = ℤ[1/2]-minus-minus d ⁻¹

    V : - ( - b) ＝ b
    V = ℤ[1/2]-minus-minus b ⁻¹

    γ : d < b
    γ = transport₂ _<_ IV V III
    
  γ₂ (inr l) = inr γ
   where
    I : - a < - c
    I = ℤ[1/2]<-swap c a l

    II : (- a) + (a - b) < (- c) + (c - d)
    II = ℤ[1/2]<-adding (- a) (- c) (a - b) (c - d) I l₁

    III : (u v : ℤ[1/2]) → (- u) + (u - v) ＝ - v
    III u v = (- u) + (u - v) ＝⟨ ℤ[1/2]+-assoc (- u) u (- v) ⁻¹             ⟩
              (- u) + u - v   ＝⟨ ap (_- v) (ℤ[1/2]+-inverse-sum-to-zero' u) ⟩
              0ℤ[1/2] - v     ＝⟨ ℤ[1/2]-zero-left-neutral (- v)             ⟩
              - v             ∎

    IV : (- a) + (a - b) ＝ - b
    IV = III a b

    V : (- c) + (c - d) ＝ - d
    V = III c d

    VI : - b < - d
    VI = transport₂ _<_ IV V II

    γ : d < b
    γ = ℤ[1/2]<-swap' b d VI

postulate
 normalise-negation :
  (a b c : ℤ) → normalise (a , c) - normalise (b , c) ＝ normalise (a ℤ- b , c)
 normalise-negation' :
  (a b : ℤ) → - normalise (a , b) ＝ normalise (ℤ- a , b)
 normalise-≤-prop : (n : ℕ) → ((k , p) : ℤ × ℤ)
                  → normalise (k , p) ≤ normalise ((k ℤ+ pos n) , p)
 normalise-≤-prop2 : (l r p : ℤ) → l ≤ r → normalise (l , p) ≤ normalise (r , p)
 from-normalise-≤-same-denom :
  (a b c : ℤ) → normalise (a , c) ≤ normalise (b , c) → a ≤ b
 normalise-succ' :
  (z n : ℤ) → normalise (z , n) ＝ normalise (z ℤ+ z , succℤ n)
 normalise-pred' :
  (z n : ℤ) → normalise (z , predℤ n) ＝ normalise (pos 2 ℤ* z , n)
 ℤ[1/2]-find-lower :
  (ε : ℤ[1/2]) → ℤ[1/2]-is-positive ε → Σ n ꞉ ℤ , normalise (pos 2 , n) < ε
 ℤ[1/2]<-1/2' : (p : ℤ[1/2]) → 0ℤ[1/2] < p → 1/2ℤ[1/2] * p < p

```
