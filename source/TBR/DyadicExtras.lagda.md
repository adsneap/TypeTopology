This file defines some extras properties needed for the TBR development.  After
the development, the proofs should be disseminated into the relevant files.

```agda

{-# OPTIONS --allow-unsolved-metas --exact-split --auto-inline --without-K
            --lossy-unification #-}

module TBR.DyadicExtras where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Exponentiation
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Properties
open import Integers.Exponentiation
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

ℤ-distributivity-neg : (p q r : ℤ) → p ℤ* q ℤ- p ℤ* r ＝ p ℤ* (q ℤ- r)
ℤ-distributivity-neg p q r = γ
 where
  I : ℤ- p ℤ* r ＝ p ℤ* (ℤ- r)
  I = negation-dist-over-mult p r ⁻¹

  γ : p ℤ* q ℤ- p ℤ* r ＝ p ℤ* (q ℤ- r)
  γ = p ℤ* q ℤ- p ℤ* r      ＝⟨ ap (p ℤ* q ℤ+_) I ⟩
      p ℤ* q ℤ+ p ℤ* (ℤ- r) ＝⟨ distributivity-mult-over-ℤ' q (ℤ- r) p ⁻¹ ⟩
      p ℤ* (q ℤ- r)         ∎

ℤ-distributivity-neg' : (p q r : ℤ) → p ℤ* q ℤ- r ℤ* q ＝ (p ℤ- r) ℤ* q
ℤ-distributivity-neg' p q r = γ
 where
  I : ℤ- r ℤ* q ＝ (ℤ- r) ℤ* q
  I = negation-dist-over-mult' r q ⁻¹

  γ : p ℤ* q ℤ- r ℤ* q ＝ (p ℤ- r) ℤ* q
  γ = p ℤ* q ℤ- r ℤ* q      ＝⟨ ap (p ℤ* q ℤ+_) I                        ⟩
      p ℤ* q ℤ+ (ℤ- r) ℤ* q ＝⟨ distributivity-mult-over-ℤ p (ℤ- r) q ⁻¹ ⟩
      (p ℤ- r) ℤ* q         ∎

2ℤ[1/2] : ℤ[1/2]
2ℤ[1/2] = (pos 2 , 0) , inl refl

normalise-neg-step' : (z : ℤ)  (n : ℕ)
 → normalise-neg (z , succ n) ＝ 2ℤ[1/2] * normalise-neg (z , n)
normalise-neg-step' z 0 = γ
 where
  I : normalise-pos (z ℤ* pos 2 , 0) ＝ (z ℤ* pos 2 , 0) , inl refl
  I = ℤ[1/2]-to-normalise-pos ((z ℤ* pos 2 , 0) , inl refl) ⁻¹

  II : z ℤ* pos 2 ℤ* pos 2 ＝ pos 2 ℤ* (z ℤ* pos 2)
  II = ℤ*-comm (z ℤ* pos 2) (pos 2)

  γ : normalise-neg (z , 1) ＝ 2ℤ[1/2] * normalise-neg (z , zero)
  γ = normalise-neg (z , 1)                           ＝⟨ refl ⟩
      normalise-neg-lemma z 1                         ＝⟨ refl ⟩
      normalise-neg-lemma (z ℤ* pos 2) 0              ＝⟨ refl ⟩
      (z ℤ* pos 2 ℤ* pos 2 , 0) , inl refl            ＝⟨ i    ⟩
      normalise-pos (z ℤ* pos 2 ℤ* pos 2 , 0)         ＝⟨ ii   ⟩
      normalise-pos ((pos 2 ℤ* (z ℤ* pos 2)) , 0)     ＝⟨ refl ⟩
      normalise-pos ((pos 2 , 0) *' (z ℤ* pos 2 , 0)) ＝⟨ iii  ⟩
      2ℤ[1/2] * normalise-pos (z ℤ* pos 2 , 0)        ＝⟨ iv   ⟩
      2ℤ[1/2] * ((z ℤ* pos 2 , 0) , inl refl)         ＝⟨ refl ⟩
      2ℤ[1/2] * normalise-neg-lemma z 0               ＝⟨ refl ⟩
      2ℤ[1/2] * normalise-neg (z , 0)                 ∎
   where
    i   = ℤ[1/2]-to-normalise-pos ((z ℤ* pos 2 ℤ* pos 2 , 0) , inl refl)
    ii  = ap (λ - → normalise-pos (- , 0)) II
    iii = ℤ[1/2]*-normalise-pos (pos 2 , 0) (z ℤ* pos 2 , 0)
    iv  = ap (2ℤ[1/2] *_) I

normalise-neg-step' z (succ n) = γ
 where
  IH : normalise-neg (z ℤ* pos 2 , succ n)
     ＝ 2ℤ[1/2] * normalise-neg (z ℤ* pos 2 , n)
  IH = normalise-neg-step' (z ℤ* pos 2) n

  I : normalise-neg (z ℤ* pos 2 , succ n)
    ＝ 2ℤ[1/2] * normalise-neg (z ℤ* pos 2 , n)
  I = normalise-neg-step' (z ℤ* pos 2) n

  γ : normalise-neg (z , succ (succ n)) ＝ 2ℤ[1/2] * normalise-neg (z , succ n)
  γ = normalise-neg (z , succ (succ n))            ＝⟨ refl ⟩
      normalise-neg-lemma z (succ (succ n))        ＝⟨ refl ⟩
      normalise-neg-lemma (z ℤ* pos 2) (succ n)    ＝⟨ refl ⟩
      normalise-neg-lemma (z ℤ* pos 2 ℤ* pos 2) n  ＝⟨ I    ⟩
      2ℤ[1/2] * normalise-neg-lemma (z ℤ* pos 2) n ＝⟨ refl ⟩
      2ℤ[1/2] * normalise-neg-lemma z (succ n)     ＝⟨ refl ⟩
      2ℤ[1/2] * normalise-neg (z , succ n)         ∎

normalise-neg-step : ((z , n) : ℤ × ℕ)
 → normalise-neg (z , succ n) ＝ 2ℤ[1/2] * normalise-neg (z , n)
normalise-neg-step (z , n) = normalise-neg-step' z n

normalise-pos-step' : (z : ℤ) (n : ℕ)
 → normalise-pos (pos 2 ℤ* z , n) ＝ 2ℤ[1/2] * normalise-pos (z , n)
normalise-pos-step' z n = γ
 where
  γ : normalise-pos (pos 2 ℤ* z , n) ＝ 2ℤ[1/2] * normalise-pos (z , n)
  γ = normalise-pos (pos 2 ℤ* z , n)         ＝⟨ i    ⟩
      normalise-pos (pos 2 ℤ* z , 0 ℕ+ n)    ＝⟨ refl ⟩
      normalise-pos ((pos 2 , 0) *' (z , n)) ＝⟨ ii   ⟩
      2ℤ[1/2] * normalise-pos (z , n)        ∎
   where
    i  = ap (λ - → normalise-pos (pos 2 ℤ* z , -)) (zero-left-neutral n ⁻¹)
    ii = ℤ[1/2]*-normalise-pos (pos 2 , 0) (z , n)

normalise-pos-step : ((z , n) : ℤ × ℕ)
 → normalise-pos (pos 2 ℤ* z , n) ＝ 2ℤ[1/2] * normalise-pos (z , n)
normalise-pos-step (z , n) = normalise-pos-step' z n

normalise-neg-to-pos' : (z : ℤ) (n : ℕ)
                     → normalise-neg (z , n)
                     ＝ normalise-pos (pos (2^ (succ n)) ℤ* z , 0)
normalise-neg-to-pos' z 0      = γ
 where
  γ : normalise-neg (z , 0) ＝ normalise-pos (pos (2^ 1) ℤ* z , 0)
  γ = normalise-neg (z , 0)               ＝⟨ refl ⟩
      (z ℤ+ z , 0) , inl refl             ＝⟨ refl ⟩
      normalise-pos (z ℤ+ z , 0)          ＝⟨ refl ⟩
      normalise-pos (z ℤ* pos 2 , 0)      ＝⟨ i    ⟩
      normalise-pos (pos 2 ℤ* z , 0)      ＝⟨ refl ⟩
      normalise-pos (pos (2^ 1) ℤ* z , 0) ∎
   where
    i = ap (λ - → normalise-pos (- , 0)) (ℤ*-comm z (pos 2))
normalise-neg-to-pos' z (succ n) = γ
 where
  IH : normalise-neg (z , n) ＝ normalise-pos (pos (2^ (succ n)) ℤ* z , 0)
  IH = normalise-neg-to-pos' z n

  n' = pos (2^ (succ n))

  γ : normalise-neg (z , succ n)
    ＝ normalise-pos (pos (2^ (succ (succ n))) ℤ* z , 0)
  γ = normalise-neg (z , succ n)                        ＝⟨ i    ⟩
      2ℤ[1/2] * normalise-neg (z , n)                   ＝⟨ ii   ⟩
      2ℤ[1/2] * normalise-pos (n' ℤ* z , 0)             ＝⟨ iii  ⟩
      normalise-pos (pos 2 ℤ* (n' ℤ* z) , 0)            ＝⟨ iv   ⟩
      normalise-pos (pos 2 ℤ* n' ℤ* z , 0)              ＝⟨ v    ⟩
      normalise-pos (pos (2 ℕ* 2^ (succ n)) ℤ* z , 0)   ＝⟨ refl ⟩
      normalise-pos (pos (2^ (succ (succ n))) ℤ* z , 0) ∎
   where
    vₐₚ : pos 2 ℤ* pos (2^ (succ n)) ＝ pos (2 ℕ* 2^ (succ n))
    vₐₚ = pos-multiplication-equiv-to-ℕ 2 (2^ (succ n))

    i   = normalise-neg-step (z , n)
    ii  = ap (2ℤ[1/2] *_) IH
    iii = normalise-pos-step (n' ℤ* z , 0) ⁻¹
    iv  = ap (λ - → normalise-pos (- , 0)) (ℤ*-assoc (pos 2) n' z ⁻¹)
    v   = ap (λ - → normalise-pos (- ℤ* z , 0)) vₐₚ

normalise-neg-to-pos : ((z , n) : ℤ × ℕ)
                     → normalise-neg (z , n)
                     ＝ normalise-pos (pos (2^ (succ n)) ℤ* z , 0)
normalise-neg-to-pos (z , n) = normalise-neg-to-pos' z n

normalise-pos-negation : (p q : ℤ) → (n : ℕ)
                       → normalise-pos (p , n) - normalise-pos (q , n)
                       ＝ normalise-pos (p ℤ- q , n)
normalise-pos-negation p q n = γ
 where
  n' = pos (2^ n)

  I : (ℤ- q) ℤ* n' ＝ ℤ- q ℤ* n'
  I = negation-dist-over-mult' q n'

  II : p ℤ* n' ℤ- q ℤ* n' ＝ (p ℤ- q) ℤ* n'
  II = ℤ-distributivity-neg' p n' q

  III : n' ℤ* n' ＝ pos (2^ (n ℕ+ n))
  III = n' ℤ* n'            ＝⟨ pos-multiplication-equiv-to-ℕ (2^ n) (2^ n) ⟩
        pos (2^ n ℕ* 2^ n)  ＝⟨ ap pos (prod-of-powers 2 n n)               ⟩
        pos (2^ (n ℕ+ n))   ∎

  IV : ((p , n) +' (ℤ- q , n)) ≈' (p ℤ- q , n)
  IV = (p ℤ* n' ℤ+ (ℤ- q) ℤ* n') ℤ* n' ＝⟨ ap (λ z → (p ℤ* n' ℤ+ z) ℤ* n') I ⟩
       (p ℤ* n' ℤ- q ℤ* n') ℤ* n'      ＝⟨ ap (_ℤ* n') II                    ⟩
       (p ℤ- q) ℤ* n' ℤ* n'            ＝⟨ ℤ*-assoc (p ℤ- q) n' n'           ⟩
       (p ℤ- q) ℤ* (n' ℤ* n')          ＝⟨ ap ((p ℤ- q) ℤ*_) III             ⟩
       (p ℤ- q) ℤ* pos (2^ (n ℕ+ n))   ∎

  γ : normalise-pos (p , n) - normalise-pos (q , n) ＝ normalise-pos (p ℤ- q , n)
  γ = normalise-pos (p , n) - normalise-pos (q , n)     ＝⟨ refl ⟩
      normalise-pos (p , n) + (- normalise-pos (q , n)) ＝⟨ i    ⟩
      normalise-pos (p , n) + normalise-pos (ℤ- q , n)  ＝⟨ ii   ⟩
      normalise-pos ((p , n) +' (ℤ- q , n))             ＝⟨ iii  ⟩
      normalise-pos (p ℤ- q , n)                        ∎
   where
    i   = ap (normalise-pos (p , n) +_) (minus-normalise-pos q n)
    ii  = ℤ[1/2]+-normalise-pos (p , n) (ℤ- q , n) ⁻¹
    iii = ≈'-to-＝ ((p , n) +' (ℤ- q , n)) (p ℤ- q , n) IV

normalise-negation :
 (p q n : ℤ) → normalise (p , n) - normalise (q , n) ＝ normalise (p ℤ- q , n)
normalise-negation p q (pos n) = normalise-pos-negation p q n
normalise-negation p q (negsucc n) = γ
 where
  n' = pos (2^ (succ n))

  γ : normalise (p , negsucc n) - normalise (q , negsucc n)
    ＝ normalise (p ℤ- q , negsucc n)
  γ = normalise (p , negsucc n) - normalise (q , negsucc n)     ＝⟨ i   ⟩
      normalise-pos (n' ℤ* p , 0) - normalise (q , negsucc n)   ＝⟨ ii  ⟩
      normalise-pos (n' ℤ* p , 0) - normalise-pos (n' ℤ* q , 0) ＝⟨ iii ⟩
      normalise-pos (n' ℤ* p ℤ- n' ℤ* q , 0)                    ＝⟨ iv  ⟩
      normalise-pos (n' ℤ* (p ℤ- q) , 0)                        ＝⟨ v   ⟩
      normalise (p ℤ- q , negsucc n)                            ∎
   where
    iiₐₚ : normalise-neg (q , n) ＝ normalise-pos (pos (2^ (succ n)) ℤ* q , 0)
    iiₐₚ = normalise-neg-to-pos (q , n)

    i   = ap (_- normalise (q , negsucc n)) (normalise-neg-to-pos (p , n))
    ii  = ap (λ z → normalise-pos (n' ℤ* p , 0) - z) iiₐₚ
    iii = normalise-pos-negation (n' ℤ* p) (n' ℤ* q) 0
    iv  = ap (λ z → normalise-pos (z , 0)) (ℤ-distributivity-neg n' p q)
    v   = normalise-neg-to-pos (p ℤ- q , n) ⁻¹

normalise-negation' : (z n : ℤ) → - normalise (z , n) ＝ normalise (ℤ- z , n)
normalise-negation' z (pos n)     = minus-normalise-pos z n
normalise-negation' z (negsucc n) = γ
 where
  I : ℤ- pos (2^ (succ n)) ℤ* z ＝ pos (2^ (succ n)) ℤ* (ℤ- z)
  I = negation-dist-over-mult (pos (2^ (succ n))) z ⁻¹

  γ : - normalise (z , negsucc n) ＝ normalise (ℤ- z , negsucc n)
  γ = - normalise (z , negsucc n)                     ＝⟨ refl ⟩
      - normalise-neg (z , n)                         ＝⟨ i    ⟩
      - normalise-pos (pos (2^ (succ n)) ℤ* z , 0)    ＝⟨ ii   ⟩
      normalise-pos (ℤ- pos (2^ (succ n)) ℤ* z , 0)   ＝⟨ iii  ⟩
      normalise-pos (pos (2^ (succ n)) ℤ* (ℤ- z) , 0) ＝⟨ iv   ⟩
      normalise-neg (ℤ- z , n) ＝⟨ refl ⟩
      normalise (ℤ- z , negsucc n) ∎
   where
    i   = ap -_ (normalise-neg-to-pos (z , n))
    ii  = minus-normalise-pos (pos (2^ (succ n)) ℤ* z) 0
    iii = ap (λ - → normalise-pos (- , 0)) I
    iv  = normalise-neg-to-pos (ℤ- z , n) ⁻¹

normalise-pos-succ : (z : ℤ) (n : ℕ) → normalise-pos (z , n) ＝ normalise-pos (z ℤ+ z , succ n)
normalise-pos-succ z n = ≈'-to-＝ (z , n) (z ℤ+ z , succ n) γ
 where
  I : pos (2 ℕ* 2^ n) ＝ pos 2 ℤ* pos (2^ n)
  I = pos-multiplication-equiv-to-ℕ 2 (2^ n) ⁻¹

  γ : (z , n) ≈' (z ℤ+ z , succ n)
  γ = z ℤ* pos (2^ (succ n))     ＝⟨ refl                               ⟩
      z ℤ* pos (2 ℕ* 2^ n)       ＝⟨ ap (z ℤ*_) I                       ⟩
      z ℤ* (pos 2 ℤ* pos (2^ n)) ＝⟨ ℤ*-assoc z (pos 2) (pos (2^ n)) ⁻¹ ⟩
      z ℤ* pos 2 ℤ* pos (2^ n)   ＝⟨ refl                               ⟩
      (z ℤ+ z) ℤ* pos (2^ n)     ∎

normalise-succ' : (z n : ℤ) → normalise (z , n) ＝ normalise (z ℤ+ z , succℤ n)
normalise-succ' z (pos n)     = normalise-pos-succ z n
normalise-succ' z (negsucc 0) = γ
 where
  I : pos 2 ℤ* z ＝ z ℤ* pos 2
  I = ℤ*-comm (pos 2) z

  γ : normalise (z , negsucc 0) ＝ normalise (z ℤ+ z , pos 0)
  γ = normalise (z , negsucc 0)      ＝⟨ refl                               ⟩
      normalise-neg (z , 0)          ＝⟨ normalise-neg-to-pos (z , 0)       ⟩
      normalise-pos (pos 2 ℤ* z , 0) ＝⟨ ap (λ - → normalise-pos (- , 0)) I ⟩
      normalise-pos (z ℤ+ z , 0)     ＝⟨ refl                               ⟩
      normalise (z ℤ+ z , pos 0)     ∎
normalise-succ' z (negsucc (succ x)) = γ
 where
  I : pos (2^ (succ (succ x))) ℤ* z ＝ pos (2^ (succ x)) ℤ* (z ℤ+ z)
  I = pos (2^ (succ (succ x))) ℤ* z     ＝⟨ refl ⟩
      pos (2 ℕ* 2^ (succ x)) ℤ* z       ＝⟨ i    ⟩
      pos 2 ℤ* pos (2^ (succ x)) ℤ* z   ＝⟨ ii   ⟩
      pos (2^ (succ x)) ℤ* pos 2 ℤ* z   ＝⟨ iii  ⟩
      pos (2^ (succ x)) ℤ* (pos 2 ℤ* z) ＝⟨ iv   ⟩
      pos (2^ (succ x)) ℤ* (z ℤ+ z)     ∎
   where
    i   = ap (_ℤ* z) (pos-multiplication-equiv-to-ℕ 2 (2^ (succ x)) ⁻¹)
    ii  = ap (_ℤ* z) (ℤ*-comm (pos 2) (pos (2^ (succ x))))
    iii = ℤ*-assoc (pos (2^ (succ x))) (pos 2) z
    iv  = ap (pos (2^ (succ x)) ℤ*_) (ℤ*-comm (pos 2) z)

  γ : normalise (z , negsucc (succ x))
    ＝ normalise (z ℤ+ z , succℤ (negsucc (succ x)))
  γ = normalise (z , negsucc (succ x))                  ＝⟨ refl ⟩
      normalise-neg (z , succ x)                        ＝⟨ i    ⟩
      normalise-pos (pos (2^ (succ (succ x))) ℤ* z , 0) ＝⟨ ii   ⟩
      normalise-pos (pos (2^ (succ x)) ℤ* (z ℤ+ z) , 0) ＝⟨ iii  ⟩
      normalise-neg (z ℤ+ z , x)                        ＝⟨ refl ⟩
      normalise (z ℤ+ z , succℤ (negsucc (succ x)))     ∎
   where
    i   = normalise-neg-to-pos (z , succ x)
    ii  = ap (λ - → normalise-pos (- , 0)) I
    iii = normalise-neg-to-pos (z ℤ+ z , x) ⁻¹

normalise-pred' : (z n : ℤ)
                → normalise (z , predℤ n) ＝ normalise (pos 2 ℤ* z , n)
normalise-pred' z n = γ
 where
  I : normalise (z , predℤ n) ＝ normalise (z ℤ+ z , succℤ (predℤ n))
  I = normalise-succ' z (predℤ n)

  γ : normalise (z , predℤ n) ＝ normalise (pos 2 ℤ* z , n)
  γ = normalise (z , predℤ n)              ＝⟨ i   ⟩
      normalise (z ℤ+ z , succℤ (predℤ n)) ＝⟨ ii  ⟩
      normalise (z ℤ+ z , n)               ＝⟨ iii ⟩
      normalise (pos 2 ℤ* z , n)           ∎
   where
    i   = normalise-succ' z (predℤ n)
    ii  = ap (λ - → normalise (z ℤ+ z , -)) (succpredℤ n)
    iii = ap (λ - → normalise (- , n)) (ℤ*-comm z (pos 2))

normalise-≤-prop2 : (p q n : ℤ) → p ≤ q → normalise (p , n) ≤ normalise (q , n)
normalise-≤-prop2 p q (pos n) l = normalise-pos-≤ (p , n) (q , n) γ
 where
  I : is-pos-succ (pos (2^ n))
  I = exponents-of-two-positive n

  γ : p ℤ* pos (2^ n) ≤ q ℤ* pos (2^ n)
  γ = positive-multiplication-preserves-order' p q (pos (2^ n)) I l
normalise-≤-prop2 p q (negsucc n) l = γ
 where
  I : normalise-pos (pos (2^ (succ n)) ℤ* p , 0) ＝ normalise-neg (p , n)
  I = normalise-neg-to-pos (p , n) ⁻¹

  II : normalise-pos (pos (2^ (succ n)) ℤ* q , 0) ＝ normalise-neg (q , n)
  II = normalise-neg-to-pos (q , n) ⁻¹

  III : is-pos-succ (pos (2^ (succ n)))
  III = exponents-of-two-positive (succ n)

  IV : p ℤ* pos (2^ (succ n)) ≤ q ℤ* pos (2^ (succ n))
  IV = positive-multiplication-preserves-order' p q (pos (2^ (succ n))) III l

  V : pos (2^ (succ n)) ℤ* p ≤ pos (2^ (succ n)) ℤ* q
  V = transport₂ _≤_ i ii IV
   where
    i : p ℤ* pos (2^ (succ n)) ＝ pos (2^ (succ n)) ℤ* p
    i = ℤ*-comm p (pos (2^ (succ n)))

    ii : q ℤ* pos (2^ (succ n)) ＝ pos (2^ (succ n)) ℤ* q
    ii = ℤ*-comm q (pos (2^ (succ n)))

  γ' : normalise-pos (pos (2^ (succ n)) ℤ* p , 0)
      ≤ normalise-pos (pos (2^ (succ n)) ℤ* q , 0)
  γ' = normalise-pos-≤
        (pos (2^ (succ n)) ℤ* p , 0)
        (pos (2^ (succ n)) ℤ* q , 0)
        V

  γ : normalise-neg (p , n) ≤ normalise-neg (q , n)
  γ = transport₂ _≤_ I II γ'

normalise-≤-prop : (n : ℕ) → ((k , p) : ℤ × ℤ)
                 → normalise (k , p) ≤ normalise (k ℤ+ pos n , p)
normalise-≤-prop n (k , p) = normalise-≤-prop2 k (k ℤ+ pos n) p (n , refl)

from-normalise-≤-same-denom :
 (p q n : ℤ) → normalise (p , n) ≤ normalise (q , n) → p ≤ q
from-normalise-≤-same-denom p q (pos n) l₁ = Cases (ℤ-trichotomous p q) γ₁ γ
 where
  γ₁ : p < q → p ≤ q
  γ₁ = <-is-≤ p q

  γ : (p ＝ q) ∔ q < p → p ≤ q
  γ e = Cases e γ₂ γ₃
   where
    γ₂ : p ＝ q → p ≤ q
    γ₂ e = transport (p ≤_) e (ℤ≤-refl p)

    γ₃ : q < p → p ≤ q
    γ₃ l₂ = 𝟘-elim γ₄
     where
      I : is-pos-succ (pos (2^ n))
      I = exponents-of-two-positive n

      II : q ℤ* pos (2^ n) < p ℤ* pos (2^ n)
      II = positive-multiplication-preserves-order q p (pos (2^ n)) I l₂

      III : normalise-pos (q , n) < normalise-pos (p , n)
      III = normalise-pos-< (q , n) (p , n) II

      IV : normalise-pos (q , n) < normalise-pos (q , n)
      IV = ℤ[1/2]<-≤ (normalise-pos (q , n))
                     (normalise-pos (p , n))
                     (normalise-pos (q , n))
                     III l₁

      γ₄ : 𝟘
      γ₄ = ℤ[1/2]<-not-itself (normalise-pos (q , n)) IV
from-normalise-≤-same-denom p q (negsucc n) l₁ = Cases (ℤ-trichotomous p q) γ₁ γ
 where
  γ₁ : p < q → p ≤ q
  γ₁ = <-is-≤ p q

  γ : (p ＝ q) ∔ q < p → p ≤ q
  γ e = Cases e γ₂ γ₃
   where
    γ₂ : p ＝ q → p ≤ q
    γ₂ e = transport (p ≤_) e (ℤ≤-refl p)

    γ₃ : q < p → p ≤ q
    γ₃ l₂ = 𝟘-elim γ₄
     where
      I : normalise-neg (p , n) ＝ normalise-pos (pos (2^ (succ n)) ℤ* p , 0)
      I = normalise-neg-to-pos (p , n)

      II : normalise-neg (q , n) ＝ normalise-pos (pos (2^ (succ n)) ℤ* q , 0)
      II = normalise-neg-to-pos (q , n)

      III : normalise-pos (pos (2^ (succ n)) ℤ* p , 0)
          ≤ normalise-pos (pos (2^ (succ n)) ℤ* q , 0)
      III = transport₂ _≤_ I II l₁

      IV : is-pos-succ (pos (2^ (succ n)))
      IV = exponents-of-two-positive (succ n)

      V : q ℤ* pos (2^ (succ n)) < p ℤ* pos (2^ (succ n))
      V = positive-multiplication-preserves-order q p (pos (2^ (succ n))) IV l₂

      VI : pos (2^ (succ n)) ℤ* q < pos (2^ (succ n)) ℤ* p
      VI = transport₂ _<_ i ii V
       where
        i : q ℤ* pos (2^ (succ n)) ＝ pos (2^ (succ n)) ℤ* q
        i = ℤ*-comm q (pos (2^ (succ n)))

        ii : p ℤ* pos (2^ (succ n)) ＝ pos (2^ (succ n)) ℤ* p
        ii = ℤ*-comm p (pos (2^ (succ n)))

      VII : normalise-pos (pos (2^ (succ n)) ℤ* q , 0)
          < normalise-pos (pos (2^ (succ n)) ℤ* p , 0)
      VII = normalise-pos-<
             (pos (2^ (succ n)) ℤ* q , 0)
             (pos (2^ (succ n)) ℤ* p , 0)
             VI

      VIII : normalise-pos (pos (2^ (succ n)) ℤ* q , 0)
           < normalise-pos (pos (2^ (succ n)) ℤ* q , 0)
      VIII = ℤ[1/2]<-≤
              (normalise-pos (pos (2^ (succ n)) ℤ* q , 0))
              (normalise-pos (pos (2^ (succ n)) ℤ* p , 0))
              (normalise-pos (pos (2^ (succ n)) ℤ* q , 0))
              VII III

      γ₄ : 𝟘
      γ₄ = ℤ[1/2]<-not-itself (normalise-pos (pos (2^ (succ n)) ℤ* q , 0)) VIII

ℤ[1/2]<-1/2' : (p : ℤ[1/2]) → 0ℤ[1/2] < p → 1/2ℤ[1/2] * p < p
ℤ[1/2]<-1/2' p l = γ
 where
  1/2 = 1/2ℤ[1/2]

  I : 0ℤ[1/2] < 1/2 * p
  I = ℤ[1/2]<-pos-multiplication-preserves-order 1/2 p ℤ[1/2]-0<1/2 l

  II : 0ℤ[1/2] + 1/2 * p < 1/2 * p + 1/2 * p
  II = ℤ[1/2]<-addition-preserves-order 0ℤ[1/2] (1/2 * p) (1/2 * p) I

  III : 0ℤ[1/2] + 1/2 * p ＝ 1/2 * p
  III = ℤ[1/2]-zero-left-neutral (1/2 * p)

  IV : 1/2 * p + 1/2 * p ＝ p
  IV = 1/2 * p + 1/2 * p ＝⟨ ℤ[1/2]-distributivity' 1/2 1/2 p ⁻¹ ⟩
       (1/2 + 1/2) * p   ＝⟨ ap (_* p) ℤ[1/2]-1/2+1/2            ⟩
       1ℤ[1/2] * p       ＝⟨ ℤ[1/2]*-mult-left-id p              ⟩
       p                 ∎

  γ : 1/2 * p < p
  γ = transport₂ _<_ III IV II

normalise-pos-<-to-< : ((p , a) (q , b) : ℤ × ℕ)
                     → normalise-pos (p , a) < normalise-pos (q , b)
                     → (p , a) < (q , b)
normalise-pos-<-to-< (p , a) (q , b) l₁ = I t
 where
  t : trich-locate (p ℤ* pos (2^ b)) (q ℤ* pos (2^ a))
  t = ℤ-trichotomous (p ℤ* pos (2^ b)) (q ℤ* pos (2^ a))

  I : (p ℤ* pos (2^ b) < q ℤ* pos (2^ a))
    ∔ (p ℤ* pos (2^ b) ＝ q ℤ* pos (2^ a))
    ∔ (q ℤ* pos (2^ a) < p ℤ* pos (2^ b))
    → p ℤ* pos (2^ b) < q ℤ* pos (2^ a)
  I (inl l₂) = l₂
  I (inr (inl e)) = 𝟘-elim γ
   where
    II : normalise-pos (p , a) ＝ normalise-pos (q , b)
    II = ≈'-to-＝ (p , a) (q , b) e

    III : normalise-pos (p , a) < normalise-pos (p , a)
    III = transport (normalise-pos (p , a) <_) (II ⁻¹) l₁

    γ : 𝟘
    γ = ℤ[1/2]<-not-itself (normalise-pos (p , a)) III
  I (inr (inr l₂)) = 𝟘-elim γ
   where
    II : normalise-pos (q , b) < normalise-pos (p , a)
    II = normalise-pos-< (q , b) (p , a) l₂

    III : normalise-pos (p , a) < normalise-pos (p , a)
    III = ℤ[1/2]<-trans
           (normalise-pos (p , a))
           (normalise-pos (q , b))
           (normalise-pos (p , a))
            l₁ II

    γ : 𝟘
    γ = ℤ[1/2]<-not-itself (normalise-pos (p , a)) III

ℤ<-+ : (p : ℤ) (n : ℕ) → p < p ℤ+ pos (succ n)
ℤ<-+ p 0        = zero , refl
ℤ<-+ p (succ n) = γ (ℤ<-+ p n)
 where
  γ : p < p ℤ+ pos (succ n) → p < p ℤ+ pos (succ (succ n))
  γ (k , e) = (succ k) , ap succℤ e

ℤ<-pos-mult : (p : ℤ) (q : ℕ) → pos 0 < p → p < p ℤ* (pos 2 ℤ* pos (succ q))
ℤ<-pos-mult p 0 (k , e) = k , γ
 where
  γ : succℤ p ℤ+ pos k ＝ p ℤ+ p
  γ = succℤ p ℤ+ pos k      ＝⟨ ℤ-left-succ p (pos k)                ⟩
      succℤ (p ℤ+ pos k)    ＝⟨ ℤ-right-succ p (pos k) ⁻¹            ⟩
      p ℤ+ succℤ (pos k)    ＝⟨ ap (p ℤ+_) (ℤ+-comm (pos k) (pos 1)) ⟩
      p ℤ+ (pos 1 ℤ+ pos k) ＝⟨ ap (p ℤ+_) e                         ⟩
      p ℤ+ p                ∎
ℤ<-pos-mult p (succ q) l = γ
 where
  IH : p < p ℤ* (pos 2 ℤ* pos (succ q))
  IH = ℤ<-pos-mult p q l

  I : pos 0 < p ℤ* pos 2
  I = ℤ<-pos-multiplication-preserves-order p (pos 2) l (1 , refl)

  II : p < p ℤ* (pos 2 ℤ* pos (succ q)) ℤ+ p ℤ* pos 2
  II = ℤ<-adding p (p ℤ* (pos 2 ℤ* pos (succ q))) (pos 0) (p ℤ* pos 2) IH I

  III : p ℤ* (pos 2 ℤ* pos (succ q)) ℤ+ p ℤ* pos 2
      ＝ p ℤ* (pos 2 ℤ* pos (succ (succ q)))
  III = p ℤ* (pos 2 ℤ* pos (succ q)) ℤ+ p ℤ* pos 2     ＝⟨ i    ⟩
        p ℤ* (pos 2 ℤ* pos (succ q) ℤ+ pos 2)          ＝⟨ refl ⟩
        p ℤ* (pos 2 ℤ* pos (succ q) ℤ+ pos 2 ℤ* pos 1) ＝⟨ ii   ⟩
        p ℤ* (pos 2 ℤ* pos (succ (succ q))) ∎
   where
    iiₐₚ : pos 2 ℤ* pos (succ q) ℤ+ pos 2 ℤ* pos 1
        ＝ pos 2 ℤ* (pos (succ q) ℤ+ pos 1)
    iiₐₚ = distributivity-mult-over-ℤ' (pos (succ q)) (pos 1) (pos 2) ⁻¹

    i  = distributivity-mult-over-ℤ' (pos 2 ℤ* pos (succ q)) (pos 2) p ⁻¹
    ii = ap (p ℤ*_) iiₐₚ

  γ : p < p ℤ* (pos 2 ℤ* pos (succ (succ q)))
  γ = transport (p <_) III II

exponents-of-two-positive' : (n : ℕ) → pos 0 < pos (2^ n)
exponents-of-two-positive' 0        = 0 , refl
exponents-of-two-positive' (succ n) = γ
 where
  I : pos 0 < pos 2
  I = 1 , refl

  II : pos 0 < pos (2^ n)
  II = exponents-of-two-positive' n

  III : pos 0 < pos 2 ℤ* pos (2^ n)
  III = ℤ<-pos-multiplication-preserves-order (pos 2) (pos (2^ n)) I II

  IV : pos 2 ℤ* pos (2^ n) ＝ pos (2^ (succ n))
  IV = pos 2 ℤ* pos (2^ n) ＝⟨ pos-multiplication-equiv-to-ℕ 2 (2^ n) ⟩
       pos (2 ℕ* 2^ n)     ＝⟨ refl                                   ⟩
       pos (2^ (succ n))   ∎

  γ : pos 0 < pos (2^ (succ n))
  γ = transport (pos 0 <_) IV III

ℤ[1/2]-find-lower' : (p n : ℕ)
                   → (α : is-ℤ[1/2] (pos (succ p)) n)
                   → Σ k ꞉ ℤ , normalise (pos 2 , k) < ((pos (succ p) , n) , α)
ℤ[1/2]-find-lower' p n α = pos (succ (succ n)) , γ
 where
  I : (pos (succ p) , n) , α ＝ normalise-pos (pos (succ p) , n)
  I = ℤ[1/2]-to-normalise-pos ((pos (succ p) , n) , α)

  II : pos 0 < pos (2^ n)
  II = exponents-of-two-positive' n

  III : pos 0 < pos 2 ℤ* pos (2^ n)
  III = ℤ<-pos-multiplication-preserves-order (pos 2) (pos (2^ n)) (1 , refl) II

  IV : pos 0 < pos 2 ℤ* pos (succ p)
  IV = ℤ<-pos-multiplication-preserves-order (pos 2) (pos (succ p)) (1 , refl) i
   where
    i : pos 0 < pos (succ p)
    i = ℤ-zero-less-than-pos p

  V : pos 2 ℤ* pos (2^ n) ℤ* (pos 2 ℤ* pos (succ p))
    ＝ pos (succ p) ℤ* pos (2^ (succ (succ n)))
  V = pos 2 ℤ* pos (2^ n) ℤ* (pos 2 ℤ* pos (succ p)) ＝⟨ i   ⟩
      pos (2^ (succ n)) ℤ* (pos 2 ℤ* pos (succ p))   ＝⟨ ii  ⟩
      pos 2 ℤ* pos (succ p) ℤ* pos (2^ (succ n))     ＝⟨ iii ⟩
      pos (succ p) ℤ* pos 2 ℤ* pos (2^ (succ n))     ＝⟨ iv  ⟩
      pos (succ p) ℤ* (pos 2 ℤ* pos (2^ (succ n)))   ＝⟨ v   ⟩
      pos (succ p) ℤ* pos (2^ (succ (succ n)))       ∎
   where
    iₐₚ : pos 2 ℤ* pos (2^ n) ＝ pos (2 ℕ* 2^ n)
    iₐₚ = pos-multiplication-equiv-to-ℕ 2 (2^ n)

    i   = ap (_ℤ* (pos 2 ℤ* pos (succ p)) ) iₐₚ
    ii  = ℤ*-comm (pos (2^ (succ n))) (pos 2 ℤ* pos (succ p))
    iii = ap (_ℤ* pos (2^ (succ n))) (ℤ*-comm (pos 2) (pos (succ p)))
    iv  = ℤ*-assoc (pos (succ p)) (pos 2) (pos (2^ (succ n)))
    v   = ap (pos (succ p) ℤ*_) (pos-multiplication-equiv-to-ℕ 2 (2^ (succ n)))

  VI : pos 2 ℤ* pos (2^ n) < pos 2 ℤ* pos (2^ n) ℤ* (pos 2 ℤ* pos (succ p))
  VI = ℤ<-pos-mult (pos 2 ℤ* pos (2^ n)) p III

  γ'' : pos 2 ℤ* pos (2^ n) < pos (succ p) ℤ* pos (2^ (succ (succ n)))
  γ'' = transport (pos 2 ℤ* pos (2^ n) <_) V VI

  γ' : normalise-pos (pos 2 , succ (succ n)) < normalise-pos (pos (succ p) , n)
  γ' = normalise-pos-< (pos 2 , succ (succ n)) (pos (succ p) , n) γ''

  γ : normalise-pos (pos 2 , succ (succ n)) < ((pos (succ p) , n) , α)
  γ = transport (normalise-pos (pos 2 , succ (succ n)) <_) (I ⁻¹) γ'

ℤ[1/2]-find-lower : (ε : ℤ[1/2])
                  → ℤ[1/2]-is-positive ε
                  → Σ k ꞉ ℤ , normalise (pos 2 , k) < ε
ℤ[1/2]-find-lower ((pos (succ p) , n) , α) l = ℤ[1/2]-find-lower' p n α
ℤ[1/2]-find-lower ((pos 0 , n) , α) l = 𝟘-elim γ
 where
  I : (pos 0 , n) , α ＝ normalise-pos (pos 0 , n)
  I = ℤ[1/2]-to-normalise-pos ((pos 0 , n) , α)

  II : normalise-pos (pos 0 , 0) < normalise-pos (pos 0 , n)
  II = transport (normalise-pos (pos 0 , 0) <_) I l

  III : (pos 0 , 0) < (pos 0 , n)
  III = normalise-pos-<-to-< (pos 0 , 0) (pos 0 , n) II

  IV : pos 0 ℤ* pos (2^ n) ＝ pos 0
  IV = ℤ-zero-left-base (pos (2^ n))

  V : pos 0 < pos 0
  V = transport (_< pos 0) IV III

  γ : 𝟘
  γ = ℤ-equal-not-less-than (pos 0) V
ℤ[1/2]-find-lower ((negsucc p , n) , α) l = 𝟘-elim γ
 where
  I : (negsucc p , n) , α ＝ normalise-pos (negsucc p , n)
  I = ℤ[1/2]-to-normalise-pos ((negsucc p , n) , α)

  II : normalise-pos (pos 0 , 0) < normalise-pos (negsucc p , n)
  II = transport (normalise-pos (pos 0 , 0) <_) I l

  III : (pos 0 , 0) < (negsucc p , n)
  III = normalise-pos-<-to-< (pos 0 , 0) (negsucc p , n) II

  IV : pos 0 ℤ* pos (2^ n) ＝ pos 0
  IV = ℤ-zero-left-base (pos (2^ n))

  V : pos 0 < negsucc p
  V = transport (_< negsucc p) IV III

  γ : 𝟘
  γ = negative-not-greater-than-zero p V

_ℤ[1/2]'≤_ : (x y : ℤ × ℤ) → 𝓤₀ ̇
(x , pos a) ℤ[1/2]'≤ (y , pos b)         = (x , a) ≤ (y , b)
(x , pos a) ℤ[1/2]'≤ (y , negsucc b)     = (x , a) ≤ (pos (2^ (succ b)) ℤ* y , 0)
(x , negsucc a) ℤ[1/2]'≤ (y , pos b)     = (pos (2^ (succ a)) ℤ* x , 0) ≤ (y , b)
(x , negsucc a) ℤ[1/2]'≤ (y , negsucc b) = (pos (2^ (succ a)) ℤ* x , 0) ≤ (pos (2^ (succ b)) ℤ* y , 0)

instance
 Order-ℤℤ : Order (ℤ × ℤ) (ℤ × ℤ)
 _≤_ {{Order-ℤℤ}} = _ℤ[1/2]'≤_

normalise-≤ : (x y : ℤ × ℤ)
            → x ≤ y
            → normalise x ≤ normalise y
normalise-≤ (x , pos a) (y , pos b) x≤y = γ
 where
  γ : normalise-pos (x , a) ≤ normalise-pos (y , b)
  γ = normalise-pos-≤ (x , a) (y , b) x≤y
normalise-≤ (x , pos a) (y , negsucc b) x≤y = γ
 where
  I : normalise-pos (x , a) ≤ normalise-pos (pos (2^ (succ b)) ℤ* y , 0)
  I = normalise-pos-≤ (x , a) (pos (2^ (succ b)) ℤ* y , 0) x≤y

  II : normalise-pos (pos (2^ (succ b)) ℤ* y , 0) ＝ normalise (y , negsucc b)
  II = normalise-neg-to-pos (y , b) ⁻¹

  γ : normalise (x , pos a) ≤ normalise (y , negsucc b)
  γ = transport (normalise (x , pos a) ≤_) II I
normalise-≤ (x , negsucc a) (y , pos b) x≤y = γ
 where
  I : normalise-pos (pos (2^ (succ a)) ℤ* x , 0) ≤ normalise-pos (y , b)
  I = normalise-pos-≤ (pos (2^ (succ a)) ℤ* x , 0) (y , b) x≤y

  II : normalise-pos (pos (2^ (succ a)) ℤ* x , 0) ＝ normalise (x , negsucc a)
  II = normalise-neg-to-pos (x , a) ⁻¹

  γ : normalise (x , negsucc a) ≤ normalise (y , pos b)
  γ = transport (_≤ normalise-pos (y , b)) II I
normalise-≤ (x , negsucc a) (y , negsucc b) x≤y = γ
 where
  I : normalise-pos (pos (2^ (succ a)) ℤ* x , 0)
    ≤ normalise-pos (pos (2^ (succ b)) ℤ* y , 0)
  I = normalise-pos-≤
       (pos (2^ (succ a)) ℤ* x , 0)
       (pos (2^ (succ b)) ℤ* y , 0)
       x≤y

  II : normalise-pos (pos (2^ (succ a)) ℤ* x , 0) ＝ normalise (x , negsucc a)
  II = normalise-neg-to-pos (x , a) ⁻¹

  III : normalise-pos (pos (2^ (succ b)) ℤ* y , 0) ＝ normalise (y , negsucc b)
  III = normalise-neg-to-pos (y , b) ⁻¹

  γ : normalise (x , negsucc a) ≤ normalise (y , negsucc b)
  γ = transport₂ _≤_ II III I

```
