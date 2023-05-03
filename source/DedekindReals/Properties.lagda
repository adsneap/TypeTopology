Andrew Sneap, April 2021 - January 2022

In this file, I prove that the Reals are arithmetically located.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Powerset
open import UF.Subsingletons
open import Naturals.Properties
open import Naturals.Order
open import Rationals.Type
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order

module DedekindReals.Properties
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where
open import DedekindReals.Type fe pe pt
open import MetricSpaces.Rationals fe pe pt
open import Rationals.Limits fe pe pt

open PropositionalTruncation pt

 -- Need to generalise this , y - x ＝ a , 0 < a
exists-2/3-n : (x y p : ℚ) → x < y → 0ℚ < p → Σ n ꞉ ℕ , (((⟨2/3⟩^ n) * (y - x)) < p)
exists-2/3-n x y (p , α) l₁ l₂ = V use-limit
 where
  p-convert : p , α ＝ toℚ p
  p-convert = toℚ-to𝔽 (p , α)
  I : ¬ (y - x ＝ 0ℚ)
  I e = ℚ<-not-itself x (transport (x <_) δ l₁)
   where
    δ : y ＝ x
    δ = y                  ＝⟨ ℚ-zero-right-neutral y ⁻¹ ⟩
        y + 0ℚ             ＝⟨ ap (y +_) (ℚ-inverse-sum-to-zero x ⁻¹) ⟩
        y + (x - x)        ＝⟨ ap (y +_) (ℚ+-comm x (- x)) ⟩
        y + ((- x) + x)    ＝⟨ ℚ+-assoc y (- x) x ⁻¹ ⟩
        y - x + x          ＝⟨ ap (_+ x) e ⟩
        0ℚ + x             ＝⟨ ℚ-zero-left-neutral x ⟩
        x                  ∎

  II : 0ℚ < y - x
  II = ℚ<-difference-positive x y l₁

  z = ℚ*-inv (y - x) I

  III : 0ℚ < ℚ*-inv (y - x) I
  III = ℚ-inv-preserves-pos (y - x) II I

  IV : 0ℚ < (toℚ p * ℚ*-inv (y - x) I)
  IV = ℚ<-pos-multiplication-preserves-order (toℚ p) (ℚ*-inv (y - x) I) (transport (0ℚ <_) p-convert l₂) III

  use-limit : Σ N ꞉ ℕ , ((n : ℕ) → N ≤ n → ℚ-metric (⟨2/3⟩^ n) 0ℚ < (toℚ p * ℚ*-inv (y - x) I))
  use-limit = ⟨2/3⟩^n-converges (toℚ p * ℚ*-inv (y - x) I) IV

  V : (Σ N ꞉ ℕ , ((n : ℕ) → N ≤ n → ℚ-metric (⟨2/3⟩^ n) 0ℚ < (toℚ p * ℚ*-inv (y - x) I)))
     → Σ n ꞉ ℕ , (((⟨2/3⟩^ n) * (y - x)) < (p , α))
  V (N , f) = (succ N) , transport₂ _<_ VIII IX VII
   where
    abstract
     VI : ℚ-metric (⟨2/3⟩^ succ N) 0ℚ <ℚ (toℚ p * ℚ*-inv (y - x) I)
     VI = f (succ N) (≤-succ N)
     VII : ℚ-metric  (⟨2/3⟩^ succ N) 0ℚ  * (y - x) <ℚ (toℚ p * ℚ*-inv (y - x) I) * (y - x)
     VII = ℚ<-pos-multiplication-preserves-order' (ℚ-metric (⟨2/3⟩^ succ N) 0ℚ) ((toℚ p * ℚ*-inv (y - x) I)) (y - x) VI II
     VIII : ℚ-metric (⟨2/3⟩^ succ N) 0ℚ * (y - x) ＝ ((⟨2/3⟩^ (succ N)) * (y - x))
     VIII = ap (_* (y - x)) i
      where
       i : ℚ-metric (⟨2/3⟩^ succ N) 0ℚ ＝ (⟨2/3⟩^ (succ N))
       i = ℚ-metric (⟨2/3⟩^ succ N) 0ℚ ＝⟨ by-definition ⟩
           abs ((⟨2/3⟩^ succ N) - 0ℚ)     ＝⟨ ap (λ β → abs ((⟨2/3⟩^ succ N) + β) ) (ℚ-minus-zero-is-zero ⁻¹) ⟩
           abs ((⟨2/3⟩^ succ N) + 0ℚ)     ＝⟨ ap abs (ℚ-zero-right-neutral ((⟨2/3⟩^ succ N))) ⟩
           abs (⟨2/3⟩^ succ N)            ＝⟨ abs-of-pos-is-pos (⟨2/3⟩^ succ N) (ℚ<-coarser-than-≤ 0ℚ (⟨2/3⟩^ succ N) (⟨2/3⟩^n-positive (succ N))) ⟩
           (⟨2/3⟩^ succ N) ∎
     IX : (toℚ p * ℚ*-inv (y - x) I) * (y - x) ＝ (p , α)
     IX = toℚ p * ℚ*-inv (y - x) I * (y - x)     ＝⟨ ap (λ γ → γ * (ℚ*-inv (y - x) I) * (y - x)) (p-convert ⁻¹) ⟩
          (p , α) * ℚ*-inv (y - x) I * (y - x)   ＝⟨ ℚ*-assoc (p , α) (ℚ*-inv (y - x) I) (y - x) ⟩
          (p , α) * (ℚ*-inv (y - x) I * (y - x)) ＝⟨ ap ((p , α) *_) (ℚ*-comm ((ℚ*-inv (y - x) I)) (y - x)) ⟩
          (p , α) * ((y - x) * ℚ*-inv (y - x) I) ＝⟨ ap ((p , α) *_) (ℚ*-inverse-product (y - x) I) ⟩
          (p , α) * 1ℚ ＝⟨ ℚ-mult-right-id (p , α) ⟩
          p , α ∎

ral-lemma : (α β : ℚ) → (n : ℕ) → β ＝ 2/3 * α → ((rec 2/3 (λ k → k * 2/3) n * 2/3) * α) ＝ (rec 2/3 (λ k → k * 2/3) n * β)
ral-lemma α β n e = ((rec 2/3 (λ k → k * 2/3) n * 2/3) * α) ＝⟨ refl ⟩
               (((⟨2/3⟩^ (succ (succ n))) * α) )            ＝⟨ ap (_* α) (I (succ n)) ⟩
               (((⟨2/3⟩^ succ n) * 2/3) * α)                ＝⟨ ℚ*-assoc (⟨2/3⟩^ (succ n)) 2/3 α ⟩
               ((⟨2/3⟩^ succ n) * (2/3 * α))                ＝⟨ ap ((⟨2/3⟩^ (succ n)) *_) (e ⁻¹) ⟩
               (rec 2/3 (λ k → k * 2/3) n * β)              ∎
 where
  I : (n : ℕ) → ⟨2/3⟩^ (succ n) ＝ ((⟨2/3⟩^ n) * 2/3)
  I zero = f
   where
    abstract
     f : ⟨2/3⟩^ (succ 0) ＝ ((⟨2/3⟩^ 0) * 2/3)
     f = (ℚ-mult-left-id 2/3) ⁻¹
  I (succ n) = refl

ℝ-arithmetically-located : (z : ℝ)
                         → (p : ℚ)
                         → 0ℚ < p
                         → ∃ (x , y) ꞉ ℚ × ℚ , (x < z) × (z < y) × 0ℚ < (y - x) × (y - x) < p
ℝ-arithmetically-located ((L , R) , inhabited-left , inhabited-right , rounded-left , rounded-right , disjoint , located) p l = ∥∥-rec ∃-is-prop I (binary-choice inhabited-left inhabited-right)
 where
  I : (Σ x ꞉ ℚ , x ∈ L) × (Σ y ꞉ ℚ , y ∈ R) → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < (y - x) × (y - x) < p)
  I ((x , x-L) , (y , y-R)) = II x y x-L y-R (pr₁ γ) (trisect x y (disjoint x y (x-L , y-R))) (pr₂ γ)
   where
    γ : Sigma ℕ (λ n → ((⟨2/3⟩^ n) * (y - x)) < p)
    γ = exists-2/3-n x y p (disjoint x y (x-L , y-R)) l

    II : (x y : ℚ) → x ∈ L → y ∈ R → (n : ℕ) → (Σ (x' , y') ꞉ ℚ × ℚ , x < x' × x' < y' × y' < y × ((y - x') ＝ (2/3 * (y - x))) × (y' - x ＝ 2/3 * (y - x)))
       → ((⟨2/3⟩^ n) * (y - x)) < p
       → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < (y - x)) × ((y - x) < p)
    II x y x-L y-R zero ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄            = ∣ (x , y) , x-L , y-R , α , β ∣
     where
      abstract
       α : 0ℚ <ℚ (y - x)
       α = ℚ<-difference-positive x y (disjoint x y (x-L , y-R))
       β : y - x <ℚ p
       β = transport (_<ℚ p) (ℚ-mult-left-id (y - x)) l₄

    II x y x-L y-R (succ zero) ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄     = ∥∥-rec ∃-is-prop III (located x' y' l₂)
     where
      III : (x' ∈ L) ∔ (y' ∈ R) → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < y - x × y - x < p)
      III (inl x'-L) = ∣ (x' , y) , x'-L , y-R , α , β ∣
       where
        abstract
         α : 0ℚ <ℚ y - x'
         α = ℚ<-difference-positive x' y (disjoint x' y (x'-L , y-R))
         β : y - x' <ℚ p
         β = transport (_<ℚ p) (e₁ ⁻¹) l₄
      III (inr y'-R) = ∣ (x , y') , x-L , y'-R , α , β ∣
       where
        abstract
         α : 0ℚ <ℚ y' - x
         α = ℚ<-difference-positive x y' (disjoint x y' (x-L , y'-R))
         β : y' - x <ℚ p
         β = transport (_<ℚ p) (e₂ ⁻¹) l₄
    II x y x-L y-R (succ (succ n)) ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄ =
      ∥∥-induction (λ _ → ∃-is-prop)
        (cases (λ x'-L → II x' y  x'-L y-R  (succ n) (trisect x' y (ℚ<-trans x' y' y l₂ l₃)) III)
               (λ y'-R → II x  y' x-L  y'-R (succ n) (trisect x y' (ℚ<-trans x x' y' l₁ l₂)) IV))
        (located x' y' l₂)
     where
      III : ((⟨2/3⟩^ succ n) * (y - x')) < p
      III = transport (_< p) (ral-lemma (y - x) (y - x') n e₁) l₄
      IV : ((⟨2/3⟩^ succ n) * (y' - x)) < p
      IV = transport (_< p) (ral-lemma (y - x) (y' - x) n e₂) l₄

trans→disjoint : (L R : 𝓟 ℚ) → disjoint L R → (q : ℚ) → ¬ (q ∈ L × q ∈ R)
trans→disjoint L R dis q (qL , qR) = ℚ<-not-itself q I
 where
  I : q < q
  I = dis q q (qL , qR)

disjoint→trans : (L R : 𝓟 ℚ) → located L R →  ((q : ℚ) → ¬ (q ∈ L × q ∈ R)) → disjoint L R
disjoint→trans L R loc dis p q (pL , qR) = I (ℚ-trichotomous p q)
 where
  I : p < q ∔ (p ＝ q) ∔ q < p → p < q
  I (inl l) = l
  I (inr (inl e)) = 𝟘-elim (dis q ((transport (_∈ L) e pL) , qR))
  I (inr (inr r)) = 𝟘-elim (∥∥-rec 𝟘-is-prop III II)
   where
    II : q ∈ L ∨ p ∈ R
    II = loc q p r
    III : ¬ (q ∈ L ∔ p ∈ R)
    III (inl qL) = dis q (qL , qR)
    III (inr pR) = dis p (pL , pR)

\end{code}
