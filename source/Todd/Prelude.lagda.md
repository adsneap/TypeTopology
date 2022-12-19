
This file defines dyadic rationals as a record, along with many widely
accepted operations, relations and results on dyadic rationals. They
are denoted ℤ[1/2].

```agda

{-# OPTIONS --exact-split --without-K --auto-inline --experimental-lossy-unification #-}

open import Integers.Addition renaming (_+_ to _+ℤ_ ; _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Properties
open import Naturals.Order hiding (max; ≤-refl; ≤-split)
open import Notation.Order 
open import UF.Base
open import UF.FunExt
open import UF.Miscelanea
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Todd.Prelude where

ℕ-is-discrete : (x y : ℕ) → decidable (x ＝ y)
ℕ-is-discrete zero zero = inl refl
ℕ-is-discrete zero (succ y) = inr (λ ())
ℕ-is-discrete (succ x) zero = inr (λ ())
ℕ-is-discrete (succ x) (succ y)
 = Cases (ℕ-is-discrete x y)
     (inl ∘ ap succ)
     (inr ∘ λ f g → f (succ-lc g))

_≤ℤ_≤ℤ_ : ℤ → ℤ → ℤ → 𝓤₀ ̇ 
x ≤ℤ y ≤ℤ z = (x ≤ℤ y) × (y ≤ℤ z)

≤ℤ²-is-prop : {l u : ℤ} (x : ℤ) → is-prop (l ≤ℤ x ≤ℤ u)
≤ℤ²-is-prop {l} {u} x = ×-is-prop (ℤ≤-is-prop l x) (ℤ≤-is-prop x u)

data 𝟛 : 𝓤₀ ̇ where
  −1 O +1 : 𝟛

_/2 : ℕ → ℕ
0 /2 = 0
1 /2 = 0
succ (succ n) /2 = succ (n /2)

_/2' : ℤ → ℤ
pos x     /2' = pos (x /2)
negsucc x /2' = ℤ- (pos (succ x /2))

sign : ℤ → (ℕ → ℤ)
sign (pos     _) = pos
sign (negsucc _) = negsucc

num : ℤ → ℕ
num  (pos     n) = n
num  (negsucc n) = n

odd even : ℤ → 𝓤₀ ̇
odd (pos                   0) = 𝟘
odd (pos                   1) = 𝟙
odd (pos (succ (succ x)))     = odd (pos x)
odd (negsucc               0) = 𝟙
odd (negsucc               1) = 𝟘
odd (negsucc (succ (succ x))) = odd (negsucc x)
even x = ¬ odd x

even-or-odd? : (x : ℤ) → even x + odd x
even-or-odd? (pos                   0) = inl (λ x → x)
even-or-odd? (pos                   1) = inr ⋆
even-or-odd? (pos (succ (succ x)))     = even-or-odd? (pos x)
even-or-odd? (negsucc               0) = inr ⋆
even-or-odd? (negsucc               1) = inl (λ x → x)
even-or-odd? (negsucc (succ (succ x))) = even-or-odd? (negsucc x)

odd-is-prop : (x : ℤ) → is-prop (odd x)
odd-is-prop (pos                   0) = 𝟘-is-prop
odd-is-prop (pos                   1) = 𝟙-is-prop
odd-is-prop (pos (succ (succ x)))     = odd-is-prop (pos x)
odd-is-prop (negsucc               0) = 𝟙-is-prop
odd-is-prop (negsucc               1) = 𝟘-is-prop
odd-is-prop (negsucc (succ (succ x))) = odd-is-prop (negsucc x)

succ-odd-is-even : (x : ℤ) → odd x → even (succℤ x)
succ-odd-is-even (pos                          1) o = id
succ-odd-is-even (pos            (succ (succ x))) o = succ-odd-is-even (pos x) o
succ-odd-is-even (negsucc                      0) o = id
succ-odd-is-even (negsucc (succ (succ (succ x)))) o = succ-odd-is-even (negsucc (succ x)) o

succ-even-is-odd : (x : ℤ) → even x → odd (succℤ x)
succ-even-is-odd (pos                          0) e = ⋆
succ-even-is-odd (pos                          1) e = e ⋆
succ-even-is-odd (pos            (succ (succ x))) e = succ-even-is-odd (pos x) e
succ-even-is-odd (negsucc                      0) e = e ⋆
succ-even-is-odd (negsucc                      1) e = ⋆
succ-even-is-odd (negsucc                      2) e = e ⋆
succ-even-is-odd (negsucc (succ (succ (succ x)))) e = succ-even-is-odd (negsucc (succ x)) e

odd-succ-succ : (x : ℤ) → odd x → odd (succℤ (succℤ x))
odd-succ-succ (pos x) = id
odd-succ-succ (negsucc zero) = id
odd-succ-succ (negsucc (succ (succ x))) = id

even-succ-succ : (x : ℤ) → even x → even (succℤ (succℤ x))
even-succ-succ (pos x) = id
even-succ-succ (negsucc zero) = id
even-succ-succ (negsucc (succ (succ x))) = id

-- even-is-prop : (x : ℤ) → is-prop (even x)
-- even-is-prop x p q = dfunext (fe _ _) (λ i → 𝟘-elim (p i))

-- even-or-odd-is-prop : (x : ℤ) → is-prop (even x + odd x)
-- even-or-odd-is-prop x = +-is-prop (even-is-prop x) (odd-is-prop x) id

_−ℤ_ : ℤ → ℤ → ℤ
x −ℤ y = x +ℤ (ℤ- y)

ℤ[_,_] : ℤ → ℤ → 𝓤₀ ̇
ℤ[ l , u ] = Σ z ꞉ ℤ , (l ≤ℤ z ≤ℤ u)

ℤ[_,_]-succ : (l u : ℤ) → ℤ[ l , u ] → ℤ[ l , succℤ u ]
ℤ[ l , u ]-succ (z , l≤z , z≤u) = z , l≤z , ℤ≤-trans z u (succℤ u) z≤u (1 , refl) 

≤ℤ-antisym : ∀ x y → x ≤ℤ y ≤ℤ x → x ＝ y
≤ℤ-antisym x y (x≤y , y≤x) with ℤ≤-split x y x≤y | ℤ≤-split y x y≤x
... | inl (n , γ) | inl (m , δ)
 = 𝟘-elim (ℤ-equal-not-less-than x (ℤ<-trans x y x (n , γ) (m , δ)))
... | inl  _  | inr y＝x = y＝x ⁻¹
... | inr x＝y | _       = x＝y

≤ℤ-back : ∀ x y → x <ℤ y → x ≤ℤ predℤ y
≤ℤ-back x .(succℤ x +ℤ pos n) (n , refl)
 = ℤ≤-trans x (x +pos n) (predℤ (succℤ x +pos n))
     (n , refl)
     (transport ((x +pos n) ≤ℤ_)
       (predsuccℤ (x +pos n) ⁻¹
       ∙ ap predℤ (ℤ-left-succ x (pos n) ⁻¹))
       (ℤ≤-refl (x +pos n)))

ℤ-dich-succ : (x y : ℤ) 
            → ((      x <ℤ y) + (y ≤ℤ       x))
            → ((succℤ x <ℤ y) + (y ≤ℤ succℤ x))
ℤ-dich-succ x y (inl (0 , refl)) = inr (ℤ≤-refl _)
ℤ-dich-succ x y (inl (succ m , refl)) = inl (m , ℤ-left-succ-pos (succℤ x) m)
ℤ-dich-succ x y (inr (m , refl)) = inr (succ m , refl)

ℤ-trich-succ : (x y : ℤ) 
             → ((      x <ℤ y) + (      x ＝ y) + (y <ℤ       x))
             → ((succℤ x <ℤ y) + (succℤ x ＝ y) + (y <ℤ succℤ x))
ℤ-trich-succ x y (inl (0           , sn+j＝i))
 = (inr ∘ inl) sn+j＝i
ℤ-trich-succ x y (inl (succ j      , sn+j＝i))
 = inl (j , (ℤ-left-succ-pos (succℤ x) j ∙ sn+j＝i))
ℤ-trich-succ x y (inr (inl              n＝i))
 = (inr ∘ inr) (0 , ap succℤ (n＝i ⁻¹))
ℤ-trich-succ x y (inr (inr (j      , sn+j＝i)))
 = (inr ∘ inr) (succ j , ap succℤ sn+j＝i)

ℤ-vert-trich-locate : ℤ → ℤ → ℤ → 𝓤₀ ̇
ℤ-vert-trich-locate z a b = (z <ℤ a) + (a ≤ℤ z ≤ℤ b) + (b <ℤ z)

ℤ-vert-trich-succ : (z a b : ℤ) → a <ℤ b
                  → ℤ-vert-trich-locate        z  a b
                  → ℤ-vert-trich-locate (succℤ z) a b
ℤ-vert-trich-succ z a b (k , η) (inl (succ n , ε))
 = inl         (n , (ℤ-left-succ-pos (succℤ z) n ∙ ε))
ℤ-vert-trich-succ z a b (k , η) (inl (0      , refl))
 = (inr ∘ inl) ((0 , refl) , (succ k , (ℤ-left-succ-pos (succℤ z) k ⁻¹ ∙ η)))
ℤ-vert-trich-succ z a b (k , η) (inr (inl ((n₁ , ε₁) , succ n₂ , ε₂)))
 = (inr ∘ inl) ((succ n₁ , (ap succℤ ε₁)) , (n₂ , (ℤ-left-succ-pos z n₂ ∙ ε₂)))
ℤ-vert-trich-succ z a b (k , η) (inr (inl ((n₁ , ε₁) , zero , ε₂)))
 = (inr ∘ inr) (0 , ap succℤ (ε₂ ⁻¹))
ℤ-vert-trich-succ z a b (k , η) (inr (inr (n , refl)))
 = (inr ∘ inr) (succ n , refl)

ℤ-vert-trich-all : (z a b : ℤ) → ℤ-vert-trich-locate z a b
ℤ-vert-trich-all z a b = Cases (ℤ-trichotomous z a) inl
                 λ a≤z → Cases (ℤ-trichotomous b z) (inr ∘ inr)
                 λ z≤b → (inr ∘ inl) (ℤ≤-attach _ _ a≤z , ℤ≤-attach _ _ z≤b)

ℤ-vert-trich-is-prop : (z a b : ℤ) → a <ℤ b → is-prop (ℤ-vert-trich-locate z a b)
ℤ-vert-trich-is-prop z a b a<b
 = +-is-prop (ℤ<-is-prop z a) (+-is-prop (≤ℤ²-is-prop z) (ℤ<-is-prop b z)
     (λ (_ , z≤b) → ℤ-bigger-or-equal-not-less z b z≤b))
    (λ z<a → cases
     (λ (a≤z , _) → ℤ-less-not-bigger-or-equal z a z<a a≤z)
     (ℤ-bigger-or-equal-not-less z b (<-is-≤ z b (ℤ<-trans z a b z<a a<b))))

ne : (a b c : ℤ)
   → ((n , _) : a ≤ c) → ((n₁ , _) : a ≤ b) → ((n₂ , _) : b ≤ c)
   → n₁ +ℕ n₂ ＝ n
ne a b c a≤c a≤b b≤c = ℤ≤-same-witness a c (ℤ≤-trans a b c a≤b b≤c) a≤c

ye : (a b c : ℤ) → ((n , _) : a ≤ c) → a ≤ b → ((n₂ , _) : b ≤ c) → n₂ < succ n
ye a b c (n , q) (n₁ , r) (n₂ , s)
 = transport (n₂ ≤_) (ne a b c (n , q) (n₁ , r) (n₂ , s)) (≤-+' n₁ n₂) 

rec-f-＝ : {X : 𝓤 ̇ } → (f : X → X) (x : X) (n : ℕ)
        → rec (f x) f n ＝ rec x f (succ n) 
rec-f-＝ f x zero = refl
rec-f-＝ f x (succ n) = ap f (rec-f-＝ f x n)

ℤ≤²-refl : (k : ℤ) → k ≤ℤ k ≤ℤ k
ℤ≤²-refl k = ℤ≤-refl k , ℤ≤-refl k

_ℕ^_ : ℕ → ℕ → ℕ
a ℕ^ b = ((a ℕ*_) ^ b) 1

infixl 33 _ℕ^_ 

2^ : ℕ → ℕ
2^ = 2 ℕ^_

negation-preserves-parity : (x : ℤ) → even x → even (ℤ- x)
negation-preserves-parity (pos 0) = id
negation-preserves-parity (pos (succ 0)) e = 𝟘-elim (e ⋆)
negation-preserves-parity (pos (succ (succ 0))) e = id
negation-preserves-parity (pos (succ (succ (succ x)))) e = negation-preserves-parity (pos (succ x)) e
negation-preserves-parity (negsucc 0) e = 𝟘-elim (e ⋆)
negation-preserves-parity (negsucc (succ 0)) e = id
negation-preserves-parity (negsucc (succ (succ x))) e = negation-preserves-parity (negsucc x) (even-succ-succ (negsucc (succ (succ x))) e)

even-lemma-pos : (x : ℕ) → even (pos x) → (pos x /2') ℤ* pos 2 ＝ pos x
even-lemma-pos 0 even-x = refl
even-lemma-pos (succ 0) even-x = 𝟘-elim (even-x ⋆)
even-lemma-pos (succ (succ x)) even-x = succℤ (pos x /2') +ℤ succℤ (pos x /2')    ＝⟨ ℤ-left-succ (pos x /2') (succℤ (pos x /2')) ⟩
                                          succℤ (succℤ ((pos x /2') ℤ* pos 2))       ＝⟨ ap (λ z → succℤ (succℤ z)) (even-lemma-pos x even-x) ⟩
                                          pos (succ (succ x)) ∎

even-lemma-neg : (x : ℕ) → even (negsucc x) → (negsucc x /2') ℤ* pos 2 ＝ negsucc x
even-lemma-neg x even-x = (ℤ- pos (succ x /2)) ℤ- pos (succ x /2)  ＝⟨ negation-dist (pos (succ x /2)) (pos (succ x /2)) ⟩
                          ℤ- (pos (succ x /2) +ℤ pos (succ x /2)) ＝⟨ ap ℤ-_ (even-lemma-pos (succ x) (negation-preserves-parity (negsucc x) even-x)) ⟩
                          negsucc x ∎

even-lemma : (x : ℤ) → even x → (x /2') ℤ* pos 2 ＝ x
even-lemma (pos x) = even-lemma-pos x
even-lemma (negsucc x) = even-lemma-neg x

power-of-pos-positive : ∀ n → is-pos-succ (pos (2^ n))
power-of-pos-positive 0 = ⋆
power-of-pos-positive (succ n) = transport is-pos-succ (pos-multiplication-equiv-to-ℕ 2 (2^ n)) I
 where
  I : is-pos-succ (pos 2 ℤ* pos (2^ n))
  I = is-pos-succ-mult (pos 2) (pos (2^ n)) ⋆ (power-of-pos-positive n)

prod-of-powers : (n a b : ℕ) → n ℕ^ a ℕ* n ℕ^ b ＝ n ℕ^ (a +ℕ b)
prod-of-powers n a zero     = refl
prod-of-powers n a (succ b) = I
 where
  I : n ℕ^ a ℕ* n ℕ^ succ b ＝ n ℕ^ (a +ℕ succ b)
  I = n ℕ^ a ℕ* n ℕ^ succ b   ＝⟨ refl ⟩
      n ℕ^ a ℕ* (n ℕ* n ℕ^ b) ＝⟨ mult-associativity (n ℕ^ a) n (n ℕ^ b) ⁻¹ ⟩
      n ℕ^ a ℕ* n ℕ* n ℕ^ b   ＝⟨ ap (_ℕ* n ℕ^ b) (mult-commutativity (n ℕ^ a) n) ⟩
      n ℕ* n ℕ^ a ℕ* n ℕ^ b   ＝⟨ mult-associativity n (n ℕ^ a) (n ℕ^ b) ⟩
      n ℕ* (n ℕ^ a ℕ* n ℕ^ b) ＝⟨ ap (n ℕ*_) (prod-of-powers n a b) ⟩
      n ℕ* n ℕ^ (a +ℕ b)       ＝⟨ refl ⟩
      n ℕ^ succ (a +ℕ b)       ＝⟨ refl ⟩
      n ℕ^ (a +ℕ succ b)       ∎

odd-succ-succ' : (k : ℤ) → odd (succℤ (succℤ k)) → odd k
odd-succ-succ' (pos x) = id
odd-succ-succ' (negsucc zero) = id
odd-succ-succ' (negsucc (succ (succ x))) = id

even-succ-succ' : (k : ℤ) → even (succℤ (succℤ k)) → even k
even-succ-succ' (pos 0) e = id
even-succ-succ' (pos (succ 0)) e = 𝟘-elim (e ⋆)
even-succ-succ' (pos (succ (succ x))) e = e
even-succ-succ' (negsucc 0) e = 𝟘-elim (e ⋆)
even-succ-succ' (negsucc (succ 0)) e = id
even-succ-succ' (negsucc (succ (succ x))) e = e

times-two-even' : (k : ℤ) → even (k +ℤ k)
times-two-even' (pos (succ k)) odd2k = times-two-even' (pos k) (odd-succ-succ' (pos k +ℤ pos k) (transport odd I odd2k))
 where
  I : pos (succ k) +ℤ pos (succ k) ＝ pos k +ℤ pos (succ (succ k))
  I = ℤ-left-succ (pos k) (pos (succ k))
times-two-even' (negsucc (succ k)) odd2k = times-two-even' (negsucc k) (transport odd I (odd-succ-succ (negsucc (succ k) +ℤ negsucc (succ k)) odd2k))
 where
  I : succℤ (succℤ (negsucc (succ k) +ℤ negsucc (succ k))) ＝ negsucc k +ℤ negsucc k
  I = succℤ (succℤ (negsucc (succ k) +ℤ negsucc (succ k)))   ＝⟨ refl ⟩
      succℤ (succℤ (predℤ (negsucc k) +ℤ predℤ (negsucc k))) ＝⟨ refl ⟩
      succℤ (succℤ (predℤ (predℤ (negsucc k) +ℤ negsucc k))) ＝⟨ ap (λ a → succℤ a) (succpredℤ (predℤ (negsucc k) +ℤ negsucc k)) ⟩
      succℤ (predℤ (negsucc k) +ℤ negsucc k)                 ＝⟨ ap succℤ (ℤ-left-pred (negsucc k) (negsucc k)) ⟩
      succℤ (predℤ (negsucc k +ℤ negsucc k))                 ＝⟨ succpredℤ (negsucc k +ℤ negsucc k) ⟩
      negsucc k +ℤ negsucc k ∎

negsucc-lemma : (x : ℕ) → negsucc x +ℤ negsucc x ＝ negsucc (x +ℕ succ x)
negsucc-lemma x = negsucc x +ℤ negsucc x           ＝⟨ refl ⟩
                  (ℤ- pos (succ x)) ℤ- pos (succ x)  ＝⟨ negation-dist (pos (succ x)) (pos (succ x)) ⟩
                  ℤ- (pos (succ x) +ℤ pos (succ x)) ＝⟨ refl ⟩
                  ℤ- succℤ (pos (succ x) +ℤ pos x)  ＝⟨ ap (λ z → ℤ- succℤ z) (distributivity-pos-addition (succ x) x) ⟩
                  ℤ- succℤ (pos (succ x +ℕ x))       ＝⟨ refl ⟩
                  negsucc (succ x +ℕ x)             ＝⟨ ap negsucc (addition-commutativity (succ x) x) ⟩
                  negsucc (x +ℕ succ x)             ∎

div-by-two' : (k : ℕ) → k +ℕ k /2 ＝ k
div-by-two' 0 = refl
div-by-two' (succ k) = (succ k +ℕ succ k) /2     ＝⟨ ap _/2 (succ-left k (succ k)) ⟩
                       succ (succ (k +ℕ k)) /2  ＝⟨ refl ⟩
                       succ ((k +ℕ k) /2)        ＝⟨ ap succ (div-by-two' k) ⟩
                       succ k                    ∎

div-by-two : (k : ℤ) → (k +ℤ k) /2' ＝ k
div-by-two (pos k) = (pos k +ℤ pos k) /2' ＝⟨ ap _/2' (distributivity-pos-addition k k) ⟩     
                     pos (k +ℕ k) /2'      ＝⟨ ap pos (div-by-two' k) ⟩
                     pos k ∎
div-by-two (negsucc x) = (negsucc x +ℤ negsucc x) /2'   ＝⟨ ap _/2' (negsucc-lemma x) ⟩
                         negsucc (x +ℕ succ x) /2'     ＝⟨ refl ⟩
                         ℤ- pos (succ (x +ℕ succ x) /2) ＝⟨ ap (λ z → ℤ- pos (z /2)) (succ-left x (succ x) ⁻¹) ⟩
                         ℤ- pos ((succ x +ℕ succ x) /2) ＝⟨ ap (λ z → ℤ- pos z) (div-by-two' (succ x)) ⟩
                         negsucc x ∎

```

```
ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , (n ＝ 0) + ((n ≠ 0) × odd z)

ℤ[1/2]-cond-is-prop : FunExt → (z : ℤ) (n : ℕ) → is-prop ((n ＝ 0) + ((n ≠ 0) × odd z))
ℤ[1/2]-cond-is-prop fe z n =
 +-is-prop ℕ-is-set (×-is-prop (Π-is-prop (fe 𝓤₀ 𝓤₀) (λ _ → 𝟘-is-prop)) (odd-is-prop z)) λ e (ne , _) → ne e

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , inl refl

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , inl refl

1/2ℤ[1/2] : ℤ[1/2]
1/2ℤ[1/2] = (pos 1 , 1) , inr (positive-not-zero 0 , ⋆)

normalise-pos normalise-neg : ℤ → ℕ → ℤ[1/2]
normalise-pos z 0        = (z , 0) , inl refl
normalise-pos z (succ n) with even-or-odd? z
... | inl e = normalise-pos (z /2') n
... | inr o = (z , succ n) , inr (positive-not-zero n , o)
normalise-neg z 0        = (z +ℤ z , 0) , inl refl
normalise-neg z (succ n) = normalise-neg (z +ℤ z) n

normalise-pos' : (x : ℤ) → (a : ℕ) → let ((k , δ) , p) = normalise-pos x a
                                     in Σ m ꞉ ℕ , ((pos (2^ m) ℤ* k , δ +ℕ m) ＝ x , a)
normalise-pos' x 0 = 0 , to-×-＝ (ℤ-mult-left-id x) refl
normalise-pos' x (succ a) with even-or-odd? x
... | inr odd-k = 0 , (to-×-＝ (ℤ-mult-left-id x) refl)
... | inl even-k with normalise-pos' (x /2') a
... | (m , e) with from-×-＝' e
... | (e₁ , e₂) = let (k , δ) , p = normalise-pos (x /2') a in
                  succ m ,
                  to-×-＝' (
                  (pos (2^ (succ m)) ℤ* k   ＝⟨ refl ⟩
                  pos (2 ℕ* 2^ m) ℤ* k      ＝⟨ ap (_ℤ* k) (pos-multiplication-equiv-to-ℕ 2 (2^ m) ⁻¹) ⟩
                  pos 2 ℤ* pos (2^ m) ℤ* k   ＝⟨ ℤ*-assoc (pos 2) (pos (2^ m)) k ⟩
                  pos 2 ℤ* (pos (2^ m) ℤ* k) ＝⟨ ap (pos 2 ℤ*_) e₁ ⟩
                  pos 2 ℤ* (x /2')          ＝⟨ ℤ*-comm (pos 2) (x /2') ⟩
                  (x /2') ℤ* pos 2          ＝⟨ even-lemma x even-k ⟩ 
                  x ∎)
                  , ap succ e₂)

normalise : ℤ × ℤ → ℤ[1/2]
normalise (k , pos     n) = normalise-pos k n
normalise (k , negsucc n) = normalise-neg k n

normalise-neg' : (x : ℤ) (a : ℕ) → let ((k , δ) , p) = normalise-neg x a
                                   in (k , δ) ＝ pos (2^ (succ a)) ℤ* x , 0
normalise-neg' x 0        = to-×-＝ (ℤ*-comm x (pos 2)) refl
normalise-neg' x (succ a) with from-×-＝' (normalise-neg' (x +ℤ x) a)
... | e₁ , e₂ = to-×-＝ I e₂
 where
  I : pr₁ (pr₁ (normalise-neg (x +ℤ x) a)) ＝ pos (2^ (succ (succ a))) ℤ* x
  I = pr₁ (pr₁ (normalise-neg (x +ℤ x) a)) ＝⟨ e₁ ⟩
      pos (2^ (succ a)) ℤ* (x ℤ* pos 2)     ＝⟨ ap (pos (2^ (succ a)) ℤ*_) (ℤ*-comm x (pos 2)) ⟩
      pos (2^ (succ a)) ℤ* (pos 2 ℤ* x)     ＝⟨ ℤ*-assoc (pos (2^ (succ a))) (pos 2) x ⁻¹ ⟩
      pos (2^ (succ a)) ℤ* pos 2 ℤ* x       ＝⟨ ap (_ℤ* x) (pos-multiplication-equiv-to-ℕ (2^ (succ a)) 2) ⟩
      pos (2^ (succ a) ℕ* 2) ℤ* x          ＝⟨ ap (λ z → pos z ℤ* x) (mult-commutativity (2^ (succ a)) 2) ⟩
      pos (2^ (succ (succ a))) ℤ* x ∎

lowest-terms-normalised : FunExt → (((k , δ) , p) : ℤ[1/2]) → normalise-pos k δ ＝ ((k , δ) , p)
lowest-terms-normalised fe ((k , .0) , inl refl) = refl
lowest-terms-normalised fe ((k , zero) , inr (δnz , k-odd)) = 𝟘-elim (δnz refl)
lowest-terms-normalised fe ((k , succ δ) , inr (δnz , k-odd)) with even-or-odd? k
... | inl k-even = 𝟘-elim (k-even k-odd)
... | inr k-odd = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop fe z n) refl

normalise-pos-lemma₁ : FunExt → (k : ℤ) (δ : ℕ) (p : (δ ＝ 0) + ((δ ≠ 0) × odd k))
             → normalise-pos ((k +ℤ k) /2') δ ＝ (k , δ) , p
normalise-pos-lemma₁ fe k 0 (inl refl) = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop fe z n) (to-×-＝ (div-by-two k) refl)
normalise-pos-lemma₁ fe k 0 (inr (δnz , k-odd)) = 𝟘-elim (δnz refl)
normalise-pos-lemma₁ fe k (succ δ) (inr p) with even-or-odd? ((k +ℤ k) /2')
normalise-pos-lemma₁ fe k (succ δ) (inr (δnz , k-odd)) | inl k-even = 𝟘-elim (k-even (transport odd (div-by-two k ⁻¹) k-odd))
... | inr _ = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop fe z n) (to-×-＝ (div-by-two k) refl)

normalise-pos-lemma₂ : (k : ℤ) (δ : ℕ) → normalise-pos k δ ＝ normalise-pos (k +ℤ k) (succ δ)
normalise-pos-lemma₂ k δ with even-or-odd? (k +ℤ k)
... | inl _ = ap (λ s → normalise-pos s δ) (div-by-two k ⁻¹)
... | inr o = 𝟘-elim (times-two-even' k o)

double : ℤ → ℤ
double a = a +ℤ a

normalise-lemma : FunExt → (k : ℤ) (δ : ℕ) (n : ℕ) (p : (δ ＝ 0) + ((δ ≠ 0) × odd k))
                → normalise (rec k double n +ℤ rec k double n , (pos (succ δ) +ℤ pos n)) ＝ (k , δ) , p
normalise-lemma fe k δ 0 p with even-or-odd? (k +ℤ k)
... | inl even = normalise-pos-lemma₁ fe k δ p
... | inr odd = 𝟘-elim (times-two-even' k odd)
normalise-lemma fe k δ (succ n) p with even-or-odd? (k +ℤ k)
... | inl even = let y = rec k double n 
                     z = (y +ℤ y) in 
                 normalise (z +ℤ z , (succℤ (pos (succ δ) +ℤ pos n))) ＝⟨ ap (λ - → normalise (z +ℤ z , succℤ -)) (distributivity-pos-addition (succ δ) n) ⟩
                 normalise (z +ℤ z , succℤ (pos (succ δ +ℕ n)))      ＝⟨ refl ⟩
                 normalise-pos (z +ℤ z) (succ (succ δ +ℕ n))         ＝⟨ normalise-pos-lemma₂ z (succ δ +ℕ n) ⁻¹ ⟩
                 normalise-pos z (succ δ +ℕ n)                      ＝⟨ refl ⟩
                 normalise (z , pos (succ δ +ℕ n))                  ＝⟨ ap (λ - → normalise (z , -)) (distributivity-pos-addition (succ δ) n ⁻¹) ⟩
                 normalise (z , pos (succ δ) +ℤ pos n)               ＝⟨ normalise-lemma fe k δ n p ⟩
                 (k , δ) , p ∎ 
... | inr odd = 𝟘-elim (times-two-even' k odd)

_<ℤ[1/2]_ _≤ℤ[1/2]_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇
((x , n) , _) <ℤ[1/2] ((y , m) , _) = x ℤ* pos (2^ m) < y ℤ* pos (2^ n)
((x , n) , _) ≤ℤ[1/2] ((y , m) , _) = x ℤ* pos (2^ m) ≤ y ℤ* pos (2^ n)

<ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x <ℤ[1/2] y)
<ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ<-is-prop (x ℤ* pos (2^ b)) (y ℤ* pos (2^ a)) 

≤ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x ≤ℤ[1/2] y)
≤ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ≤-is-prop (x ℤ* pos (2^ b)) (y ℤ* pos (2^ a))

ℤ[1/2]⁺ : 𝓤₀ ̇
ℤ[1/2]⁺ = Σ x ꞉ ℤ[1/2] , 0ℤ[1/2] <ℤ[1/2] x

_<ℤ[1/2]⁺_ _≤ℤ[1/2]⁺_ : ℤ[1/2]⁺ → ℤ[1/2]⁺ → 𝓤₀ ̇
(x , l) <ℤ[1/2]⁺ (y , l') = x <ℤ[1/2] y
(x , l) ≤ℤ[1/2]⁺ (y , l') = x ≤ℤ[1/2] y

is-positive : ℤ[1/2] -> 𝓤₀ ̇
is-positive x = 0ℤ[1/2] <ℤ[1/2] x

instance
 Order-ℤ[1/2]-ℤ[1/2] : Order ℤ[1/2] ℤ[1/2]
 _≤_ {{Order-ℤ[1/2]-ℤ[1/2]}} = _≤ℤ[1/2]_

 Strict-Order-ℤ[1/2]-ℤ[1/2] : Strict-Order ℤ[1/2] ℤ[1/2]
 _<_ {{Strict-Order-ℤ[1/2]-ℤ[1/2]}} = _<ℤ[1/2]_

instance
 Order-ℤ[1/2]⁺-ℤ[1/2]⁺ : Order ℤ[1/2]⁺ ℤ[1/2]⁺
 _≤_ {{Order-ℤ[1/2]⁺-ℤ[1/2]⁺}} = _≤ℤ[1/2]⁺_

 Strict-Order-ℤ[1/2]⁺-ℤ[1/2]⁺ : Strict-Order ℤ[1/2]⁺ ℤ[1/2]⁺
 _<_ {{Strict-Order-ℤ[1/2]⁺-ℤ[1/2]⁺}} = _<ℤ[1/2]⁺_

record Dyadics : 𝓤₁ ̇ where
 field
  _ℤ[1/2]+_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-comm  : commutative _ℤ[1/2]+_
  ℤ[1/2]+-assoc : associative _ℤ[1/2]+_
  ℤ[1/2]-_      : ℤ[1/2] → ℤ[1/2]

 infix 20  ℤ[1/2]-_
 infixl 19 _ℤ[1/2]-_

 _ℤ[1/2]-_ : (p q : ℤ[1/2]) → ℤ[1/2]
 p ℤ[1/2]- q = p ℤ[1/2]+ (ℤ[1/2]- q)

 field
  ℤ[1/2]+-inv   : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x ℤ[1/2]+ y) ＝ 0ℤ[1/2]
  _ℤ[1/2]*_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]*-comm   : commutative _ℤ[1/2]*_
  ℤ[1/2]*-assoc  : associative _ℤ[1/2]*_
  ℤ[1/2]-mult-left-id : (x : ℤ[1/2]) → 1ℤ[1/2] ℤ[1/2]* x ＝ x
  ℤ[1/2]-negation-involutive : (x : ℤ[1/2]) → x ＝ ℤ[1/2]- (ℤ[1/2]- x)
  ℤ[1/2]-minus-dist : (x y : ℤ[1/2]) → (ℤ[1/2]- (x ℤ[1/2]+ y)) ＝ ((ℤ[1/2]- x) ℤ[1/2]+ (ℤ[1/2]- y))
  min : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  max : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-abs : ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-dist : (x y z : ℤ[1/2]) → (x ℤ[1/2]* z) ℤ[1/2]+ (y ℤ[1/2]* z) ＝ ((x ℤ[1/2]+ y) ℤ[1/2]* z)
  trans  : (x y z : ℤ[1/2]) → x < y → y < z → x < z
  trans' : (x y z : ℤ[1/2]) → x ≤ y → y ≤ z → x ≤ z
  no-min : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (y < x)
  no-max : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x < y)
  dense  : (x y : ℤ[1/2]) → (x < y) → Σ k ꞉ ℤ[1/2] , (x < k) × (k < y)
  trans<≤ : (x y z : ℤ[1/2]) → x < y → y ≤ z → x < z
  ≤-refl : (x : ℤ[1/2]) → x ≤ x
  <-is-≤ℤ[1/2] : (x y : ℤ[1/2]) → x < y → x ≤ y
  diff-positive : (x y : ℤ[1/2]) → x < y → 0ℤ[1/2] < (y ℤ[1/2]- x)
  diff-positive' : (x y : ℤ[1/2]) → x ≤ y → 0ℤ[1/2] ≤ (y ℤ[1/2]- x)
  <-swap : (x y : ℤ[1/2]) → x < y → (ℤ[1/2]- y) < (ℤ[1/2]- x)
  ≤-swap : (x y : ℤ[1/2]) → x ≤ y → (ℤ[1/2]- y) ≤ (ℤ[1/2]- x)
  ≤-split : (x y : ℤ[1/2]) → x ≤ y → x < y + (x ＝ y)
  <-swap-consequence : (x y z : ℤ[1/2]) → x < (y ℤ[1/2]+ z) → (x ℤ[1/2]- y) < z
  <-pos-mult : (x y z : ℤ[1/2]) → 0ℤ[1/2] < z → x < y → (x ℤ[1/2]* z) < (y ℤ[1/2]* z)
  <-pos-mult' : (x y : ℤ[1/2]) → 0ℤ[1/2] < x → 0ℤ[1/2] < y → 0ℤ[1/2] < (x ℤ[1/2]* y)
  ℤ[1/2]-minus-zero : 0ℤ[1/2] ＝ (ℤ[1/2]- 0ℤ[1/2])
  ℤ[1/2]<-+ : (x y : ℤ[1/2]) → 0ℤ[1/2] < y → x < (x ℤ[1/2]+ y)
  ℤ[1/2]<-+' : (x y z : ℤ[1/2]) → x < (y ℤ[1/2]+ z) → (x ℤ[1/2]- y) < z
  ℤ[1/2]<-neg : (x y : ℤ[1/2]) → 0ℤ[1/2] < y → (x ℤ[1/2]- y) < x
  ℤ[1/2]<-neg' : (x y z : ℤ[1/2]) → (x ℤ[1/2]- y) < z → x < (z ℤ[1/2]+ y)
  ℤ[1/2]<-rearrange : (x y z : ℤ[1/2]) → (x ℤ[1/2]+ y) < z → y < (z ℤ[1/2]- x)
  ℤ[1/2]-pos-abs : (x y : ℤ[1/2]) → x < y → y ℤ[1/2]- x ＝ ℤ[1/2]-abs (y ℤ[1/2]- x)
  ℤ[1/2]-pos-abs' : (x y : ℤ[1/2]) → x ≤ y → y ℤ[1/2]- x ＝ ℤ[1/2]-abs (y ℤ[1/2]- x)
  ℤ[1/2]≤-adding : (x y u v : ℤ[1/2]) → x ≤ y → u ≤ v → (x ℤ[1/2]+ u) ≤ (y ℤ[1/2]+ v)
  ℤ[1/2]<-adding : (x y u v : ℤ[1/2]) → x < y → u < v → (x ℤ[1/2]+ u) < (y ℤ[1/2]+ v)
  ℤ[1/2]<-+cancel : (x y z : ℤ[1/2]) → (z ℤ[1/2]+ x) < (z ℤ[1/2]+ y) → x < y
  ℤ[1/2]-te : (x y : ℤ[1/2]) → ℤ[1/2]-abs (x ℤ[1/2]+ y) ≤ (ℤ[1/2]-abs x ℤ[1/2]+ ℤ[1/2]-abs y)
  ℤ[1/2]<-to-abs : (x y : ℤ[1/2]) → ((ℤ[1/2]- y) < x) × (x < y) → ℤ[1/2]-abs x < y
  ℤ[1/2]-abs-lemma : (x y : ℤ[1/2]) → ℤ[1/2]-abs (x ℤ[1/2]- y) ＝ ℤ[1/2]-abs (y ℤ[1/2]- x)
  ℤ[1/2]-1/2-< : (x : ℤ[1/2]) → 0ℤ[1/2] < x → (1/2ℤ[1/2] ℤ[1/2]* x) < x
  normalise-< : ((k , p) : ℤ × ℤ) → normalise (k , p) < normalise ((k +pos 2) , p)
  normalise-≤ : ∀ n → ((k , p) : ℤ × ℤ) → normalise (k , p) ≤ normalise ((k +pos n) , p)
  normalise-≤2 : ∀ l r p → l ≤ r → normalise (l , p) ≤ normalise (r , p) 
  normalise-equality : ((k , p) : ℤ × ℤ) → normalise (pos 1 , predℤ p) ＝ normalise (k +pos 2 , p) ℤ[1/2]- normalise (k , p)
  ℤ[1/2]-ordering-property : (a b c d : ℤ[1/2]) → (a ℤ[1/2]- b) < (c ℤ[1/2]- d) → (a < c) + (d < b)
  normalise-succ : (z n : ℤ) → normalise (z , n) ≤ normalise (z +ℤ z , succℤ n)
  normalise-succ' : (z n : ℤ) → normalise (z , n) ＝ normalise (z +ℤ z , succℤ n)
  normalise-pred' : (z n : ℤ) → normalise (z , predℤ n) ＝ normalise (pos 2 ℤ* z , n)
  ℤ[1/2]<-positive-mult : (a b : ℤ[1/2]) → is-positive a → is-positive b → is-positive (a ℤ[1/2]* b)
  ℤ[1/2]-find-lower : ∀ ε → is-positive ε → Σ n ꞉ ℤ , normalise (pos 2 , n) < ε
  normalise-negation : ∀ a b c → normalise (a , c) ℤ[1/2]- normalise (b , c) ＝ normalise (a ℤ- b , c)
  from-normalise-≤-same-denom : (a b c : ℤ) → normalise (a , c) ≤ normalise (b , c) → a ≤ b

 metric : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
 metric p q = ℤ[1/2]-abs (p ℤ[1/2]- q)

 Bℤ[1/2] : (x y ε : ℤ[1/2]) → 0ℤ[1/2] < ε → 𝓤₀ ̇
 Bℤ[1/2] p q ε l = metric p q < ε

 field
  ℤ[1/2]-metric-neg : (x y ε : ℤ[1/2]) (l : 0ℤ[1/2] < ε) → metric x y < ε → metric (ℤ[1/2]- x) (ℤ[1/2]- y) < ε
  ℤ[1/2]-metric-comm : (x y ε : ℤ[1/2]) (l : 0ℤ[1/2] < ε) → Bℤ[1/2] x y ε l → Bℤ[1/2] y x ε l

 ℤ[1/2]<-≤ : (x y z : ℤ[1/2]) → x < y → y ≤ z → x < z
 ℤ[1/2]<-≤ x y z x<y y≤z with ≤-split y z y≤z
 ... | inl y<z = trans x y z x<y y<z
 ... | inr y=z = transport (x <_) y=z x<y

 ℤ[1/2]≤-< : (x y z : ℤ[1/2]) → x ≤ y → y < z → x < z
 ℤ[1/2]≤-< x y z x≤y y<z with ≤-split x y x≤y
 ... | inl x<y = trans x y z x<y y<z
 ... | inr x＝y = transport (_< z) (x＝y ⁻¹) y<z

 trans₂ : (w x y z : ℤ[1/2]) → w < x → x < y → y < z → w < z
 trans₂ w x y z w<x x<y y<z = trans w x z w<x (trans x y z x<y y<z)

 <-swap' : (x y : ℤ[1/2]) → (ℤ[1/2]- x) < (ℤ[1/2]- y) → y < x
 <-swap' x y l = transport₂ _<_ (ℤ[1/2]-negation-involutive y ⁻¹) (ℤ[1/2]-negation-involutive x ⁻¹) (<-swap (ℤ[1/2]- x) (ℤ[1/2]- y) l)

 0<1/2ℤ[1/2] : 0ℤ[1/2] < 1/2ℤ[1/2]
 0<1/2ℤ[1/2] = 0 , refl

 1/2ℤ[1/2]<1ℤ[1/2] : 1/2ℤ[1/2] < 1ℤ[1/2]
 1/2ℤ[1/2]<1ℤ[1/2] = 0 , refl

 0<1ℤ[1/2] : 0ℤ[1/2] < 1ℤ[1/2]
 0<1ℤ[1/2] = 0 , refl

 numerator-≤ : (((a , x) , l₁) ((b , y) , l₂) : ℤ[1/2])
             → x ＝ y → a ≤ b → ((a , x) , l₁) ≤ ((b , y) , l₂)
 numerator-≤ ((a , x) , l₁) ((b , y) , l₂) e l = transport (λ z → a ℤ* pos (2^ z) ≤ b ℤ* pos (2^ x)) e I
  where
   I : a ℤ* pos (2^ x) ≤ b ℤ* pos (2^ x)
   I = positive-multiplication-preserves-order' a b (pos (2^ x)) (power-of-pos-positive x) l

 numerator-≤' : (((a , x) , l₁) ((b , y) , l₂) : ℤ[1/2])
              → x ＝ y
              → ((a , x) , l₁) ≤ ((b , y) , l₂)
              → a ≤ b
 numerator-≤'((a , x) , l₁) ((b , y) , l₂) e l = γ
  where
   I : a ℤ* pos (2^ x) ≤ b ℤ* pos (2^ x)
   I = transport (λ z → a ℤ* pos (2^ z) ≤ b ℤ* pos (2^ x)) (e ⁻¹) l
   γ : a ≤ b
   γ = ℤ≤-ordering-right-cancellable a b (pos (2^ x)) (power-of-pos-positive x) I
 
 normalise-≤' : ((k , δ) : ℤ × ℕ) → ((m , ε) : ℤ × ℕ)
             → k ℤ* pos (2^ ε) ≤ m ℤ* pos (2^ δ)
             → normalise (k , pos δ) ≤ normalise (m , pos ε)
 normalise-≤' (k , δ) (m , ε) l with normalise-pos' k δ , normalise-pos' m ε
 ... | (n₁ , e₁) , (n₂ , e₂) = let (((k' , δ') , p) , ((m' , ε') , p')) = (normalise-pos k δ , normalise-pos m ε) in 
  ℤ≤-ordering-right-cancellable
   (k' ℤ* pos (2^ ε'))
    (m' ℤ* pos (2^ δ'))
     (pos (2^ (n₁ +ℕ n₂)))
      (power-of-pos-positive (n₁ +ℕ n₂))
       (transport₂ _≤_ (I k ε k' ε' n₁ n₂ (pr₁ (from-×-＝' e₁) ⁻¹) (pr₂ (from-×-＝' e₂) ⁻¹))
                       ((I m δ m' δ' n₂ n₁ (pr₁ (from-×-＝' e₂) ⁻¹) (pr₂ (from-×-＝' e₁) ⁻¹))
                        ∙ ap (λ z → m' ℤ* pos (2^ δ') ℤ* pos (2^ z)) (addition-commutativity n₂ n₁)) l)
   where
    k' = pr₁ (pr₁ (normalise-pos k δ))
    δ' = pr₂ (pr₁ (normalise-pos k δ))
    m' = pr₁ (pr₁ (normalise-pos m ε))
    ε' = pr₂ (pr₁ (normalise-pos m ε))
    I : (k : ℤ) (ε : ℕ) (k' : ℤ) (ε' : ℕ) (n₁ n₂ : ℕ) → k ＝ pos (2^ n₁) ℤ* k' → ε ＝ ε' +ℕ n₂ → k ℤ* pos (2^ ε) ＝ k' ℤ* pos (2^ ε') ℤ* pos (2^ (n₁ +ℕ n₂))
    I k ε k' ε' n₁ n₂ e₁ e₂ =
        k ℤ* pos (2^ ε)                            ＝⟨ ap (_ℤ* pos (2^ ε)) e₁ ⟩
        pos (2^ n₁) ℤ* k' ℤ* pos (2^ ε)             ＝⟨ ap (_ℤ* pos (2^ ε)) (ℤ*-comm (pos (2^ n₁)) k') ⟩
        k' ℤ* pos (2^ n₁) ℤ* pos (2^ ε)             ＝⟨ ap (λ z → k' ℤ* pos (2^ n₁) ℤ* pos (2^ z)) e₂ ⟩
        k' ℤ* pos (2^ n₁) ℤ* pos (2^ (ε' +ℕ n₂))    ＝⟨ ℤ*-assoc k' (pos (2^ n₁)) (pos (2^ (ε' +ℕ n₂))) ⟩
        k' ℤ* (pos (2^ n₁) ℤ* pos (2^ (ε' +ℕ n₂)))  ＝⟨ ap (k' ℤ*_) (pos-multiplication-equiv-to-ℕ (2^ n₁) (2^ (ε' +ℕ n₂))) ⟩
        k' ℤ* pos ((2^ n₁) ℕ* 2^ (ε' +ℕ n₂))       ＝⟨ ap (λ z →  k' ℤ* pos ((2^ n₁) ℕ* z)) (prod-of-powers 2 ε' n₂ ⁻¹) ⟩
        k' ℤ* pos (2^ n₁ ℕ* (2^ ε' ℕ* 2^ n₂))      ＝⟨ ap (λ z → k' ℤ* pos z) (mult-associativity (2^ n₁) (2^ ε') (2^ n₂) ⁻¹) ⟩
        k' ℤ* pos (2^ n₁ ℕ* 2^ ε' ℕ* 2^ n₂)        ＝⟨ ap (λ z → k' ℤ* pos (z ℕ* 2^ n₂)) (mult-commutativity (2^ n₁) (2^ ε')) ⟩
        k' ℤ* pos (2^ ε' ℕ* 2^ n₁ ℕ* 2^ n₂)        ＝⟨ ap (λ z → k' ℤ* pos z) (mult-associativity (2^ ε') (2^ n₁) (2^ n₂)) ⟩
        k' ℤ* pos (2^ ε' ℕ* (2^ n₁ ℕ* 2^ n₂))      ＝⟨ ap (λ z → k' ℤ* z) (pos-multiplication-equiv-to-ℕ (2^ ε') (2^ n₁ ℕ* 2^ n₂) ⁻¹) ⟩
        k' ℤ* (pos (2^ ε') ℤ* pos (2^ n₁ ℕ* 2^ n₂)) ＝⟨ ap (λ z → k' ℤ* (pos (2^ ε') ℤ* pos z)) (prod-of-powers 2 n₁ n₂) ⟩
        k' ℤ* (pos (2^ ε') ℤ* pos (2^ (n₁ +ℕ n₂)))  ＝⟨ ℤ*-assoc k' (pos (2^ ε')) (pos (2^ (n₁ +ℕ n₂))) ⁻¹ ⟩
        k' ℤ* pos (2^ ε') ℤ* pos (2^ (n₁ +ℕ n₂))    ∎

 normalise-≤'' : ((k , δ) : ℤ × ℕ) → ((m , ε) : ℤ × ℕ)
             → k ℤ* pos (2^ (succ δ)) ≤ m ℤ* pos (2^ (succ ε))
             → normalise (k , negsucc δ) ≤ normalise (m , negsucc ε)
 normalise-≤'' (k , δ) (m , ε) with (from-×-＝' (normalise-neg' k δ) , from-×-＝' (normalise-neg' m ε))
 ... | ((e₁ , e₂) , e₃ , e₄) = transport₂ _≤_
                                (ℤ*-comm k (pos (2^ (succ δ))) ∙ ap₂ (λ z z' → z ℤ* pos (2^ z')) (e₁ ⁻¹) (e₄ ⁻¹))
                                 (ℤ*-comm m (pos (2^ (succ ε))) ∙ ap₂ (λ z z' → z ℤ* pos (2^ z')) (e₃ ⁻¹) (e₂ ⁻¹))


```

```
data Vec (A : 𝓤 ̇ ) : ℕ → 𝓤 ̇  where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

pattern [_] x = x ∷ []

vec-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {n : ℕ} → (A → B) → Vec A n → Vec B n
vec-map f [] = []
vec-map f (x ∷ v) = f x ∷ vec-map f v
```

