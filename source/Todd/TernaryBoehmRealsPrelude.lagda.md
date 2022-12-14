```agda
{-# OPTIONS --without-K --exact-split #-}

open import UF.FunExt
open import MLTT.Spartan

module Todd.TernaryBoehmRealsPrelude where

open import MLTT.Two-Properties hiding (zero-is-not-one)
open import Naturals.Order
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Integers.Type
open import Integers.Order
open import Integers.Addition renaming (_+_ to _+ℤ_ ; _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_  to  −ℤ_)
open import UF.Subsingletons
open import Naturals.Order
open import NotionsOfDecidability.DecidableAndDetachable
open import Notation.Order

succ-lc : (x y : ℕ) → succ x ＝ succ y → x ＝ y
succ-lc x x refl = refl

ℕ-is-discrete : (x y : ℕ) → decidable (x ＝ y)
ℕ-is-discrete zero zero = inl refl
ℕ-is-discrete zero (succ y) = inr (λ ())
ℕ-is-discrete (succ x) zero = inr (λ ())
ℕ-is-discrete (succ x) (succ y)
 = Cases (ℕ-is-discrete x y)
     (inl ∘ ap succ)
     (inr ∘ λ f g → f (succ-lc x y g))

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
negsucc x /2' = −ℤ (pos (succ x /2))

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
x −ℤ y = x +ℤ (−ℤ y)

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

ye : (a b c : ℤ) → ((n , _) : a ≤ c) → a ≤ b → ((n₂ , _) : b ≤ c) → n₂ <ℕ succ n
ye a b c (n , q) (n₁ , r) (n₂ , s)
 = transport (n₂ ≤ℕ_) (ne a b c (n , q) (n₁ , r) (n₂ , s)) (≤-+' n₁ n₂)

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

negation-preserves-parity : (x : ℤ) → even x → even (−ℤ x)
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
even-lemma-neg x even-x = (−ℤ pos (succ x /2)) −ℤ pos (succ x /2)  ＝⟨ negation-dist (pos (succ x /2)) (pos (succ x /2)) ⟩
                          −ℤ (pos (succ x /2) +ℤ pos (succ x /2)) ＝⟨ ap −ℤ_ (even-lemma-pos (succ x) (negation-preserves-parity (negsucc x) even-x)) ⟩
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
                  (−ℤ pos (succ x)) −ℤ pos (succ x)  ＝⟨ negation-dist (pos (succ x)) (pos (succ x)) ⟩
                  −ℤ (pos (succ x) +ℤ pos (succ x)) ＝⟨ refl ⟩
                  −ℤ succℤ (pos (succ x) +ℤ pos x)  ＝⟨ ap (λ z → −ℤ succℤ z) (distributivity-pos-addition (succ x) x) ⟩
                  −ℤ succℤ (pos (succ x +ℕ x))       ＝⟨ refl ⟩
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
                         −ℤ pos (succ (x +ℕ succ x) /2) ＝⟨ ap (λ z → −ℤ pos (z /2)) (succ-left x (succ x) ⁻¹) ⟩
                         −ℤ pos ((succ x +ℕ succ x) /2) ＝⟨ ap (λ z → −ℤ pos z) (div-by-two' (succ x)) ⟩
                         negsucc x ∎

```
