```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
open import Integers.Integers
open import Integers.Addition renaming (_+_ to _ℤ+_;  _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_ )
open import Integers.Order
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Quotient
open import UF.Powerset hiding (𝕋)

module Todd.Approximations2
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
 where

open import Todd.RationalsDyadic fe renaming (1/2ℤ[1/2] to 1/2)
open import Todd.DyadicReals pe pt fe
open import Todd.TBRFunctions pt fe pe sq
open import Todd.TernaryBoehmReals pt fe pe sq hiding (ι ; _≤_≤_)
open import Todd.TBRDyadicReals pt fe pe sq hiding (⟦_⟧)
open PropositionalTruncation pt

open OrderProperties DyOrPr
open DyadicProperties Dp renaming (_ℤ[1/2]+_ to _+_ ; ℤ[1/2]-_ to -_ ; _ℤ[1/2]-_ to _-_ ; _ℤ[1/2]*_ to _*_)
                                    
open import Naturals.Order renaming (max to ℕmax) hiding (≤-refl ; ≤-trans)

𝔻 : 𝓤₀ ̇
𝔻 = ℤ × ℤ

η η⁺² : 𝔻 → ℤ[1/2]
η = normalise
η⁺² (k , p) = normalise (k ℤ+ pos 2 , p)

η[_] : 𝔻 → ℤ[1/2] × ℤ[1/2]
η[ (k , p) ] = η (k , p) , η⁺² (k , p)

instance
 canonical-map-𝔻-to-ℤ[1/2] : Canonical-Map 𝔻 ℤ[1/2]
 ι {{canonical-map-𝔻-to-ℤ[1/2]}} = η

ld rd : (ℤ → 𝔻 × 𝔻) → (n : ℤ) → ℤ[1/2]
ld ζ n = ι (pr₁ (ζ n))
rd ζ n = ι (pr₂ (ζ n))

```
Sequences

```agda

is-odcs : (ℤ → 𝔻 × 𝔻) → 𝓤₀ ̇
is-odcs ζ = ((n : ℤ) → ld ζ n ≤ rd ζ n)
          × ((ε : ℤ[1/2]) → (Σ n ꞉ ℤ , (rd ζ n - ld ζ n) ≤ ε))
          × ((n : ℤ) → (ld ζ n ≤ ld ζ (succℤ n))
                     × (rd ζ (succℤ n) ≤ rd ζ n))

||_|| : (ℤ → 𝔻) → (ℤ → 𝔻 × 𝔻)
|| ζ || n = (ζ n) , (pr₁ (ζ n) ℤ+ pos 2 , pr₂ (ζ n))

is-gbr : (ℤ → 𝔻) → 𝓤₀  ̇
is-gbr γ = ((ε : ℤ[1/2]) → Σ n ꞉ ℤ , (η (pos 1 , predℤ (pr₂ (γ n))) ≤ ε))
         × ((n : ℤ) → (η (γ n) ≤ η (γ (succℤ n))) × (η⁺² (γ (succℤ n)) ≤ η⁺² (γ n)))

𝔾-gives-odcs : (ξ : ℤ → 𝔻) → is-gbr ξ → is-odcs || ξ ||
𝔾-gives-odcs ξ (ξc₁ , ξc₂) = c₁ , c₂ , ξc₂
 where
  c₁ : (n : ℤ) → (ld || ξ || n) ≤ (rd || ξ || n)
  c₁ n = <-is-≤ℤ[1/2] (ld || ξ || n) (rd || ξ || n) (normalise-< (ξ n))
  c₂ : (ε : ℤ[1/2]) → Σ n ꞉ ℤ , ((rd || ξ || n) - (ld || ξ || n)) ≤ ε
  c₂ ε with ξc₁ ε
  ... | (n , l) = n , (transport (_≤ ε) (normalise-equality (ξ n)) l)

<_> : 𝕋 → (ℤ → 𝔻)
< χ , b > n = χ n , n

<>-is-gbr-lemma₁ : ((χ , b) : 𝕋) → (n : ℤ) → normalise (χ n , n) ≤ normalise (χ (succℤ n) , (succℤ n))
<>-is-gbr-lemma₁ = {!easy !}

<>-is-gbr-lemma₂ : ((χ , b) : 𝕋) → (n : ℤ) → normalise (succℤ (succℤ (χ (succℤ n))) , (succℤ n)) ≤ normalise (succℤ (succℤ (χ n)) , n)
<>-is-gbr-lemma₂ = {!easy!}

normalise-ε : ((χ , b) : 𝕋) → (ε : ℤ[1/2]) → Σ n ꞉ ℤ , (normalise (pos 1 , predℤ (pr₂ (< χ , b > n))) ≤ ε)
normalise-ε = {!should be easy!}

<>-is-gbr : (χ : 𝕋) → is-gbr < χ >
<>-is-gbr χ = normalise-ε χ , (λ n → <>-is-gbr-lemma₁ χ n
                                   , <>-is-gbr-lemma₂ χ n)

<>-gives-odcs : (χ : 𝕋) → is-odcs || < χ > ||
<>-gives-odcs χ = 𝔾-gives-odcs < χ > (<>-is-gbr χ)

is-odcs-c₃-lemma-ns : (ζ : (ℤ → 𝔻 × 𝔻)) → ((c₁ , c₂ , c₃) : is-odcs ζ)
                    → (n₁ n₂ : ℤ) → (k : ℕ) → n₁ ℤ+ pos k ＝ n₂ → (ld ζ n₁ ≤ℤ[1/2] ld ζ n₂) × (rd ζ n₂ ≤ℤ[1/2] rd ζ n₁)
is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ n₂ 0        e = transport (λ - → ld ζ n₁ ≤ ld ζ -) e (≤-refl (ld ζ n₁))
                                                      , transport (λ - → rd ζ - ≤ rd ζ n₁) e (≤-refl (rd ζ n₁))
is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ n₂ 1 e = transport (λ - → ld ζ n₁ ≤ ld ζ -) e (pr₁ (c₃ n₁))
                                               , transport (λ - → rd ζ - ≤ rd ζ n₁) e (pr₂ (c₃ n₁))                                             
is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ n₂ (succ (succ k)) e with (is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ (predℤ n₂) (succ k) (predsuccℤ (succℤ (n₁ +pos k)) ⁻¹ ∙ ap predℤ e))
... | (l₁ , l₂) = trans' (ld ζ n₁) (ld ζ (predℤ n₂)) (ld ζ n₂) l₁ (transport (λ - → ld ζ (predℤ n₂) ≤ℤ[1/2] ld ζ -) (succpredℤ n₂) (pr₁ (c₃ (predℤ n₂))))
                , trans' (rd ζ n₂) (rd ζ (predℤ n₂)) (rd ζ n₁) (transport (λ - → rd ζ - ≤ℤ[1/2] rd ζ (predℤ n₂)) (succpredℤ n₂) (pr₂ (c₃ (predℤ n₂)))) l₂

is-odcs-c₃-lemma : (ζ : (ℤ → 𝔻 × 𝔻)) → ((c₁ , c₂ , c₃) : is-odcs ζ)
                 → (n₁ n₂ : ℤ) → n₁ ≤ n₂ → (ld ζ n₁ ≤ℤ[1/2] ld ζ n₂) × (rd ζ n₂ ≤ℤ[1/2] rd ζ n₁)
is-odcs-c₃-lemma ζ c n₁ n₂ (k , e) = is-odcs-c₃-lemma-ns ζ c n₁ n₂ k e

⦅_⦆ : Σ ζ ꞉ (ℤ → 𝔻 × 𝔻) , is-odcs ζ → ℝ-d
⦅ ζ , (c₁ , c₂ , c₃) ⦆
 = (L , R)
 , inhabited-l , inhabited-r
 , rounded-l   , rounded-r
 , is-disjoint , is-located
 where
  L R : 𝓟 ℤ[1/2]
  L p = (∃ n ꞉ ℤ , (p <ℤ[1/2] ld ζ n)) , ∃-is-prop
  R q = (∃ n ꞉ ℤ , (rd ζ n <ℤ[1/2] q)) , ∃-is-prop
  inhabited-l : inhabited-left L
  inhabited-l = ∣ (ld ζ (pos 0) - 1ℤ[1/2])
              , ∣ pos 0 , ℤ[1/2]<-neg (ld ζ (pos 0)) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  inhabited-r : inhabited-right R
  inhabited-r = ∣ (rd ζ (pos 0) + 1ℤ[1/2])
             , ∣ pos 0  , ℤ[1/2]<-+ (rd ζ (pos 0)) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  rounded-l : rounded-left L
  rounded-l p = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , (p <ℤ[1/2] ld ζ n) → ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] ld ζ n'))
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , (p <ℤ[1/2] ld ζ n) → Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] ld ζ n'))
      I (n , p<ζn) = let (p' , p<p' , p'<ζn) = dense p (ld ζ n) p<ζn
                     in p' , (p<p' , ∣ n , p'<ζn ∣)
    rtl : ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] ld ζ n))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] ld ζ n)
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] ld ζ n))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] ld ζ n)
      I (p' , p<p' , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (p' <ℤ[1/2] ld ζ n) → Σ n ꞉ ℤ , (p <ℤ[1/2] ld ζ n)
        II (n  , p'<ζn) = n , (trans p p' (ld ζ n) p<p' p'<ζn)
      
  rounded-r : rounded-right R
  rounded-r q = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , rd ζ n < q → ∃ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , rd ζ n < q → Σ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
      I (n , ζn<q) = let (q' , ζn<q' , q'<q) = dense (rd ζ n) q ζn<q
                     in q' , (q'<q , ∣ n , ζn<q' ∣)
    rtl : ∃ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
      I (q' , q'<q , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (rd ζ n < q') → Σ n ꞉ ℤ , (rd ζ n <ℤ[1/2] q)
        II (n , ζ<q') = n , (trans (rd ζ n) q' q ζ<q' q'<q)
  
  is-disjoint : disjoint L R
  is-disjoint p q (tp<x , tx<q) = ∥∥-rec (<ℤ[1/2]-is-prop p q) I (binary-choice tp<x tx<q)
   where
    I : (Σ n ꞉ ℤ , (p <ℤ[1/2] ld ζ n)) × (Σ n' ꞉ ℤ , (rd ζ n' <ℤ[1/2] q))
      → p <ℤ[1/2] q
    I ((n , p<l) , (n' , r<q)) with ℤ-dichotomous n n'
    ... | inl n≤n' = let p<l' = ℤ[1/2]<-≤ p (ld ζ n) (ld ζ n') p<l (pr₁ (is-odcs-c₃-lemma ζ (c₁ , c₂ , c₃) n n' n≤n'))
                         l<q' = ℤ[1/2]≤-< (ld ζ n') (rd ζ n') q (c₁ n') r<q
                     in trans p (ld ζ n') q p<l' l<q'
    ... | inr n'≤n = let p<r' = ℤ[1/2]<-≤ p (ld ζ n) (rd ζ n) p<l (c₁ n)
                         r<q' = ℤ[1/2]≤-< (rd ζ n) (rd ζ n') q (pr₂ (is-odcs-c₃-lemma ζ (c₁ , c₂ , c₃) n' n n'≤n)) r<q
                     in trans p (rd ζ n) q p<r' r<q'
 
  is-located : located L R
  is-located p q p<q = I (c₂ (1/2 * (q - p)))
   where
    0<ε : 0ℤ[1/2] < (1/2 * (q - p))
    0<ε = <-pos-mult' 1/2 (q - p) 0<1/2ℤ[1/2] (diff-positive p q p<q)
    I : (Σ n ꞉ ℤ , ((rd ζ n - ld ζ n) ≤ℤ[1/2] (1/2 * (q - p)))) → (L p holds) ∨ (R q holds)
    I (n , l₁) = II (ℤ[1/2]-ordering-property (rd ζ n) (ld ζ n) q p l₂)
     where
      l₂ :(rd ζ n - ld ζ n) < (q - p)
      l₂ = ℤ[1/2]≤-< (rd ζ n - ld ζ n) (1/2 * (q - p)) (q - p) l₁ (ℤ[1/2]-1/2-< (q - p) (diff-positive p q p<q))
      II : rd ζ n < q ∔ p < ld ζ n → (L p holds) ∨ (R q holds)
      II (inl ζ<q) = ∣ inr ∣ n , ζ<q ∣ ∣
      II (inr p<ζ) = ∣ inl ∣ n , p<ζ ∣ ∣

⟦_⟧ : 𝕋 → ℝ-d
⟦ χ ⟧ = ⦅ || < χ > || , <>-gives-odcs χ ⦆

is-prenormalised : (ℤ → 𝔻) → 𝓤₀ ̇
is-prenormalised ζ = Σ κ ꞉ (ℤ → ℤ) , ((n : ℤ) → n ≤ pr₂ ((ζ ∘ κ) n)
                                              × (κ n ≤ κ (succℤ n))
                                              × (n ≤ κ n))

prenorm : (χ : ℤ → 𝔻) → is-prenormalised χ → (ℤ → 𝔻)
prenorm χ (κ , _) = χ ∘ κ

prenorm-is-gbr : (χ : ℤ → 𝔻)
               → (ipχ : is-prenormalised χ)
               → is-gbr (prenorm χ ipχ)
prenorm-is-gbr = {!!}

prenorm-is-odcs : (χ : ℤ → 𝔻)
                → (ipχ : is-prenormalised χ)
                → is-odcs || prenorm χ ipχ ||
prenorm-is-odcs χ ipχ = 𝔾-gives-odcs (prenorm χ ipχ) (prenorm-is-gbr χ ipχ)

prenorm-same-real : (χ : ℤ → 𝔻)
                  → (ioχ : is-odcs || χ ||)
                  → (ipχ : is-prenormalised χ)
                  → ⦅ || χ || , ioχ ⦆ ＝ ⦅ || prenorm χ ipχ || , prenorm-is-odcs χ ipχ ⦆
prenorm-same-real χ ioχ ipχ = {!!}

is-normalised : (χ : ℤ → 𝔻) → 𝓤₀ ̇
is-normalised χ = (n : ℤ) → pr₂ (χ n) ＝ n

norm : (χ : ℤ → 𝔻) → (ℤ → 𝔻)
norm χ n = rec (pr₁ (χ n)) upRight (abs (n ℤ- pr₂ (χ n))) , n

norm-is-normalised : (χ : ℤ → 𝔻) → is-normalised (norm χ)
norm-is-normalised χ n = refl

norm-is-prenormalised : (χ : ℤ → 𝔻) → is-prenormalised (norm χ)
norm-is-prenormalised χ = id , (λ n → (0 , refl) , (1 , refl) , (0 , refl))

norm-is-odcs : (χ : ℤ → 𝔻)
             → is-odcs || norm χ ||
norm-is-odcs χ = prenorm-is-odcs (norm χ) (norm-is-prenormalised χ)

norm-same-real : (χ : ℤ → 𝔻)
               → (inχ : is-odcs || χ ||)
               → ⦅ || χ || , inχ ⦆ ＝ ⦅ || norm χ || , norm-is-odcs χ ⦆
norm-same-real = {!!}

toTB : (Σ χ ꞉ (ℤ → 𝔻) , is-normalised χ) → 𝕋
toTB (χ , inχ) = {!!}

toTB-same-real : ((χ , inχ) : Σ is-normalised)
               → (ioχ : is-odcs || χ ||)
               → ⟦ toTB (χ , inχ) ⟧ ＝ ⦅ || χ || , ioχ ⦆
toTB-same-real = {!!}

open import Todd.BuildingBlocks pt fe pe sq

record Approximations : 𝓤 ̇ where
 field
  n : ℕ
  C : Collection n
 open Collection C

 F' : Vec (Σ is-odcs) n → ℤ → ℤ[1/2] × ℤ[1/2]
 F' ζs n = (L (vec-map (λ (ζ , odcs) → {!!}) ζs))
         , (R (vec-map (λ (ζ , odcs) → {!!}) ζs))

```
