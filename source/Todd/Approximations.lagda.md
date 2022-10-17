
```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
open import Integers.Integers
open import Integers.Addition renaming (_+_ to _ℤ+_;  _-_ to _ℤ-_)
open import Integers.Negation renaming (-_ to ℤ-_ )
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
                                    
open import Naturals.Order renaming (max to ℕmax)

𝔻 = ℤ[1/2]

is-odcs : (ℤ → ℤ[1/2] × ℤ[1/2]) → 𝓤₀  ̇  
is-odcs ζ = ((n : ℤ) → pr₁ (ζ n) ≤ℤ[1/2] pr₂ (ζ n))
          × ((ϵ : 𝔻) → Σ n ꞉ ℤ , ((pr₂ (ζ n) - pr₁ (ζ n)) ≤ℤ[1/2] ϵ))
          × ((n : ℤ) → (pr₁ (ζ n) ≤ℤ[1/2] pr₁ (ζ (succℤ n)))
                     × (pr₂ (ζ (succℤ n)) ≤ℤ[1/2] pr₂ (ζ n)))

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
  inhabited-l = ∣ (pr₁ (ζ (pos 0)) - ((pos 1 , 0) , (inl refl)))
              , {!!} ∣
  inhabited-r : inhabited-right R
  inhabited-r = {!!}
  rounded-l : rounded-left L
  rounded-l = {!!}
  rounded-r : rounded-right R
  rounded-r = {!!}
  is-disjoint : disjoint L R
  is-disjoint = {!!}
  is-located : located L R
  is-located = {!!}

η η⁺² : ℤ × ℤ → ℤ[1/2]
η   = normalise
η⁺² (k , p) = normalise (k +pos 2 , p)

η[_,_] : ℤ → ℤ → ℤ[1/2] × ℤ[1/2]
η[ k , p ] = η (k , p) , η⁺² (k , p)



```
