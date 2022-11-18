
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

module NewFile
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
 where

open import RationalsDyadic fe renaming (1/2ℤ[1/2] to 1/2)
open import DyadicReals pe pt fe
open import TBRFunctions pt fe pe sq
open import TernaryBoehmReals pt fe pe sq hiding (ι ; _≤_≤_)
open import TBRDyadicReals pt fe pe sq
open PropositionalTruncation pt

open OrderProperties DyOrPr
open DyadicProperties Dp renaming (_ℤ[1/2]+_ to _+_ ; ℤ[1/2]-_ to -_ ; _ℤ[1/2]-_ to _-_ ; _ℤ[1/2]*_ to _*_)
                                    
open import Naturals.Order renaming (max to ℕmax) hiding (≤-refl ; ≤-trans)

nested converges : ℤ → ℤ[1/2] × ℤ[1/2] → {!!} ̇
nested    ζ = {!!}
converges ζ = {!!}

l r : ℤ × ℤ → ℤ[1/2]
l (k , i) = normalise (k        , i)
r (k , i) = normalise (k +pos 2 , i)

variable-width-interval : ℤ × ℤ × ℤ → ℤ[1/2] × ℤ[1/2]
variable-width-interval (k , c , i) = l (k , i) , l (c , i)

specific-width-interval :     ℤ × ℤ → ℤ[1/2] × ℤ[1/2]
specific-width-interval (k     , i) = l (k , i) , r (k , i)

seq-of-vw-intervals : (ℤ → (ℤ × ℤ × ℤ)) → ℤ → ℤ[1/2] × ℤ[1/2]
seq-of-vw-intervals = variable-width-interval ∘_

seq-of-sw-intervals : (ℤ →      ℤ × ℤ)  → ℤ → ℤ[1/2] × ℤ[1/2]
seq-of-sw-intervals = specific-width-interval ∘_

vw-nested vw-converges : (ℤ → (ℤ × ℤ × ℤ)) → {!!} ̇ 
vw-nested    ζ = {!!}
vw-converges ζ = {!!}

_≡_ = Id

is-normalised    : (ℤ → ℤ × ℤ) → 𝓤₀ ̇ 
is-normalised    ζ = (n : ℤ) → pr₂ (ζ n) ≡ n

is-prenormalised : (ℤ → ℤ × ℤ) → 𝓤₀ ̇
is-prenormalised ζ = (n : ℤ) → pr₂ (ζ n) ≥ n

normalised-implies-prenormalised : (ζ : ℤ → ℤ × ℤ) → is-normalised ζ → is-prenormalised ζ 
normalised-implies-prenormalised ζ ρ n = 0 , (ρ n ⁻¹)


