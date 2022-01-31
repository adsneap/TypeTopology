Tom de Jong, early January 2022.

TODO: Describe contents.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-FunExt
open import UF-PropTrunc

open import UF-Subsingletons

module DcpoBases
        (pt : propositional-truncations-exist)
        (pe : Prop-Ext)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF-Base hiding (_≈_)
open import UF-Equiv
open import UF-EquivalenceExamples


open import UF-Subsingletons-FunExt

open import Dcpo pt fe 𝓥
open import DcpoContinuous pt fe 𝓥
open import DcpoMiscelanea pt fe 𝓥
open import DcpoWayBelow pt fe 𝓥

open import UF-Size hiding (is-small ; is-locally-small)


-- TODO: Move elsewhere
module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {I : 𝓦 ̇  } {J : 𝓦' ̇  }
        (ρ : I ≃ J)
        (α : I → ⟨ 𝓓 ⟩)
       where

 reindexed-family : J → ⟨ 𝓓 ⟩
 reindexed-family = α ∘ ⌜ ρ ⌝⁻¹

 reindexed-family-is-directed : is-Directed 𝓓 α
                              → is-Directed 𝓓 reindexed-family
 reindexed-family-is-directed δ = J-inh , β-semidirected
  where
   J-inh : ∥ J ∥
   J-inh = ∥∥-functor ⌜ ρ ⌝ (inhabited-if-Directed 𝓓 α δ)
   β : J → ⟨ 𝓓 ⟩
   β = reindexed-family
   β-semidirected : is-semidirected (underlying-order 𝓓) β
   β-semidirected j₁ j₂ =
    ∥∥-functor r (semidirected-if-Directed 𝓓 α δ (⌜ ρ ⌝⁻¹ j₁) (⌜ ρ ⌝⁻¹ j₂))
     where
      r : (Σ i ꞉ I , (β j₁ ⊑⟨ 𝓓 ⟩ α i) × (β j₂ ⊑⟨ 𝓓 ⟩ α i))
        → (Σ j ꞉ J , (β j₁ ⊑⟨ 𝓓 ⟩ β j) × (β j₂ ⊑⟨ 𝓓 ⟩ β j))
      r (i , l₁ , l₂) = (⌜ ρ ⌝ i
                        , (β j₁                    ⊑⟨ 𝓓 ⟩[ l₁ ]
                           α i                     ⊑⟨ 𝓓 ⟩[ k ]
                           (α ∘ ⌜ ρ ⌝⁻¹ ∘ ⌜ ρ ⌝) i ∎⟨ 𝓓 ⟩)
                        , (β j₂                    ⊑⟨ 𝓓 ⟩[ l₂ ]
                           α i                     ⊑⟨ 𝓓 ⟩[ k ]
                           (α ∘ ⌜ ρ ⌝⁻¹ ∘ ⌜ ρ ⌝) i ∎⟨ 𝓓 ⟩))
       where
        k = ≡-to-⊑ 𝓓
             (ap α ((inverses-are-retractions ⌜ ρ ⌝ (⌜⌝-is-equiv ρ) i) ⁻¹))

 reindexed-family-sup : (x : ⟨ 𝓓 ⟩)
                      → is-sup (underlying-order 𝓓) x α
                      → is-sup (underlying-order 𝓓) x (reindexed-family)
 reindexed-family-sup x x-is-sup = ub , lb-of-ubs
  where
   β : J → ⟨ 𝓓 ⟩
   β = reindexed-family
   ub : is-upperbound (underlying-order 𝓓) x β
   ub i = sup-is-upperbound (underlying-order 𝓓) x-is-sup (⌜ ρ ⌝⁻¹ i)
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓓) x β
   lb-of-ubs y y-is-ub = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
                          x-is-sup y lemma
    where
     lemma : is-upperbound (underlying-order 𝓓) y α
     lemma i = α i         ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
               β (⌜ ρ ⌝ i) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
               y           ∎⟨ 𝓓 ⟩
      where
       ⦅1⦆ = ≡-to-⊑ 𝓓
             (ap α (inverses-are-retractions ⌜ ρ ⌝ (⌜⌝-is-equiv ρ) i) ⁻¹)
       ⦅2⦆ = y-is-ub (⌜ ρ ⌝ i)


module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
       where

 ↡ᴮ : ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ↡ᴮ x = Σ b ꞉ B , β b ≪⟨ 𝓓 ⟩ x

 ↡ι : (x : ⟨ 𝓓 ⟩) → ↡ᴮ x → ⟨ 𝓓 ⟩
 ↡ι x = β ∘ pr₁

 record is-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   ≪ᴮ-is-small : (x : ⟨ 𝓓 ⟩) → ((b : B) → is-small (β b ≪⟨ 𝓓 ⟩ x))
   ↡ᴮ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↡ι x)
   ↡ᴮ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↡ι x)

  _≪ᴮₛ_ : (b : B) (x : ⟨ 𝓓 ⟩) → 𝓥 ̇
  b ≪ᴮₛ x = pr₁ (≪ᴮ-is-small x b)

  ≪ᴮₛ-≃-≪ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ≪ᴮₛ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
  ≪ᴮₛ-≃-≪ᴮ {b} {x} = pr₂ (≪ᴮ-is-small x b)

  ↡ᴮₛ : ⟨ 𝓓 ⟩ → 𝓥 ̇
  ↡ᴮₛ x = Σ b ꞉ B , (b ≪ᴮₛ x)

  ↡ιₛ : (x : ⟨ 𝓓 ⟩) → ↡ᴮₛ x → ⟨ 𝓓 ⟩
  ↡ιₛ x = β ∘ pr₁

  ↡ᴮₛ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↡ιₛ x)
  ↡ᴮₛ-is-directed x = reindexed-family-is-directed 𝓓
                       (Σ-cong (λ b → ≃-sym ≪ᴮₛ-≃-≪ᴮ)) (↡ι x) (↡ᴮ-is-directed x)

  ↡ᴮₛ-∐-≡ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↡ᴮₛ-is-directed x) ≡ x
  ↡ᴮₛ-∐-≡ x = antisymmetry 𝓓 (∐ 𝓓 (↡ᴮₛ-is-directed x)) x ⦅1⦆ ⦅2⦆
   where
    ⦅1⦆ : ∐ 𝓓 (↡ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
    ⦅1⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 (↡ᴮₛ-is-directed x) x
          (λ (b , u) → sup-is-upperbound (underlying-order 𝓓) (↡ᴮ-is-sup x)
                        (b , (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ u)))
    ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↡ᴮₛ-is-directed x)
    ⦅2⦆ = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (↡ᴮ-is-sup x)
          (∐ 𝓓 (↡ᴮₛ-is-directed x))
          (λ (b , v) → ∐-is-upperbound 𝓓 (↡ᴮₛ-is-directed x)
                        (b , (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ v)))

  ↡ᴮₛ-∐-⊑ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↡ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
  ↡ᴮₛ-∐-⊑ x = ≡-to-⊑ 𝓓 (↡ᴮₛ-∐-≡ x)

  ↡ᴮₛ-∐-⊒ : (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↡ᴮₛ-is-directed x)
  ↡ᴮₛ-∐-⊒ x = ≡-to-⊑ 𝓓 ((↡ᴮₛ-∐-≡ x) ⁻¹)

  ↡ᴮₛ-way-below : (x : ⟨ 𝓓 ⟩) (b : ↡ᴮₛ x) → ↡ιₛ x b ≪⟨ 𝓓 ⟩ x
  ↡ᴮₛ-way-below x (b , u) = ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ u



 module _
         (sb : is-small-basis)
        where

  open is-small-basis sb

  structurally-continuous-if-equiped-with-small-basis : structurally-continuous 𝓓
  structurally-continuous-if-equiped-with-small-basis = record {
    index-of-approximating-family     = ↡ᴮₛ ;
    approximating-family              = ↡ιₛ ;
    approximating-family-is-directed  = ↡ᴮₛ-is-directed ;
    approximating-family-is-way-below = ↡ᴮₛ-way-below ;
    approximating-family-∐-≡          = ↡ᴮₛ-∐-≡
   }

  ⊑-in-terms-of-≪ᴮ : {x y : ⟨ 𝓓 ⟩}
                   → (x ⊑⟨ 𝓓 ⟩ y) ≃ (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y)
  ⊑-in-terms-of-≪ᴮ {x} {y} =
   logically-equivalent-props-are-equivalent
    (prop-valuedness 𝓓 x y)
    (Π₂-is-prop fe (λ b u → ≪-is-prop-valued 𝓓)) ⦅⇒⦆ ⦅⇐⦆
     where
      ⦅⇒⦆ : x ⊑⟨ 𝓓 ⟩ y → (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y)
      ⦅⇒⦆ x-below-y b b-way-below-x = ≪-⊑-to-≪ 𝓓 b-way-below-x x-below-y
      ⦅⇐⦆ : (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y) → x ⊑⟨ 𝓓 ⟩ y
      ⦅⇐⦆ h = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
              (↡ᴮ-is-sup x) y
              (λ (b , b-way-below-x) → ≪-to-⊑ 𝓓 (h b b-way-below-x))

  locally-small-if-small-basis : is-locally-small 𝓓
  locally-small-if-small-basis =
   ⌜ local-smallness-equivalent-definitions 𝓓 ⌝⁻¹ γ
    where
     γ : is-locally-small' 𝓓
     γ x y = (∀ (b : B) → b ≪ᴮₛ x → b ≪ᴮₛ y) , e
      where
       e = (∀ (b : B) → b ≪ᴮₛ x → b ≪ᴮₛ y)             ≃⟨ I   ⟩
           (∀ (b : B) → b ≪ᴮₛ x → β b ≪⟨ 𝓓 ⟩ y)       ≃⟨ II  ⟩
           (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y) ≃⟨ III ⟩
           x ⊑⟨ 𝓓 ⟩ y                                ■
        where
         I   = Π-cong fe fe B _ _ (λ b →
                →cong fe fe (≃-refl (b ≪ᴮₛ x)) ≪ᴮₛ-≃-≪ᴮ)
         II  = Π-cong fe fe B _ _ (λ b →
                →cong fe fe ≪ᴮₛ-≃-≪ᴮ (≃-refl (β b ≪⟨ 𝓓 ⟩ y)))
         III = ≃-sym (⊑-in-terms-of-≪ᴮ)


  small-basis-nullary-interpolation : (x : ⟨ 𝓓 ⟩) → ∃ b ꞉ B , β b ≪⟨ 𝓓 ⟩ x
  small-basis-nullary-interpolation x =
   ∥∥-functor id (inhabited-if-Directed 𝓓 (↡ι x) (↡ᴮ-is-directed x))

  small-basis-nullary-interpolationₛ : (x : ⟨ 𝓓 ⟩) → ∃ b ꞉ B , b ≪ᴮₛ x
  small-basis-nullary-interpolationₛ x =
   ∥∥-functor (λ (b , u) → b , (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ u))
             (small-basis-nullary-interpolation x)

  small-basis-unary-interpolation : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                                  → ∃ b ꞉ B , (x ≪⟨ 𝓓 ⟩ β b) × (β b ≪⟨ 𝓓 ⟩ y)
  small-basis-unary-interpolation {x} {y} x-way-below-y = goal
   where
    I : 𝓥 ̇
    I = Σ b ꞉ B , Σ c ꞉ B , (b ≪ᴮₛ β c) × (c ≪ᴮₛ y)
    π : I → ⟨ 𝓓 ⟩
    π (b , _ , _ , _) = β b
    I-inhabited : ∥ I ∥
    I-inhabited = ∥∥-rec ∥∥-is-prop h (small-basis-nullary-interpolationₛ y)
     where
      h : (Σ c ꞉ B , c ≪ᴮₛ y) → ∥ I ∥
      h (c , c-way-below-y) =
       ∥∥-functor k (small-basis-nullary-interpolationₛ (β c))
        where
         k : (Σ b ꞉ B , b ≪ᴮₛ β c) → I
         k (b , b-way-below-c) = (b , c , b-way-below-c , c-way-below-y)
    δ : is-Directed 𝓓 π
    δ = I-inhabited , σ
     where
      σ : is-semidirected (underlying-order 𝓓) π
      σ (b₁ , c₁ , b₁-way-below-c₁ , c₁-way-below-y)
        (b₂ , c₂ , b₂-way-below-c₂ , c₂-way-below-y) =
       ∥∥-rec ∥∥-is-prop h (semidirected-if-Directed 𝓓 (↡ιₛ y) (↡ᴮₛ-is-directed y)
                             (c₁ , c₁-way-below-y)
                             (c₂ , c₂-way-below-y))
        where
         h : (Σ j ꞉ ↡ᴮₛ y , (β c₁ ⊑⟨ 𝓓 ⟩ β (pr₁ j)) × (β c₂ ⊑⟨ 𝓓 ⟩ β (pr₁ j)))
           → ∃ i ꞉ I , (β b₁ ⊑⟨ 𝓓 ⟩ π i) × (β b₂ ⊑⟨ 𝓓 ⟩ π i)
         h ((c , c-way-below-y) , c₁-below-c , c₂-below-c) =
          ∥∥-functor k
           (semidirected-if-Directed 𝓓 (↡ιₛ (β c)) (↡ᴮₛ-is-directed (β c))
             (b₁ , ⌜ φ ⌝⁻¹ (≪-⊑-to-≪ 𝓓 (⌜ φ ⌝ b₁-way-below-c₁) c₁-below-c))
             (b₂ , ⌜ φ ⌝⁻¹ (≪-⊑-to-≪ 𝓓 (⌜ φ ⌝ b₂-way-below-c₂) c₂-below-c)))
           where
            φ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ≪ᴮₛ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
            φ = ≪ᴮₛ-≃-≪ᴮ
            k : Σ j ꞉ ↡ᴮₛ (β c) , (β b₁ ⊑⟨ 𝓓 ⟩ β (pr₁ j))
                                × (β b₂ ⊑⟨ 𝓓 ⟩ β (pr₁ j))
              → Σ i ꞉ I , (β b₁ ⊑⟨ 𝓓 ⟩ π i) × (β b₂ ⊑⟨ 𝓓 ⟩ π i)
            k ((b , b-way-below-c) , b₁-below-b , b₂-below-b) =
             ((b , c , b-way-below-c , c-way-below-y) , (b₁-below-b , b₂-below-b))
    y-below-sup-of-π : y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
    y-below-sup-of-π = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
                        (↡ᴮ-is-sup y) (∐ 𝓓 δ)
                        (λ (c , c-way-below-y) →
                          sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
                           (↡ᴮ-is-sup (β c)) (∐ 𝓓 δ)
                            (λ (b , b-way-below-c) →
                              ∐-is-upperbound 𝓓 δ
                               (b , c , ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ b-way-below-c
                                      , ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ c-way-below-y)))

    claim : ∃ i ꞉ I , x ⊑⟨ 𝓓 ⟩ π i
    claim = x-way-below-y I π δ y-below-sup-of-π

    goal : ∃ b ꞉ B , (x ≪⟨ 𝓓 ⟩ β b) × (β b ≪⟨ 𝓓 ⟩ y)
    goal = ∥∥-functor γ claim
     where
      γ : (Σ i ꞉ I , x ⊑⟨ 𝓓 ⟩ π i)
        → Σ b ꞉ B , (x ≪⟨ 𝓓 ⟩ β b) × (β b ≪⟨ 𝓓 ⟩ y)
      γ ((b , c , b-way-below-c , c-way-below-y) , x-below-b) =
       (c , (⊑-≪-to-≪ 𝓓 x-below-b (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-c))
          , ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ c-way-below-y)

  -- TODO: Explain use of do-notation
  small-basis-binary-interpolation : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
                                   → ∃ b ꞉ B , (x   ≪⟨ 𝓓 ⟩ β b)
                                             × (y   ≪⟨ 𝓓 ⟩ β b)
                                             × (β b ≪⟨ 𝓓 ⟩ z  )
  small-basis-binary-interpolation {x} {y} {z} x-way-below-z y-way-below-z = do
   let δ = ↡ᴮₛ-is-directed z
   let l = ↡ᴮₛ-∐-⊒ z
   (b₁ , x-way-below-b₁ , b₁-way-below-z) ← small-basis-unary-interpolation
                                             x-way-below-z
   (b₂ , y-way-below-b₂ , b₂-way-below-z) ← small-basis-unary-interpolation
                                             y-way-below-z

   ((c₁ , c₁-way-below-z) , b₁-below-c₁)  ← b₁-way-below-z (↡ᴮₛ z) (↡ιₛ z) δ l
   ((c₂ , c₂-way-below-z) , b₂-below-c₂)  ← b₂-way-below-z (↡ᴮₛ z) (↡ιₛ z) δ l

   ((c  , c-way-below-z ) , c₁-below-c
                          , c₂-below-c)   ← semidirected-if-Directed 𝓓 (↡ιₛ z) δ
                                             (c₁ , c₁-way-below-z)
                                             (c₂ , c₂-way-below-z)
   let b₁-below-c = β b₁ ⊑⟨ 𝓓 ⟩[ b₁-below-c₁ ]
                    β c₁ ⊑⟨ 𝓓 ⟩[ c₁-below-c ]
                    β c  ∎⟨ 𝓓 ⟩
   let b₂-below-c = β b₂ ⊑⟨ 𝓓 ⟩[ b₂-below-c₂ ]
                    β c₂ ⊑⟨ 𝓓 ⟩[ c₂-below-c ]
                    β c  ∎⟨ 𝓓 ⟩
   ∣ c , ≪-⊑-to-≪ 𝓓 x-way-below-b₁ b₁-below-c
       , (≪-⊑-to-≪ 𝓓 y-way-below-b₂ b₂-below-c)
       , ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ c-way-below-z ∣




 is-small-basis-Σ : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 is-small-basis-Σ = (x : ⟨ 𝓓 ⟩) → ((b : B) → is-small (β b ≪⟨ 𝓓 ⟩ x))
                                × is-Directed 𝓓 (↡ι x)
                                × is-sup (underlying-order 𝓓) x (↡ι x)

 being-small-basis-Σ-is-prop : is-prop is-small-basis-Σ
 being-small-basis-Σ-is-prop =
  Π-is-prop fe (λ x →
   ×₃-is-prop (Π-is-prop fe
               (λ b → prop-has-size-is-prop (λ _ → pe) (λ _ _ → fe)
                       (β b ≪⟨ 𝓓 ⟩ x) (≪-is-prop-valued 𝓓) 𝓥))
              (being-directed-is-prop (underlying-order 𝓓) (↡ι x))
              (is-sup-is-prop (underlying-order 𝓓) (axioms-of-dcpo 𝓓) x (↡ι x)))

 is-small-basis-≃ : is-small-basis ≃ is-small-basis-Σ
 is-small-basis-≃ = qinveq f (g , ρ , σ)
  where
   f : is-small-basis → is-small-basis-Σ
   f sb x = (≪ᴮ-is-small x , ↡ᴮ-is-directed x , ↡ᴮ-is-sup x)
    where
     open is-small-basis sb
   g : is-small-basis-Σ → is-small-basis
   g sb = record {
     ≪ᴮ-is-small = λ x → pr₁ (sb x);
     ↡ᴮ-is-directed = λ x → pr₁ (pr₂ (sb x));
     ↡ᴮ-is-sup  = λ x → pr₂ (pr₂ (sb x))
    }
   ρ : g ∘ f ∼ id
   ρ _ = refl
   σ : f ∘ g ∼ id
   σ _ = refl

 being-small-basis-is-prop : is-prop is-small-basis
 being-small-basis-is-prop = equiv-to-prop is-small-basis-≃
                              being-small-basis-Σ-is-prop




module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 has-specified-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-specified-small-basis = Σ B ꞉ 𝓥 ̇  , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , is-small-basis 𝓓 β

 has-unspecified-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-unspecified-small-basis = ∥ has-specified-small-basis ∥

 structurally-continuous-if-specified-small-basis : has-specified-small-basis
                                                  → structurally-continuous 𝓓
 structurally-continuous-if-specified-small-basis (B , β , sb) =
  structurally-continuous-if-equiped-with-small-basis 𝓓 β sb

 is-continuous-dcpo-if-unspecified-small-basis : has-unspecified-small-basis
                                               → is-continuous-dcpo 𝓓
 is-continuous-dcpo-if-unspecified-small-basis =
  ∥∥-functor structurally-continuous-if-specified-small-basis



\end{code}

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
       where

 ↓ᴮ : ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓣 ̇
 ↓ᴮ x = Σ b ꞉ B , β b ⊑⟨ 𝓓 ⟩ x

 ↓ι : (x : ⟨ 𝓓 ⟩) → ↓ᴮ x → ⟨ 𝓓 ⟩
 ↓ι x = β ∘ pr₁

 record is-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   basis-is-compact : (b : B) → is-compact 𝓓 (β b)
   ⊑ᴮ-is-small : (x : ⟨ 𝓓 ⟩) → ((b : B) → is-small (β b ⊑⟨ 𝓓 ⟩ x))
   ↓ᴮ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓ι x)
   ↓ᴮ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↓ι x)

  _⊑ᴮₛ_ : (b : B) (x : ⟨ 𝓓 ⟩) → 𝓥 ̇
  b ⊑ᴮₛ x = pr₁ (⊑ᴮ-is-small x b)

  ⊑ᴮₛ-≃-⊑ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ⊑ᴮₛ x) ≃ (β b ⊑⟨ 𝓓 ⟩ x)
  ⊑ᴮₛ-≃-⊑ᴮ {b} {x} = pr₂ (⊑ᴮ-is-small x b)

  ↓ᴮₛ : ⟨ 𝓓 ⟩ → 𝓥 ̇
  ↓ᴮₛ x = Σ b ꞉ B , (b ⊑ᴮₛ x)

  ↓ιₛ : (x : ⟨ 𝓓 ⟩) → ↓ᴮₛ x → ⟨ 𝓓 ⟩
  ↓ιₛ x = β ∘ pr₁

  ↓ᴮₛ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓ιₛ x)
  ↓ᴮₛ-is-directed x = reindexed-family-is-directed 𝓓
                       (Σ-cong (λ b → ≃-sym ⊑ᴮₛ-≃-⊑ᴮ)) (↓ι x) (↓ᴮ-is-directed x)

  ↓ᴮₛ-∐-≡ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↓ᴮₛ-is-directed x) ≡ x
  ↓ᴮₛ-∐-≡ x = antisymmetry 𝓓 (∐ 𝓓 (↓ᴮₛ-is-directed x)) x ⦅1⦆ ⦅2⦆
   where
    ⦅1⦆ : ∐ 𝓓 (↓ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
    ⦅1⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 (↓ᴮₛ-is-directed x) x
          (λ (b , u) → sup-is-upperbound (underlying-order 𝓓) (↓ᴮ-is-sup x)
                        (b , (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ u)))
    ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↓ᴮₛ-is-directed x)
    ⦅2⦆ = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (↓ᴮ-is-sup x)
          (∐ 𝓓 (↓ᴮₛ-is-directed x))
          (λ (b , v) → ∐-is-upperbound 𝓓 (↓ᴮₛ-is-directed x)
                        (b , (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝⁻¹ v)))

  ↓ᴮₛ-∐-⊑ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↓ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
  ↓ᴮₛ-∐-⊑ x = ≡-to-⊑ 𝓓 (↓ᴮₛ-∐-≡ x)

  ↓ᴮₛ-∐-⊒ : (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↓ᴮₛ-is-directed x)
  ↓ᴮₛ-∐-⊒ x = ≡-to-⊑ 𝓓 ((↓ᴮₛ-∐-≡ x) ⁻¹)

  ↓ᴮₛ-compact : (x : ⟨ 𝓓 ⟩) (b : ↓ᴮₛ x) → is-compact 𝓓 (↓ιₛ x b)
  ↓ᴮₛ-compact x (b , u) = basis-is-compact b

 compact-basis-is-basis : is-small-compact-basis
                        → is-small-basis 𝓓 β
 compact-basis-is-basis scb = record {
   ≪ᴮ-is-small    = λ x b → ( b ⊑ᴮₛ x
                            , ((b ⊑ᴮₛ x)      ≃⟨ ⊑ᴮₛ-≃-⊑ᴮ ⟩
                               (β b ⊑⟨ 𝓓 ⟩ x) ≃⟨ lemma b  ⟩
                               (β b ≪⟨ 𝓓 ⟩ x) ■));
   ↡ᴮ-is-directed = λ x → reindexed-family-is-directed 𝓓
                           (↓ᴮ-≃-↡ᴮ x) (↓ι x) (↓ᴮ-is-directed x);
   ↡ᴮ-is-sup      = λ x → reindexed-family-sup 𝓓 (↓ᴮ-≃-↡ᴮ x) (↓ι x)
                           x (↓ᴮ-is-sup x)
  }
   where
    open is-small-compact-basis scb
    lemma : (b : B) {x : ⟨ 𝓓 ⟩} → (β b ⊑⟨ 𝓓 ⟩ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
    lemma b = compact-⊑-≃-≪ 𝓓 (basis-is-compact b)
    ↓ᴮ-≃-↡ᴮ : (x : ⟨ 𝓓 ⟩) → ↓ᴮ x ≃ ↡ᴮ 𝓓 β x
    ↓ᴮ-≃-↡ᴮ x = Σ-cong (λ b → lemma b)

\end{code}

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 structurally-algebraic-if-equiped-with-small-compact-basis :
    {B : 𝓥 ̇  } (β : B → ⟨ 𝓓 ⟩)
  → is-small-compact-basis 𝓓 β
  → structurally-algebraic 𝓓
 structurally-algebraic-if-equiped-with-small-compact-basis β scb = record {
   index-of-compact-family    = ↓ᴮₛ;
   compact-family             = ↓ιₛ;
   compact-family-is-directed = ↓ᴮₛ-is-directed;
   compact-family-is-compact  = ↓ᴮₛ-compact;
   compact-family-∐-≡         = ↓ᴮₛ-∐-≡
  }
   where
    open is-small-compact-basis scb

 has-specified-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-specified-small-compact-basis =
  Σ B ꞉ 𝓥 ̇ , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , is-small-compact-basis 𝓓 β

 has-unspecified-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-unspecified-small-compact-basis = ∥ has-specified-small-compact-basis ∥

 structurally-algebraic-if-specified-small-compact-basis :
    has-specified-small-compact-basis
  → structurally-algebraic 𝓓
 structurally-algebraic-if-specified-small-compact-basis (B , β , sb) =
  structurally-algebraic-if-equiped-with-small-compact-basis β sb

 is-algebraic-dcpo-if-unspecified-small-compact-basis : has-unspecified-small-compact-basis
                                               → is-algebraic-dcpo 𝓓
 is-algebraic-dcpo-if-unspecified-small-compact-basis =
  ∥∥-functor structurally-algebraic-if-specified-small-compact-basis



\end{code}

TODO: Move to DcpoContinuous?

\begin{code}

record _is-continuous-retract-of_
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇  where
  field
   section : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
   retraction : ⟨ 𝓔 ⟩ → ⟨ 𝓓 ⟩
   retraction-section-equation : retraction ∘ section ∼ id
   section-is-continuous : is-continuous 𝓓 𝓔 section
   retraction-is-continuous : is-continuous 𝓔 𝓓 retraction

structural-continuity-of-dcpo-preserved-by-continuous-retract :
   (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
 → 𝓓 is-continuous-retract-of 𝓔
 → structurally-continuous 𝓔
 → structurally-continuous 𝓓
structural-continuity-of-dcpo-preserved-by-continuous-retract 𝓓 𝓔 ρ γ =
 record
   { index-of-approximating-family =
      λ x → index-of-approximating-family (section x)
   ; approximating-family =
      λ x → retraction ∘ approximating-family (section x)
   ; approximating-family-is-directed = lemma₁
   ; approximating-family-is-way-below = lemma₂
   ; approximating-family-∐-≡ = lemma₃
   }
 where
  open structurally-continuous γ
  open _is-continuous-retract-of_ ρ
  r : ⟨ 𝓔 ⟩ → ⟨ 𝓓 ⟩
  r = retraction
  s : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
  s = section
  α : (y : ⟨ 𝓔 ⟩) → index-of-approximating-family y → ⟨ 𝓔 ⟩
  α = approximating-family
  lemma₁ : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (r ∘ α (s x))
  lemma₁ x = image-is-directed' 𝓔 𝓓 (retraction , retraction-is-continuous)
              (approximating-family-is-directed (section x))
  lemma₂ : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (r ∘ α (s x))
  lemma₂ x i J β δ x-below-∐β =
   ∥∥-functor h (approximating-family-is-way-below (s x) i J (s ∘ β) ε l)
    where
     h : (Σ j ꞉ J , α (s x) i ⊑⟨ 𝓔 ⟩ s (β j))
       → Σ j ꞉ J , r (α (s x) i) ⊑⟨ 𝓓 ⟩ β j
     h (j , u) = (j , v)
      where
       v = r (α (s x) i) ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
           r (s (β j))   ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
           β j           ∎⟨ 𝓓 ⟩
        where
         ⦅1⦆ = monotone-if-continuous 𝓔 𝓓 (r , retraction-is-continuous)
               (α (s x) i) (s (β j)) u
         ⦅2⦆ = ≡-to-⊑ 𝓓 (retraction-section-equation (β j))
     ε : is-Directed 𝓔 (s ∘ β)
     ε = image-is-directed' 𝓓 𝓔 (s , section-is-continuous) δ
     l = s x       ⊑⟨ 𝓔 ⟩[ ⦅1⦆ ]
         s (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩[ ⦅2⦆ ]
         ∐ 𝓔 ε     ∎⟨ 𝓔 ⟩
      where
       ⦅1⦆ = monotone-if-continuous 𝓓 𝓔 (s , section-is-continuous)
             x (∐ 𝓓 δ) x-below-∐β
       ⦅2⦆ = continuous-∐-⊑ 𝓓 𝓔 (s , section-is-continuous) δ
  lemma₃ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (lemma₁ x) ≡ x
  lemma₃ x = ∐ 𝓓 (lemma₁ x) ≡⟨ ⦅1⦆ ⟩
             r (∐ 𝓔 δ)      ≡⟨ ⦅2⦆ ⟩
             r (s x)        ≡⟨ ⦅3⦆ ⟩
             x              ∎
   where
    δ : is-Directed 𝓔 (α (s x))
    δ = approximating-family-is-directed (s x)
    ⦅1⦆ = (continuous-∐-≡ 𝓔 𝓓 (r , retraction-is-continuous) δ) ⁻¹
    ⦅2⦆ = ap r (approximating-family-∐-≡ (s x))
    ⦅3⦆ = retraction-section-equation x

continuity-of-dcpo-preserved-by-continuous-retract :
   (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
 → 𝓓 is-continuous-retract-of 𝓔
 → is-continuous-dcpo 𝓔
 → is-continuous-dcpo 𝓓
continuity-of-dcpo-preserved-by-continuous-retract 𝓓 𝓔 ρ =
 ∥∥-functor (structural-continuity-of-dcpo-preserved-by-continuous-retract 𝓓 𝓔 ρ)

\end{code}
