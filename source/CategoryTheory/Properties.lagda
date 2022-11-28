\begin{code}

open import MLTT.Spartan renaming (_∘_ to _∘'_)

open import CategoryTheory.Type
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module CategoryTheory.Properties where

module _
  (𝓤 : Universe)
  (pC : precategory {𝓤} {𝓥})
 where

 open precategory pC

 isomorphism : {a b : ob} → (f : hom a b) → 𝓥 ̇
 isomorphism {a} {b} f = Σ g ꞉ hom b a , (g ∘ f ＝ 1ₐ) × (f ∘ g ＝ 1ₐ)

 isomorphism-is-prop : {a b : ob} → {f : hom a b} → is-prop (isomorphism f)
 isomorphism-is-prop {_} {_} {f} (g , η , ε) (g' , η' , ε') = to-subtype-＝ (λ _ → ×-is-prop hom-set hom-set) g-equals-g'
   where
    g-equals-g' : g ＝ g'
    g-equals-g' = g              ＝⟨ unit-r g ⁻¹ ⟩
                  g ∘ 1ₐ         ＝⟨ ap (g ∘_) (ε' ⁻¹) ⟩
                  g ∘ (f ∘ g')   ＝⟨ assoc g' f g ⟩
                  (g ∘ f) ∘ g'   ＝⟨ ap (_∘ g') η ⟩
                  1ₐ ∘ g'        ＝⟨ unit-l g' ⟩
                  g'             ∎

 _≅_ : (a b : ob) → 𝓥 ̇
 a ≅ b = Σ f ꞉ hom a b , isomorphism f

 isomorphism-is-set : {a b : ob} → is-set (a ≅ b) 
 isomorphism-is-set {a} {b} = subsets-of-sets-are-sets (hom a b) isomorphism hom-set isomorphism-is-prop

cSet : precategory {𝓤 ⁺}
cSet {𝓤} = record
          { ob = hSet 𝓤
          ; hom = λ (A , _) (B , _) → A → B
          ; hom-set = λ { {(A , A-is-set)} {B , B-is-set} → Π-is-set {!!} λ _ → B-is-set }
          ; 1ₐ = id
          ; _∘_ = _∘'_
          ; unit-l = λ f → refl
          ; unit-r = λ f → refl
          ; assoc = λ f g h → refl
          }



\end{code}
