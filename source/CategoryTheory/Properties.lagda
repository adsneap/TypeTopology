\begin{code}

open import MLTT.Spartan renaming (_∘_ to _∘'_)

open import CategoryTheory.Type
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt

module CategoryTheory.Properties where

module _
  (𝓤 : Universe)
  (pC : precategory {𝓤} {𝓥})
 where

 open precategory pC

 isomorphism : {a b : ob} → (f : hom a b) → 𝓥 ̇
 isomorphism {a} {b} f = Σ g ꞉ hom b a , (g ∘ f ＝ u) × (f ∘ g ＝ u)

 isomorphism-is-prop : {a b : ob} → {f : hom a b} → is-prop (isomorphism f)
 isomorphism-is-prop {_} {_} {f} (g , η , ε) (g' , η' , ε') = to-subtype-＝ (λ _ → ×-is-prop hom-set hom-set) g-equals-g'
   where
    g-equals-g' : g ＝ g'
    g-equals-g' = g              ＝⟨ unit-r g ⁻¹ ⟩
                  g ∘ u          ＝⟨ ap (g ∘_) (ε' ⁻¹) ⟩
                  g ∘ (f ∘ g')   ＝⟨ assoc g' f g ⟩
                  (g ∘ f) ∘ g'   ＝⟨ ap (_∘ g') η ⟩
                  u ∘ g'         ＝⟨ unit-l g' ⟩
                  g'             ∎

 _≅_ : (a b : ob) → 𝓥 ̇
 a ≅ b = Σ f ꞉ hom a b , isomorphism f

 {-
 Isomorphisms are sets, because they are a subset of the space of homsets, and homsets are sets.
 -}

 isomorphism-is-set : {a b : ob} → is-set (a ≅ b) 
 isomorphism-is-set {a} {b} = subsets-of-sets-are-sets (hom a b) isomorphism hom-set isomorphism-is-prop

 ! : {a b : ob} → a ≅ b → b ≅ a
 ! (f , g , p1 , p2) = g , f , p2 , p1

 idtoiso : {a b : ob} → a ＝ b → a ≅ b
 idtoiso refl = u , u , (unit-l u) , (unit-r u)

 _≅∘_ : {a b c : ob} → a ≅ b → b ≅ c → a ≅ c
 (f , g , η , ε) ≅∘ (f' , g' , η' , ε') = f' ∘ f , (g ∘ g') , I , II
  where
   I : (g ∘ g') ∘ (f' ∘ f) ＝ u
   I = (g ∘ g') ∘ (f' ∘ f)      ＝⟨ assoc f f' (g ∘ g') ⟩
       ((g ∘ g') ∘ f') ∘ f      ＝⟨ ap (_∘ f) (assoc f' g' g ⁻¹) ⟩
       (g ∘ (g' ∘ f')) ∘ f      ＝⟨ ap (λ - → (g ∘ -) ∘ f) η' ⟩
       (g ∘ u) ∘ f              ＝⟨ ap (_∘ f) (unit-r g) ⟩
       g ∘ f                    ＝⟨ η ⟩
       u  ∎
   II : (f' ∘ f) ∘ (g ∘ g') ＝ u
   II = (f' ∘ f) ∘ (g ∘ g')   ＝⟨ assoc g' g (f' ∘ f) ⟩
        ((f' ∘ f) ∘ g) ∘ g'   ＝⟨ ap (_∘ g') (assoc g f f' ⁻¹) ⟩
        ((f' ∘ (f ∘ g)) ∘ g') ＝⟨ ap (λ - → (f' ∘ -) ∘ g') ε ⟩
        (f' ∘ u) ∘ g'         ＝⟨ ap (_∘ g') (unit-r f') ⟩
        f' ∘ g'               ＝⟨ ε' ⟩
        u ∎

\end{code}
