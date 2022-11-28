
\begin{code}

module CategoryTheory.Type where

open import MLTT.Spartan renaming (_∘_ to _∘'_)
open import UF.Subsingletons

record precategory {𝓤 𝓥 : Universe} : 𝓤 ⁺ ⊔ (𝓥 ⁺) ̇ where
 field
  ob : 𝓤 ̇
  hom : (a b : ob) → 𝓥 ̇
  hom-set : ∀ {a} {b} → is-set (hom a b)
  1ₐ : {a : ob } → hom  a a
  _∘_ : {a b c : ob} → hom  b c → hom  a b → hom  a c
  unit-l : {a b : ob} → (f : hom  a b) → (1ₐ ∘ f) ＝ f
  unit-r : {a b : ob} → (f : hom  a b) → (f ∘ 1ₐ) ＝ f
  assoc : {a b c d : ob} → (f : hom  a b) → (g : hom b c) → (h : hom c d) → (h ∘ (g ∘ f)) ＝ ((h ∘ g) ∘ f)

\end{code}

