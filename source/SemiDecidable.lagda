Tom de Jong, 22 October 2021.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc
open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-ImageAndSurjection

open import DecidableAndDetachable
open import DiscreteAndSeparated
open import Two-Properties
open import UF-Miscelanea

open import UF-Powerset
open import UF-EquivalenceExamples

\end{code}

\begin{code}
module SemiDecidable
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
        (pt  : propositional-truncations-exist)
       where

open PropositionalTruncation pt
open ImageAndSurjection pt

semidecidability-structure : (X : 𝓤 ̇  ) → 𝓤 ̇
semidecidability-structure X = Σ α ꞉ (ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)

semidecidability-structure' : (𝓣 : Universe) (X : 𝓤 ̇  ) → 𝓣 ⁺ ⊔ 𝓤 ̇
semidecidability-structure' 𝓣 X = Σ A ꞉ (ℕ → Ω 𝓣) , is-decidable-subset A
                                                    × (X ≃ (∃ n ꞉ ℕ , n ∈ A))

--TODO: Move somewhere better
∥∥-cong : {X : 𝓤 ̇  } {Y : 𝓥 ̇  } → X ≃ Y → ∥ X ∥ ≃ ∥ Y ∥
∥∥-cong f = logically-equivalent-props-are-equivalent ∥∥-is-prop ∥∥-is-prop
             (∥∥-functor ⌜ f ⌝) (∥∥-functor ⌜ f ⌝⁻¹)

open import UF-Equiv-FunExt

≃-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
       → X ≃ A → Y ≃ B → (X ≃ Y) ≃ (A ≃ B)
≃-cong {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {A} {B} ϕ ψ =
 (X ≃ Y)                              ≃⟨ I              ⟩
 (Σ g ꞉ (A → B) , is-equiv (⌜ e ⌝ g)) ≃⟨ II             ⟩
 (Σ g ꞉ (A → B) , is-equiv g)         ≃⟨ ≃-refl (A ≃ B) ⟩
 (A ≃ B)                              ■
  where
   e : (A → B) ≃ (X → Y)
   e = ≃-sym (→cong fe fe ϕ ψ)
   I  = ≃-sym (Σ-change-of-variable is-equiv ⌜ e ⌝ (⌜⌝-is-equiv e))
   II = Σ-cong (λ g → logically-equivalent-props-are-equivalent
                       (being-equiv-is-prop (λ _ _ → fe) (⌜ ψ ⌝⁻¹ ∘ g ∘ ⌜ ϕ ⌝))
                       (being-equiv-is-prop (λ _ _ → fe) g)
                       (II₁ g)
                       (II₂ g))
    where
     II₂ : (g : A → B) → is-equiv g → is-equiv (⌜ ψ ⌝⁻¹ ∘ g ∘ ⌜ ϕ ⌝)
     II₂ g i = ∘-is-equiv (⌜⌝-is-equiv ϕ) (∘-is-equiv i (⌜⌝⁻¹-is-equiv ψ))
     II₁ : (g : A → B) → is-equiv (⌜ ψ ⌝⁻¹ ∘ g ∘ ⌜ ϕ ⌝) → is-equiv g
     II₁ g i = equiv-closed-under-∼ c g j H
      where
       c : A → B
       c = ⌜ ψ ⌝ ∘ ⌜ ψ ⌝⁻¹ ∘ g ∘ ⌜ ϕ ⌝ ∘ ⌜ ϕ ⌝⁻¹
       j : is-equiv c
       j = ∘-is-equiv (⌜⌝⁻¹-is-equiv ϕ) (∘-is-equiv i (⌜⌝-is-equiv ψ))
       H : g ∼ (⌜ ψ ⌝ ∘ ⌜ ψ ⌝⁻¹ ∘ g ∘ ⌜ ϕ ⌝ ∘ ⌜ ϕ ⌝⁻¹)
       H x = (≃-sym-is-rinv ψ (g ((⌜ ϕ ⌝ ∘ ⌜ ϕ ⌝⁻¹) x))
               ∙ ap g (≃-sym-is-linv (≃-sym ϕ) x)      ) ⁻¹

≃-cong' : {X : 𝓤 ̇ } {A : 𝓥 ̇ } {B : 𝓦 ̇ }
       → A ≃ B → (X ≃ A) ≃ (X ≃ B)
≃-cong' = ≃-cong (≃-refl _)

semidecidability-structure-≃ : {𝓣 : Universe} {X : 𝓤 ̇  }
                             → semidecidability-structure X
                             ≃ semidecidability-structure' 𝓣 X
semidecidability-structure-≃ {𝓤} {𝓣} {X} =
 (Σ α ꞉ (ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , α n ≡ ₁))                            ≃⟨ I   ⟩
 (Σ 𝔸 ꞉ (Σ A ꞉ (ℕ → Ω 𝓣) , is-decidable-subset A)
                          , X ≃ (∃ n ꞉ ℕ , ⌜ χ ⌝ 𝔸 n ≡ ₁))            ≃⟨ II  ⟩
 (Σ A ꞉ (ℕ → Ω 𝓣) , Σ δ ꞉ is-decidable-subset A
                         , X ≃ (∃ n ꞉ ℕ , ⌜ χ ⌝ (A , δ) n ≡ ₁))       ≃⟨ III ⟩
 (Σ A ꞉ (ℕ → Ω 𝓣) , is-decidable-subset A × (X ≃ (∃ n ꞉ ℕ , n ∈ A))) ■
  where
   χ : (Σ A ꞉ (ℕ → Ω 𝓣) , is-decidable-subset A) ≃ (ℕ → 𝟚)
   χ = ≃-sym (𝟚-classifies-decidable-subsets fe fe pe)
   I   = ≃-sym (Σ-change-of-variable (λ α → X ≃ (∃ n ꞉ ℕ , α n ≡ ₁))
          ⌜ χ ⌝ (⌜⌝-is-equiv χ))
   II  = Σ-assoc
   III = Σ-cong (λ A → Σ-cong
                (λ δ → ≃-cong' (∥∥-cong (Σ-cong (λ n → κ A δ n)))))
    where
     κ : (A : ℕ → Ω 𝓣) (δ : is-decidable-subset A) (n : ℕ )
       → (⌜ χ ⌝ (A , δ) n ≡ ₁) ≃ (A n holds)
     κ A δ n = logically-equivalent-props-are-equivalent
                    𝟚-is-set (holds-is-prop (A n))
                    (lr-implication (pr₂ lemma)) (rl-implication (pr₂ lemma))
      where
       lemma : ((⌜ χ ⌝ (A , δ) n ≡ ₀) ⇔ ¬ (n ∈ A))
             × ((⌜ χ ⌝ (A , δ) n ≡ ₁) ⇔   (n ∈ A))
       lemma = 𝟚-classifies-decidable-subsets-values fe fe pe A δ n

is-semidecidable : (X : 𝓤 ̇  ) → 𝓤 ̇
is-semidecidable X = ∥ semidecidability-structure X ∥

is-semidecidable' : (𝓣 : Universe) (X : 𝓤 ̇  ) → 𝓣 ⁺ ⊔ 𝓤 ̇
is-semidecidable' 𝓣 X = ∥ semidecidability-structure' 𝓣 X ∥

is-semidecidable-≃ : {𝓣 : Universe} {X : 𝓤 ̇  }
                   → is-semidecidable X ≃ is-semidecidable' 𝓣 X
is-semidecidable-≃ = ∥∥-cong (semidecidability-structure-≃)

prop-if-semidecidability-structure : {X : 𝓤 ̇  }
                                   → semidecidability-structure X → is-prop X
prop-if-semidecidability-structure σ = equiv-to-prop (pr₂ σ) ∥∥-is-prop

prop-if-semidecidable : {X : 𝓤 ̇  } → is-semidecidable X → is-prop X
prop-if-semidecidable = ∥∥-rec (being-prop-is-prop fe)
                               prop-if-semidecidability-structure

\end{code}

\begin{code}

-- TODO: Rename
silly-lemma : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {A : (x : X) → Y x → 𝓦 ̇  }
            → (∃ x ꞉ X , ∃ y ꞉ Y x , A x y)
            ≃ (∃ x ꞉ X , Σ y ꞉ Y x , A x y)
silly-lemma {𝓤} {𝓥} {𝓦} {X} {Y} {A} =
 logically-equivalent-props-are-equivalent ∥∥-is-prop ∥∥-is-prop f g
  where
   g : (∃ x ꞉ X , Σ y ꞉ Y x , A x y)
     → (∃ x ꞉ X , ∃ y ꞉ Y x , A x y)
   g = ∥∥-functor (λ (x , y , a) → x , ∣ y , a ∣)
   f : (∃ x ꞉ X , ∃ y ꞉ Y x , A x y)
     → (∃ x ꞉ X , Σ y ꞉ Y x , A x y)
   f = ∥∥-rec ∥∥-is-prop ϕ
    where
     ϕ : (Σ x ꞉ X , ∃ y ꞉ Y x , A x y)
       → (∃ x ꞉ X , Σ y ꞉ Y x , A x y)
     ϕ (x , p) = ∥∥-functor (λ (y , a) → x , y , a) p

∃-cong : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {Y' : X → 𝓦 ̇  }
       → ((x : X) → Y x ≃ Y' x)
       → ∃ Y ≃ ∃ Y'
∃-cong e = ∥∥-cong (Σ-cong e)

open import BinaryNaturals hiding (_+_)

-- TODO: Make a version with ∃ n ꞉ ℕ , ∃ m ꞉ ℕ instead?
semidecidability-pairing-lemma : {X : 𝓤 ̇  }
  → (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁))
  ≃ semidecidability-structure X
semidecidability-pairing-lemma {𝓤} {X} =
 (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁))            ≃⟨ I   ⟩
 (Σ Ψ ꞉ (ℕ × ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁))        ≃⟨ II  ⟩
 (Σ ϕ ꞉ (ℕ → 𝟚)     , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , ⌜ e₂ ⌝ ϕ (n , m) ≡ ₁)) ≃⟨ III ⟩
 (Σ ϕ ꞉ (ℕ → 𝟚)     , X ≃ (∃ k ꞉ ℕ           , ϕ k ≡ ₁))              ■
 where
  e₁ : (ℕ × ℕ → 𝟚) ≃ (ℕ → ℕ → 𝟚)
  e₁ = curry-uncurry (λ _ _ → fe)
  e₂ : (ℕ → 𝟚) ≃ (ℕ × ℕ → 𝟚)
  e₂ = →cong'' fe fe (≃-sym pairing)
  I  = ≃-sym (Σ-change-of-variable (λ Ψ → X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁))
                                   ⌜ e₁ ⌝ (⌜⌝-is-equiv e₁))
  II = ≃-sym (Σ-change-of-variable
               (λ Ψ → X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁))
               ⌜ e₂ ⌝ (⌜⌝-is-equiv e₂))
  III = Σ-cong (λ ϕ → ≃-cong' (∥∥-cong (lemma ϕ)))
   where
    ρ : ℕ × ℕ ≃ ℕ
    ρ = pairing
    σ : (ℕ → 𝟚) → (ℕ × ℕ → 𝟚)
    σ = ⌜ e₂ ⌝
    lemma : (ϕ : ℕ → 𝟚)
          → (Σ n ꞉ ℕ , Σ m ꞉ ℕ , σ ϕ (n , m) ≡ ₁)
          ≃ (Σ k ꞉ ℕ , ϕ k ≡ ₁)
    lemma ϕ = (Σ n ꞉ ℕ , Σ m ꞉ ℕ , σ ϕ (n , m) ≡ ₁)           ≃⟨ ≃-sym Σ-assoc ⟩
              (Σ p ꞉ ℕ × ℕ       , σ ϕ p ≡ ₁)                 ≃⟨ ⦅i⦆           ⟩
              (Σ k ꞉ ℕ           , σ ϕ (⌜ ρ ⌝⁻¹ k) ≡ ₁)       ≃⟨ ≃-refl _      ⟩
              (Σ k ꞉ ℕ           , ϕ (⌜ ρ ⌝ (⌜ ρ ⌝⁻¹ k)) ≡ ₁) ≃⟨ ⦅ii⦆          ⟩
              (Σ k ꞉ ℕ           , ϕ k ≡ ₁)                   ■
     where
      ⦅i⦆  = ≃-sym (Σ-change-of-variable (λ p → σ ϕ p ≡ ₁) ⌜ ρ ⌝⁻¹ (⌜⌝⁻¹-is-equiv ρ))
      ⦅ii⦆ = Σ-cong (λ k → ≡-cong-l _ _ (ap ϕ (≃-sym-is-rinv ρ k)))

-- TODO: In need of a better name. Maybe: semidecidability-structure-ω-joins ?
semidecidability-structure-∃ : (X : ℕ → 𝓤 ̇  )
                             → (Π n ꞉ ℕ , semidecidability-structure (X n))
                             → semidecidability-structure (∃ X)
semidecidability-structure-∃ X σ = ⌜ semidecidability-pairing-lemma ⌝ γ
 where
  γ : Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , ∃ X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁)
  γ = Ψ , e
   where
    lemma : (Π n ꞉ ℕ , semidecidability-structure (X n))
          → (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , Π n ꞉ ℕ , X n ≃ (∃ m ꞉ ℕ , Ψ n m ≡ ₁))
    lemma = ⌜ ΠΣ-distr-≃ ⌝
    Ψ : ℕ → ℕ → 𝟚
    Ψ = pr₁ (lemma σ)
    e = ∃ X                             ≃⟨ ∃-cong (pr₂ (lemma σ)) ⟩
        (∃ n ꞉ ℕ , ∃ m ꞉ ℕ , Ψ n m ≡ ₁) ≃⟨ silly-lemma            ⟩
        (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁) ■

key-construction : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {A : X → 𝓦 ̇  }
                 → (∃ A → Σ Y)
                 → X → X → 𝓤 ⊔ 𝓦 ̇
key-construction {𝓤} {𝓥} {𝓦} {X} {Y} {A} f x y =
  Σ a ꞉ A y , pr₁ (f ∣ y , a ∣) ≡ x

blah : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {A : X → 𝓦 ̇  }
     → ((x : X) → is-prop (Y x))
     → (f : (∃ A ≃ (Σ Y)))
     → (x : X) → Y x ≃ ∃ (key-construction ⌜ f ⌝ x)
blah {𝓤} {𝓥} {𝓦} {X} {Y} {A} i f x =
 logically-equivalent-props-are-equivalent (i x) ∥∥-is-prop α β
  where
   β : ∃ (key-construction ⌜ f ⌝ x) → Y x
   β = ∥∥-rec (i x) γ
    where
     γ : Σ (key-construction ⌜ f ⌝ x) → Y x
     γ (y , a , e) = transport Y e (pr₂ (⌜ f ⌝ ∣ y , a ∣))
   α : Y x → ∃ (key-construction ⌜ f ⌝ x)
   α y = ∥∥-functor γ (⌜ f ⌝⁻¹ (x , y))
    where
     γ : Σ A → Σ (key-construction ⌜ f ⌝ x)
     γ (x' , a) = x' , (a , ap pr₁ e)
      where
       e = (⌜ f ⌝ ∣ x' , a ∣)        ≡⟨ ap ⌜ f ⌝ (∥∥-is-prop ∣ x' , a ∣ (⌜ f ⌝⁻¹ (x , y))) ⟩
           (⌜ f ⌝ (⌜ f ⌝⁻¹ (x , y))) ≡⟨ ≃-sym-is-rinv f (x , y) ⟩
           (x , y) ∎

{-
  "All" that's left now is to show that key-construction n m is proposition-valued and decidable.
  This would give that X n is semi-decidable for every n : ℕ.
-}

semidecidability-structure-Σ : (X : ℕ → 𝓤 ̇  )
                             → ((n : ℕ) → is-prop (X n))
                             → semidecidability-structure (Σ X)
                             → (Π n ꞉ ℕ , semidecidability-structure (X n))
semidecidability-structure-Σ X X-is-prop-valued (Ψ , e) n =
 ⌜ semidecidability-structure-≃ ⌝⁻¹ σ
  where
   φ : ℕ → 𝓤₀ ̇
   φ = key-construction ⌜ e ⌝⁻¹ n
   φ-is-prop-valued : (m : ℕ) → is-prop (φ m)
   φ-is-prop-valued m = Σ-is-prop 𝟚-is-set (λ _ → ℕ-is-set)
   φ-is-detachable : detachable φ
   φ-is-detachable m = decidable-closed-under-Σ 𝟚-is-set
                        (𝟚-is-discrete (Ψ m) ₁)
                        (λ (p : Ψ m ≡ ₁) → ℕ-is-discrete (pr₁ (⌜ e ⌝⁻¹ ∣ m , p ∣)) n)
   φ⁺ : ℕ → Ω 𝓤₀
   φ⁺ n = (φ n , φ-is-prop-valued n)
   σ : semidecidability-structure' 𝓤₀ (X n)
   σ = φ⁺ , φ-is-detachable , (blah X-is-prop-valued (≃-sym e) n)

-- Countable-Semidecidable-Choice
Countable-Semidecidability-Choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
Countable-Semidecidability-Choice 𝓤 = (X : ℕ → 𝓤 ̇  )
                                    → (Π n ꞉ ℕ , ∥ semidecidability-structure (X n) ∥)
                                    → ∥ Π n ꞉ ℕ , semidecidability-structure (X n) ∥

Semidecidability-Closed-Under-ω-Joins : (𝓤 : Universe) → 𝓤 ⁺ ̇
Semidecidability-Closed-Under-ω-Joins 𝓤 = (X : ℕ → 𝓤 ̇  )
                                        → (Π n ꞉ ℕ , is-semidecidable (X n))
                                        → is-semidecidable (∃ X)

csc-implies-that-semidecidability-is-closed-under-ω-joins : {𝓤 : Universe}
 → Countable-Semidecidability-Choice 𝓤
 → Semidecidability-Closed-Under-ω-Joins 𝓤
csc-implies-that-semidecidability-is-closed-under-ω-joins {𝓤} csc X σ =
 ∥∥-functor (semidecidability-structure-∃ X) (csc X σ)

Semidecidability-Closed-Under-Special-ω-Joins : (𝓤 : Universe) → 𝓤 ⁺ ̇
Semidecidability-Closed-Under-Special-ω-Joins 𝓤 = (X : ℕ → 𝓤 ̇  )
                                              → is-prop (Σ X)
                                              → (Π n ꞉ ℕ , is-semidecidable (X n))
                                              → is-semidecidable (Σ X)

Countable-Semidecidability-Special-Choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
Countable-Semidecidability-Special-Choice 𝓤 = (X : ℕ → 𝓤 ̇  )
                                          → is-prop (Σ X)
                                          → (Π n ꞉ ℕ , ∥ semidecidability-structure (X n) ∥)
                                          → ∥ Π n ꞉ ℕ , semidecidability-structure (X n) ∥

--TODO: Move somewhere better
semidecidability-structure-cong : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
                                → X ≃ Y
                                → semidecidability-structure X
                                → semidecidability-structure Y
semidecidability-structure-cong {𝓤} {𝓥} f (ϕ , e) = (ϕ , (≃-sym f ● e))

is-semidecidable-cong : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
                      → X ≃ Y
                      → is-semidecidable X
                      → is-semidecidable Y
is-semidecidable-cong = ∥∥-functor ∘ semidecidability-structure-cong

converse-in-special-cases : {𝓤 : Universe}
                          → Semidecidability-Closed-Under-Special-ω-Joins 𝓤
                          → Countable-Semidecidability-Special-Choice 𝓤
converse-in-special-cases h X i σ =
 ∥∥-functor (semidecidability-structure-Σ X j)
            (h X i σ)
          -- (∥∥-functor (semidecidability-structure-cong e) {!!}) -- (h X i σ))
 where
  j : (n : ℕ) → is-prop (X n)
  j n = prop-if-semidecidable (σ n)
  {-
  e : ∃ X ≃ Σ X
  e = prop-is-equivalent-to-its-truncation i
  -}

\end{code}

TODO:

Countable-Semidecidability-Special-Choice 𝓤

implies that Ωˢᵈ is a dominance, i.e.

semidecidable-closed-under-Σ

\begin{code}

being-semidecidable-is-prop : {X : 𝓤 ̇  } → is-prop (is-semidecidable X)
being-semidecidable-is-prop = ∥∥-is-prop

Semidecidable-Closed-Under-Σ : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Closed-Under-Σ 𝓤 𝓥 = (P : 𝓤 ̇  )
                                 → is-semidecidable P
                                 → (Q : P → 𝓥 ̇  )
                                 → ((p : P) → is-semidecidable (Q p))
                                 → is-semidecidable (Σ Q)

𝟘-has-semidecidability-structure : semidecidability-structure 𝟘
𝟘-has-semidecidability-structure = ϕ , e
 where
  ϕ : ℕ → 𝟚
  ϕ _ = ₀
  ϕ-is-not-₁-anywhere : ¬ (∃ n ꞉ ℕ , ϕ n ≡ ₁)
  ϕ-is-not-₁-anywhere = forall₀-implies-not-exists₁ pt ϕ (λ _ → refl)
  e : 𝟘 ≃ (∃ n ꞉ ℕ , ϕ n ≡ ₁)
  e = ≃-sym (lr-implication negations-are-equiv-to-𝟘 ϕ-is-not-₁-anywhere)

𝟘-is-semidecidable : is-semidecidable 𝟘
𝟘-is-semidecidable = ∣ 𝟘-has-semidecidability-structure ∣

empty-types-have-semidecidability-structure : {X : 𝓤 ̇  } → is-empty X
                                            → semidecidability-structure X
empty-types-have-semidecidability-structure e =
 semidecidability-structure-cong
  (≃-sym (lr-implication negations-are-equiv-to-𝟘 e))
  𝟘-has-semidecidability-structure

empty-types-are-semidecidable : {X : 𝓤 ̇  } → is-empty X → is-semidecidable X
empty-types-are-semidecidable e =
 ∣ empty-types-have-semidecidability-structure e ∣

open import NaturalsOrder
open import Fin-Properties

-- TODO: Move
decidable-⇔ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → X ⇔ Y
               → decidable X
               → decidable Y
decidable-⇔ {𝓤} {𝓥} {X} {Y} (f , g) (inl  x) = inl (f x)
decidable-⇔ {𝓤} {𝓥} {X} {Y} (f , g) (inr nx) = inr (nx ∘ g)

open import CompactTypes
Compact-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → X ≃ Y
             → Compact X {𝓦}
             → Compact Y {𝓦}
Compact-cong {𝓤} {𝓥} {𝓦} {X} {Y} f c A δ =
 decidable-⇔ (⌜ g ⌝ , ⌜ g ⌝⁻¹) (c B d)
  where
   B : X → 𝓦 ̇
   B x = A (⌜ f ⌝ x)
   g : Σ B ≃ Σ A
   g = Σ-change-of-variable A ⌜ f ⌝ (⌜⌝-is-equiv f)
   d : detachable B
   d x = δ (⌜ f ⌝ x)

-- TODO: Promote this to another equivalent version of semidecidability-structure?
-- TODO: Also add for the version → 𝟚?
least-witness : (A : ℕ → 𝓤 ̇  )
              → ((n : ℕ) → is-prop (A n))
              → detachable A
              → Σ B ꞉ (ℕ → 𝓤 ̇  ) , ((n : ℕ) → is-prop (B n)) × detachable B × (∃ A ≃ Σ B)
least-witness {𝓤} A A-is-prop-valued A-is-detachable =
 B , B-is-prop-valued , B-is-detachable , γ
 where
   B : ℕ → 𝓤 ̇
   B n = A n × is-empty (Σ r ꞉ Fin' n , A (pr₁ r))
   B-is-detachable : detachable B
   B-is-detachable n = ×-preserves-decidability (A-is-detachable n) (¬-preserves-decidability σ)
    where
     σ : decidable (Σ r ꞉ Fin' n , A (pr₁ r))
     σ = Compact-cong (≃-Fin n) Fin-Compact (A ∘ pr₁)
          (λ r → A-is-detachable (pr₁ r))
   B-is-prop-valued : (n : ℕ) → is-prop (B n)
   B-is-prop-valued n = ×-is-prop (A-is-prop-valued n) (negations-are-props fe)
   ΣB-is-prop : is-prop (Σ B)
   ΣB-is-prop (n , a , min) (n' , a' , min') =
    to-subtype-≡ B-is-prop-valued (κ (<-linear n n'))
     where
      κ : (n < n') + (n ≡ n') + (n' < n)
        → n ≡ n'
      κ (inl k)       = 𝟘-elim (min' ((n , k) , a))
      κ (inr (inl e)) = e
      κ (inr (inr l)) = 𝟘-elim (min ((n' , l) , a'))
   γ : ∃ A ≃ Σ B
   γ = logically-equivalent-props-are-equivalent ∥∥-is-prop ΣB-is-prop f g
    where
     g : Σ B → ∥ Σ A ∥
     g (n , a , _) = ∣ n , a ∣
     f : ∥ Σ A ∥ → Σ B
     f = ∥∥-rec ΣB-is-prop h
      where
       h : Σ A → Σ B
       h (n , a) = k , a' , ν
        where
         u : Σμ A
         u = minimal-from-given A A-is-detachable (n , a)
         k : ℕ
         k = pr₁ u
         a' : A k
         a' = pr₁ (pr₂ u)
         min : (m : ℕ) → A m → k ≤ m
         min = pr₂ (pr₂ u)
         ν : is-empty (Σ r ꞉ Fin' k , A (pr₁ r))
         ν ((m , l) , aₘ) = less-not-bigger-or-equal m k l (min m aₘ)

\end{code}

We should now have enough...

\begin{code}

semidecidable-closed-under-Σ : Semidecidability-Closed-Under-Special-ω-Joins 𝓤
                             → Semidecidable-Closed-Under-Σ 𝓥 𝓤
semidecidable-closed-under-Σ {𝓤} H P ρ Q σ = ∥∥-rec being-semidecidable-is-prop γ ρ
 where
  γ : semidecidability-structure P
    → is-semidecidable (Σ Q)
  γ (α , e) = is-semidecidable-cong ΣQ₂-ΣQ-equiv ΣQ₂-is-semidecidable
   where
    Q-is-prop-valued : (p : P) → is-prop (Q p)
    Q-is-prop-valued p = prop-if-semidecidable (σ p)

    W : Σ Q₁ ꞉ (ℕ → 𝓤₀ ̇  ) , ((n : ℕ) → is-prop (Q₁ n))
                           × detachable Q₁
                           × ((∃ n ꞉ ℕ , α n ≡ ₁) ≃ Σ Q₁)
    W = least-witness (λ n → α n ≡ ₁) (λ n → 𝟚-is-set)
                      (λ n → 𝟚-is-discrete (α n) ₁)

    Q₁ : ℕ → 𝓤₀ ̇
    Q₁ = pr₁ W
    Q₁-is-prop-valued : (n : ℕ) → is-prop (Q₁ n)
    Q₁-is-prop-valued = pr₁ (pr₂ W)
    Q₁-is-detachable : detachable Q₁
    Q₁-is-detachable = pr₁ (pr₂ (pr₂ W))
    ΣQ₁-equiv : (∃ n ꞉ ℕ , α n ≡ ₁) ≃ Σ Q₁
    ΣQ₁-equiv = pr₂ (pr₂ (pr₂ W))
    ΣQ₁-to-P : Σ Q₁ → P
    ΣQ₁-to-P = ⌜ e ⌝⁻¹ ∘ ⌜ ΣQ₁-equiv ⌝⁻¹

    Q₂ : ℕ → 𝓤 ̇
    Q₂ n = Σ q ꞉ Q₁ n , Q (ΣQ₁-to-P (n , q))
    Q₂-is-prop-valued : (n : ℕ) → is-prop (Q₂ n)
    Q₂-is-prop-valued n = Σ-is-prop (Q₁-is-prop-valued n)
                           (λ q₁ → Q-is-prop-valued (ΣQ₁-to-P (n , q₁)))

    ΣQ₂-is-prop : is-prop (Σ Q₂)
    ΣQ₂-is-prop (n , q₁ , q) (n' , q₁' , q') =
     to-subtype-≡ Q₂-is-prop-valued
                  (ap pr₁ (equiv-to-prop (≃-sym ΣQ₁-equiv) ∥∥-is-prop
                            (n , q₁) (n' , q₁')))

    ΣQ₂-ΣQ-equiv : Σ Q₂ ≃ Σ Q
    ΣQ₂-ΣQ-equiv = logically-equivalent-props-are-equivalent ΣQ₂-is-prop
                    (Σ-is-prop (prop-if-semidecidable ρ)
                    (λ p → prop-if-semidecidable (σ p)))
                    f g
     where
      f : Σ Q₂ → Σ Q
      f (n , q₁ , q) = (ΣQ₁-to-P (n , q₁) , q)
      g : Σ Q → Σ Q₂
      g (p , q) = (n , q₁ , transport Q (prop-if-semidecidable ρ p p') q)
       where
        n : ℕ
        n = pr₁ (⌜ ΣQ₁-equiv ⌝ (⌜ e ⌝ p))
        q₁ : Q₁ n
        q₁ = pr₂ (⌜ ΣQ₁-equiv ⌝ (⌜ e ⌝ p))
        p' : P
        p' = ΣQ₁-to-P (n , q₁)

    ΣQ₂-is-semidecidable : is-semidecidable (Σ Q₂)
    ΣQ₂-is-semidecidable = H Q₂ ΣQ₂-is-prop τ
     where
      τ : (n : ℕ) → is-semidecidable (Q₂ n)
      τ n = κ (Q₁-is-detachable n)
       where
        κ : decidable (Q₁ n) → is-semidecidable (Q₂ n)
        κ (inl  q₁) = is-semidecidable-cong claim (σ p)
         where
          p : P
          p = ΣQ₁-to-P (n , q₁)
          claim : Q p ≃ Q₂ n
          claim = logically-equivalent-props-are-equivalent
                   (Q-is-prop-valued p) (Q₂-is-prop-valued n)
                   ϕ ψ
           where
            ϕ : Q p → Q₂ n
            ϕ q = q₁ , q
            ψ : Q₂ n → Q p
            ψ (q₁ , q) =
             transport Q (prop-if-semidecidable ρ (ΣQ₁-to-P (n , q₁)) p) q
        κ (inr nq₁) = empty-types-are-semidecidable claim
         where
          claim : is-empty (Q₂ n)
          claim (q₁ , q) = nq₁ q₁

Escardo-Knapp-Choice : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Escardo-Knapp-Choice 𝓤 𝓥 = (P : 𝓤 ̇  ) (Q : 𝓥 ̇  )
                         → is-semidecidable P
                         → (P → is-semidecidable Q)
                         → ∥ (P → semidecidability-structure Q) ∥

theorem-3-1 : Semidecidable-Closed-Under-Σ 𝓤 𝓥
            → Escardo-Knapp-Choice 𝓤 𝓥
theorem-3-1 H P Q ρ σ = ∥∥-functor g τ
 where
  τ : is-semidecidable (P × Q)
  τ = H P ρ (λ _ → Q) σ
  f : P → (P × Q) ≃ Q
  f p = logically-equivalent-props-are-equivalent
         (×-is-prop (prop-if-semidecidable ρ) Q-is-prop) Q-is-prop
          pr₂ (λ q → p , q)
   where
    Q-is-prop : is-prop Q
    Q-is-prop = prop-if-semidecidable (σ p)
  g : semidecidability-structure (P × Q) → (P → semidecidability-structure Q)
  g 𝕤 p = semidecidability-structure-cong (f p) 𝕤

\end{code}

\begin{code}



Semidecidable-Dominance-Axiom : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Dominance-Axiom 𝓤 𝓥 = (P : 𝓤 ̇  )
                                  → is-semidecidable P
                                  → (Q : 𝓥 ̇  )
                                  → (P → is-semidecidable Q)
                                  → is-semidecidable (P × Q)

-- TODO: Reorganize using Dominance?
closure-under-Σ-criterion : Semidecidable-Dominance-Axiom 𝓤 (𝓤 ⊔ 𝓥)
                          → Semidecidable-Closed-Under-Σ 𝓤 𝓥
closure-under-Σ-criterion {𝓤} {𝓥} D P ρ Q σ = τ
 where
  i : is-prop P
  i = prop-if-semidecidable ρ
  j : (p : P) → is-prop (Q p)
  j p = prop-if-semidecidable (σ p)
  Q' : 𝓤 ⊔ 𝓥 ̇
  Q' = Σ Q
  k : is-prop Q'
  k = Σ-is-prop i j
  e : (p : P) → Q' ≃ Q p
  e p = logically-equivalent-props-are-equivalent k (j p)
         (λ (p' , q) → transport Q (i p' p) q)
         (λ q → p , q)
  τ : is-semidecidable (Σ Q)
  τ = is-semidecidable-cong (Σ-cong e) (D P ρ Q' τ')
   where
    τ' : P → is-semidecidable Q'
    τ' p = is-semidecidable-cong (≃-sym (e p)) (σ p)

theorem-3-1-converse : Escardo-Knapp-Choice 𝓤 (𝓤 ⊔ 𝓥)
                     → Semidecidable-Closed-Under-Σ 𝓤 𝓥
theorem-3-1-converse {𝓤} {𝓥} ekc = closure-under-Σ-criterion γ
 where
  γ : Semidecidable-Dominance-Axiom 𝓤 (𝓤 ⊔ 𝓥)
  γ P ρ Q σ = ∥∥-rec being-semidecidable-is-prop r ρ
   where
    r : semidecidability-structure P → is-semidecidable (P × Q)
    r (α , e) = ∥∥-functor s (ekc P Q ρ σ)
     where
      to-P : (∃ n ꞉ ℕ , α n ≡ ₁) → P
      to-P = ⌜ e ⌝⁻¹
      s : (P → semidecidability-structure Q)
        → semidecidability-structure (P × Q)
      s σ⁺ = ⌜ semidecidability-pairing-lemma ⌝ τ
       where
        β : P → (ℕ → 𝟚)
        β p = pr₁ (σ⁺ p)
        φ : ℕ × ℕ → 𝓤₀ ̇
        φ (n , m) = Σ b ꞉ α n ≡ ₁ , β (to-P ∣ n , b ∣) m ≡ ₁
        φ-is-detachable : detachable φ
        φ-is-detachable (n , m) = decidable-closed-under-Σ
                                   𝟚-is-set
                                   (𝟚-is-discrete (α n) ₁)
                                   (λ b → 𝟚-is-discrete (β (to-P ∣ n , b ∣) m) ₁)
        φ-is-prop-valued : (k : ℕ × ℕ) → is-prop (φ k)
        φ-is-prop-valued k = Σ-is-prop 𝟚-is-set (λ b → 𝟚-is-set)
        φ⁺ : ℕ × ℕ → Ω 𝓤₀
        φ⁺ k = φ k , φ-is-prop-valued k

        τ : Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ ,  Ψ n m ≡ ₁)
        τ = ⌜ uncurry-lemma ⌝ τ'
         where
          uncurry-lemma :
             (Σ Ψ ꞉ (ℕ × ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ ,  Ψ (n , m) ≡ ₁))
           ≃ (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ ,  Ψ n m ≡ ₁))
          uncurry-lemma = ≃-sym (Σ-change-of-variable _
                                  ⌜ μ ⌝⁻¹ (⌜⌝⁻¹-is-equiv μ))
           where
            μ : (ℕ × ℕ → 𝟚) ≃ (ℕ → ℕ → 𝟚)
            μ = curry-uncurry (λ _ _ → fe)

          τ' : (Σ Ψ ꞉ (ℕ × ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁))
          τ' = Ψ , (P × Q                              ≃⟨ I  ⟩
                   (∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m))     ≃⟨ II ⟩
                   (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁) ■)
           where
            χ : (Σ A ꞉ (ℕ × ℕ → Ω 𝓤₀) , is-decidable-subset A) → (ℕ × ℕ → 𝟚)
            χ = ⌜ 𝟚-classifies-decidable-subsets fe fe pe ⌝⁻¹
            Ψ : ℕ × ℕ → 𝟚
            Ψ = χ (φ⁺ , φ-is-detachable)

            II = ∥∥-cong (Σ-cong (λ n → Σ-cong
                                  (λ m → logically-equivalent-props-are-equivalent
                                          (φ-is-prop-valued (n , m))
                                          𝟚-is-set
                                          (rl-implication (lemma n m))
                                          (lr-implication (lemma n m)))))
             where
              lemma : (n m : ℕ) → χ (φ⁺ , φ-is-detachable) (n , m) ≡ ₁ ⇔ (n , m) ∈ φ⁺
              lemma n m = pr₂ (𝟚-classifies-decidable-subsets-values fe fe pe
                                φ⁺ φ-is-detachable (n , m))
            I  = logically-equivalent-props-are-equivalent j ∥∥-is-prop f g
             where
              j : is-prop (P × Q)
              j = prop-criterion
                   (λ (p , q) → ×-is-prop (prop-if-semidecidable ρ)
                                          (prop-if-semidecidable (σ p)))
              e' : (p : P) → Q ≃ (∃ m ꞉ ℕ , β p m ≡ ₁)
              e' p = pr₂ (σ⁺ p)
              g : (∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)) → P × Q
              g = ∥∥-rec j g'
               where
                g' : (Σ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)) → P × Q
                g' (n , m , b , b') = p , ⌜ e' p ⌝⁻¹ ∣ m , b' ∣
                 where
                  p : P
                  p = to-P ∣ n , b ∣
              f : P × Q → ∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)
              f (p , q) = ∥∥-rec ∥∥-is-prop f' (⌜ e ⌝ p)
               where
                f' : (Σ n ꞉ ℕ , α n ≡ ₁)
                   → ∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)
                f' (n , b) = ∥∥-functor f'' (⌜ e' p' ⌝ q)
                 where
                  p' : P
                  p' = to-P ∣ n , b ∣
                  f'' : (Σ m ꞉ ℕ , β p' m ≡ ₁)
                      → (Σ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m))
                  f'' (m , b') = n , m , b , b'

\end{code}

Summary:

   EKCˢᵈ <=> Dominance Axiom
    ^                     ^
    |                     |
    |                     |
Special CC <=> Special ω-joins in Ωˢᵈ
    ^                     ^
    |                     |
    |                     |
Semidecidable CC ==> ω-joins in Ωˢᵈ

The conjecture is that ω-joins in Ωˢᵈ is equivalent to some form of countable choice. But which?!

Discussion:

 * Ωˢᵈ is closed under finitary (nullary + binary) joins
 * Ωˢᵈ is closed under finitary (nullary + binary) meets
 * LPO <=> Ωˢᵈ ≃ 𝟚.
 * If LPO holds, then Ωˢᵈ is closed under negation. Conversely,
   If
     X ≃ ∃ n ꞉ ℕ , α n ≡ ₁
   and
     ∀ n ꞉ ℕ , γ n ≡ ₁ ≃ ¬ X
                       ≃ ∃ n ꞉ ℕ , β n ≡ ₁

 * TODO: Think about implication
