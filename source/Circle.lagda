Tom de Jong, 28 January 2020
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import Integers
open import Integers-Properties
open import Integers-SymmetricInduction

open import UF-Embeddings
open import UF-Equiv hiding (_≅_)
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts

open import UF-PropTrunc
open import UF-Univalence
open import UF-UA-FunExt

open import UF-SIP -- Maybe use MGS-SIP?

module Circle
        (pt : propositional-truncations-exist)
        (ua : is-univalent 𝓤₀)
       where

fe₀ : funext 𝓤₀ 𝓤₀
fe₀ = univalence-gives-funext ua

open PropositionalTruncation pt
open sip
open sip-with-axioms

Tℤ : 𝓤₁ ̇
Tℤ = Σ X ꞉ 𝓤₀ ̇ , Σ f ꞉ (X → X) , ∥ (ℤ , succ-ℤ) ≡ (X , f) ∥

base : Tℤ
base = (ℤ , succ-ℤ , ∣ refl ∣)

Tℤ-is-connected : (X Y : Tℤ) → ∥ X ≡ Y ∥
Tℤ-is-connected (X , f , p) (Y , g , q) = ∥∥-rec ∥∥-is-prop ϕ p
 where
  ϕ : (ℤ , succ-ℤ) ≡ (X , f)
    → ∥ X , f , p ≡ Y , g , q ∥
  ϕ refl = ∥∥-rec ∥∥-is-prop ψ q
   where
    ψ : (ℤ , succ-ℤ) ≡ (Y , g)
      → ∥ ℤ , succ-ℤ , p ≡ Y , g , q ∥
    ψ refl = ∣ ap ⌜ Σ-assoc ⌝ (to-subtype-≡ (λ _ → ∥∥-is-prop) refl) ∣

\end{code}

\begin{code}

_≅_ : Tℤ → Tℤ → 𝓤₀ ̇
(X , f , _) ≅ (Y , g , _) = Σ e ꞉ (X → Y) , is-equiv e
                                          × (e ∘ f ≡ g ∘ e)

Tℤ-structure : 𝓤₀ ̇ → 𝓤₀ ̇
Tℤ-structure X = X → X

Tℤ⁻ : 𝓤₁ ̇
Tℤ⁻ = Σ X ꞉ 𝓤₀ ̇ , Tℤ-structure X

sns-data : SNS Tℤ-structure 𝓤₀
sns-data = (ι , ρ , θ)
 where
  ι : (X Y : Tℤ⁻) → ⟨ X ⟩ ≃ ⟨ Y ⟩ → 𝓤₀ ̇
  ι (X , f) (Y , g) (e , _) = e ∘ f ≡ g ∘ e
  ρ : (X : Tℤ⁻) → ι X X (≃-refl ⟨ X ⟩)
  ρ (X , f) = refl
  h : {X : 𝓤₀ ̇ } {f g : Tℤ-structure X}
    → canonical-map ι ρ f g ∼ id {𝓤₀} {f ≡ g}
  h refl = refl
  θ : {X : 𝓤₀ ̇} (f g : Tℤ-structure X)
    → is-equiv (canonical-map ι ρ f g)
  θ f g = equiv-closed-under-∼ _ _ (id-is-equiv (f ≡ g)) h

characterization-of-Tℤ-≡ : (X Y : Tℤ)
                         → (X ≡ Y) ≃ (X ≅ Y)
characterization-of-Tℤ-≡ =
 characterization-of-≡-with-axioms ua
  sns-data
  (λ X f → ∥ (ℤ , succ-ℤ) ≡ (X , f) ∥)
  (λ X f → ∥∥-is-prop)

to-Tℤ-≡ : (X Y : Tℤ) → X ≅ Y → X ≡ Y
to-Tℤ-≡ X Y = ⌜ characterization-of-Tℤ-≡ X Y ⌝⁻¹

\end{code}

\begin{code}

loop-≅ : base ≅ base
loop-≅ = (succ-ℤ , succ-ℤ-is-equiv , refl)

loop : base ≡ base
loop = to-Tℤ-≡ base base loop-≅

\end{code}

\begin{code}

fundamental-group-of-circle-is-ℤ : (base ≡ base) ≃ ℤ
fundamental-group-of-circle-is-ℤ =
 (base ≡ base)                                            ≃⟨ I   ⟩
 (Σ e ꞉ (ℤ → ℤ) , is-equiv e × (e ∘ succ-ℤ ≡ succ-ℤ ∘ e)) ≃⟨ II  ⟩
 (Σ e ꞉ (ℤ → ℤ) , is-equiv e × (e ∘ succ-ℤ ∼ succ-ℤ ∘ e)) ≃⟨ III ⟩
 (Σ e ꞉ (ℤ → ℤ) , (e ∘ succ-ℤ ∼ succ-ℤ ∘ e) × is-equiv e) ≃⟨ IV  ⟩
 (Σ e ꞉ (ℤ → ℤ) , (e ∘ succ-ℤ ∼ succ-ℤ ∘ e))              ≃⟨ V   ⟩
 ℤ                                                        ■
  where
   I   = characterization-of-Tℤ-≡ base base
   II  = Σ-cong (λ e → ×-cong (≃-refl (is-equiv e))
                              (≃-funext fe₀ (e ∘ succ-ℤ) (succ-ℤ ∘ e)))
   III = Σ-cong (λ e → ×-comm)
   IV  = Σ-cong γ
    where
     γ : (e : ℤ → ℤ)
       → (e ∘ succ-ℤ ∼ succ-ℤ ∘ e) × is-equiv e
       ≃ (e ∘ succ-ℤ ∼ succ-ℤ ∘ e)
     γ e = qinveq pr₁ (ϕ , η , ε)
      where
       ϕ : e ∘ succ-ℤ ∼ succ-ℤ ∘ e
         → (e ∘ succ-ℤ ∼ succ-ℤ ∘ e) × is-equiv e
       ϕ c = (c , is-equiv-if-commute-with-succ-ℤ e c)
       η : ϕ ∘ pr₁ ∼ id
       η (i , c) = to-subtype-≡ (λ _ → being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀ e) refl
       ε : pr₁ ∘ ϕ ∼ id
       ε _ = refl
   V   = ℤ-symmetric-induction fe₀ (λ _ → ℤ) (λ _ → succ-ℤ-≃)

\end{code}

\begin{code}

to-≃-of-⟨⟩ : {X Y : Tℤ} → X ≡ Y → ⟨ X ⟩ ≃ ⟨ Y ⟩
to-≃-of-⟨⟩ {X} {Y} p = pr₁ c , pr₁ (pr₂ c)
 where
  c = ⌜ characterization-of-Tℤ-≡ X Y ⌝ p

to-≃-of-⟨⟩-is-idtoeq : {X Y : Tℤ} (p : X ≡ Y)
                     → idtoeq ⟨ X ⟩ ⟨ Y ⟩ (ap ⟨_⟩ p) ≡ to-≃-of-⟨⟩ p
to-≃-of-⟨⟩-is-idtoeq refl = refl

idtoeq-of-loop-is-succ-ℤ-≃ : idtoeq ℤ ℤ (ap ⟨_⟩ loop) ≡ succ-ℤ-≃
idtoeq-of-loop-is-succ-ℤ-≃ =
 idtoeq ℤ ℤ (ap ⟨_⟩ loop)                        ≡⟨ I    ⟩
 to-≃-of-⟨⟩ loop                                 ≡⟨ refl ⟩
 (pr₁ (ϕ loop)       , pr₁ (pr₂ (ϕ loop)))       ≡⟨ refl ⟩
 (pr₁ (ϕ (ψ loop-≅)) , pr₁ (pr₂ (ϕ (ψ loop-≅)))) ≡⟨ II   ⟩
 (pr₁ loop-≅         , pr₁ (pr₂ loop-≅))         ∎
  where
   ϕ : base ≡ base → base ≅ base
   ϕ = ⌜ characterization-of-Tℤ-≡ base base ⌝
   ψ : base ≅ base → base ≡ base
   ψ = ⌜ characterization-of-Tℤ-≡ base base ⌝⁻¹
   I  = to-≃-of-⟨⟩-is-idtoeq loop
   II = ap (λ - → (pr₁ - , pr₁ (pr₂ -))) (ε loop-≅)
    where
     ε : ϕ ∘ ψ ∼ id
     ε = inverses-are-sections ϕ (⌜⌝-is-equiv (characterization-of-Tℤ-≡ base base))

\end{code}

\begin{code}

⟨_⟩₂ : (X : Tℤ) → ⟨ X ⟩ → ⟨ X ⟩
⟨ (X , f , t) ⟩₂ = f

\end{code}

\begin{code}

_⁻ : Tℤ → Tℤ⁻
X ⁻ = ⟨ X ⟩ , ⟨ X ⟩₂

Tℤ-≡-from-Tℤ⁻-≡ : {X Y : Tℤ}
                → X ⁻ ≡ Y ⁻
                → X ≡ Y
Tℤ-≡-from-Tℤ⁻-≡ q = ap ⌜ Σ-assoc ⌝ (to-subtype-≡ (λ _ → ∥∥-is-prop) q)

Tℤ-prop-induction : {𝓤 : Universe} {P : Tℤ → 𝓤 ̇ }
                  → ((X : Tℤ) → is-prop (P X))
                  → P base
                  → (X : Tℤ) → P X
Tℤ-prop-induction {𝓤} {P} i p (X , f , t) = ∥∥-rec (i (X , f , t)) γ t
 where
  γ : (ℤ , succ-ℤ) ≡ (X , f) → P (X , f , t)
  γ q = transport P (Tℤ-≡-from-Tℤ⁻-≡ q) p

\end{code}

\begin{code}

module Tℤ-rec
        {A : 𝓤 ̇ }
        (fe : funext 𝓤 𝓤)
       where

 module _
         ((a , p) : Σ a' ꞉ A , a' ≡ a')
        where

  -- Bezem, Buchholtz, Grayson
  BBG : (X : Tℤ⁻) → 𝓤 ̇
  BBG (X , f) = Σ a' ꞉ A , Σ h ꞉ (X → a ≡ a') , ((x : X) → h (f x) ≡ p ∙ h x)

  BBG-base : 𝓤 ̇
  BBG-base = BBG (ℤ , succ-ℤ)

  BBG-base-is-singleton : is-singleton BBG-base
  BBG-base-is-singleton = equiv-to-singleton ϕ (singleton-types-are-singletons a)
   where
    ϕ : BBG-base ≃ singleton-type a
    ϕ = Σ-cong ψ
     where
      ψ : (a' : A)
        → (Σ h ꞉ (ℤ → a ≡ a') , ((z : ℤ) → h (succ-ℤ z) ≡ p ∙ h z))
        ≃ (a ≡ a')
      ψ a' = ℤ-symmetric-induction (lower-funext 𝓤 𝓤 fe) (λ _ → a ≡ a') (λ _ → g)
       where
        g : (a ≡ a') ≃ (a ≡ a')
        g = ((p ∙_) , ∙-is-equiv-left p)

  BBG-is-singleton : ((X , f , _) : Tℤ) → is-singleton (BBG (X , f))
  BBG-is-singleton = γ
   where
    abstract
     γ = Tℤ-prop-induction (λ _ → being-singleton-is-prop fe)
                      BBG-base-is-singleton

  Tℤ-rec : Tℤ → A
  Tℤ-rec X = pr₁ (center (BBG-is-singleton X))

  Tℤ-rec-lemma₁ : (X : Tℤ) → (⟨ X ⟩) → a ≡ Tℤ-rec X
  Tℤ-rec-lemma₁ X = pr₁ (pr₂ (center (BBG-is-singleton X)))

  Tℤ-rec-lemma₂ : (X : Tℤ) (x : ⟨ X ⟩)
                → Tℤ-rec-lemma₁ X (⟨ X ⟩₂ x) ≡ p ∙ Tℤ-rec-lemma₁ X x
  Tℤ-rec-lemma₂ X = pr₂ (pr₂ (center (BBG-is-singleton X)))

  ap-Tℤ-rec-lemma : {X Y : Tℤ} (e : X ≡ Y) (x : ⟨ X ⟩)
                  → ap Tℤ-rec e
                  ≡ (Tℤ-rec-lemma₁ X x) ⁻¹
                    ∙ (Tℤ-rec-lemma₁ Y (⌜ idtoeq ⟨ X ⟩ ⟨ Y ⟩ (ap ⟨_⟩ e) ⌝ x))
  ap-Tℤ-rec-lemma {X} {Y} refl x =
   ap Tℤ-rec refl                                     ≡⟨ refl ⟩
   refl                                               ≡⟨ γ    ⟩
   (t X x) ⁻¹ ∙ (t X x)                               ≡⟨ refl ⟩
   (t X x) ⁻¹ ∙ (t X (⌜ idtoeq ⟨ X ⟩ ⟨ Y ⟩ refl ⌝ x)) ∎
    where
     t : (W : Tℤ) → ⟨ W ⟩ → a ≡ Tℤ-rec W
     t = Tℤ-rec-lemma₁
     γ = (left-inverse (t X x)) ⁻¹

  ap-Tℤ-rec-loop-lemma₁ : ap Tℤ-rec loop
                        ≡ (Tℤ-rec-lemma₁ base 𝟎) ⁻¹ ∙ p ∙ Tℤ-rec-lemma₁ base 𝟎
  ap-Tℤ-rec-loop-lemma₁ =
   ap Tℤ-rec loop                                            ≡⟨ I   ⟩
   (t base 𝟎) ⁻¹ ∙ (t base (⌜ idtoeq ℤ ℤ (ap ⟨_⟩ loop) ⌝ 𝟎)) ≡⟨ II  ⟩
   (t base 𝟎) ⁻¹ ∙ (t base (succ-ℤ 𝟎))                       ≡⟨ III ⟩
   (t base 𝟎) ⁻¹ ∙ (p ∙ t base 𝟎)                            ≡⟨ IV  ⟩
   (t base 𝟎) ⁻¹ ∙ p ∙ t base 𝟎                              ∎
    where
     t : (X : Tℤ) → ⟨ X ⟩ → a ≡ Tℤ-rec X
     t = Tℤ-rec-lemma₁
     I   = ap-Tℤ-rec-lemma loop 𝟎
     II  = ap (λ - → (t base 𝟎) ⁻¹ ∙ (t base (⌜ - ⌝ 𝟎)))
            idtoeq-of-loop-is-succ-ℤ-≃
     III = ap (λ - → (t base 𝟎) ⁻¹ ∙ -) (Tℤ-rec-lemma₂ base 𝟎)
     IV  = ∙assoc (t base 𝟎 ⁻¹) p (t base 𝟎) ⁻¹

  ap-Tℤ-rec-loop-lemma₂ : ap Tℤ-rec loop
                        ≡ transport (λ - → - ≡ -) (Tℤ-rec-lemma₁ base 𝟎) p
  ap-Tℤ-rec-loop-lemma₂ =
   ap Tℤ-rec loop                                       ≡⟨ I  ⟩
   (Tℤ-rec-lemma₁ base 𝟎) ⁻¹ ∙ p ∙ Tℤ-rec-lemma₁ base 𝟎 ≡⟨ II ⟩
   transport (λ - → - ≡ -) (Tℤ-rec-lemma₁ base 𝟎) p     ∎
    where
     I  = ap-Tℤ-rec-loop-lemma₁
     II = (transport-along-≡ (Tℤ-rec-lemma₁ base 𝟎) p) ⁻¹

  Tℤ-rec-comp : (Tℤ-rec base , ap Tℤ-rec loop) ≡ (a , p)
  Tℤ-rec-comp = (to-Σ-≡ ((Tℤ-rec-lemma₁ base 𝟎) , (ap-Tℤ-rec-loop-lemma₂ ⁻¹))) ⁻¹

\end{code}

\begin{code}

⟨⟩-is-set : (X : Tℤ) → is-set ⟨ X ⟩
⟨⟩-is-set = Tℤ-prop-induction (λ _ → being-set-is-prop fe₀) ℤ-is-set

⟨⟩₂-is-equiv : (X : Tℤ) → is-equiv ⟨ X ⟩₂
⟨⟩₂-is-equiv = Tℤ-prop-induction
                (λ X → being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀ ⟨ X ⟩₂)
                succ-ℤ-is-equiv

⟨_⟩₂-≃ : (X : Tℤ) → ⟨ X ⟩ ≃ ⟨ X ⟩
⟨_⟩₂-≃ X = (⟨ X ⟩₂ , ⟨⟩₂-is-equiv X)

⟨_⟩₂⁻¹ : (X : Tℤ) → ⟨ X ⟩ → ⟨ X ⟩
⟨_⟩₂⁻¹ X = ⌜ ⟨ X ⟩₂-≃ ⌝⁻¹


\end{code}

\begin{code}

≅-comp-Tℤ : (X Y Z : Tℤ) → X ≅ Y → Y ≅ Z → X ≅ Z
≅-comp-Tℤ X Y Z (e , i , c) (e' , i' , c') =
 (e' ∘ e , ∘-is-equiv-abstract i i' , dfunext fe₀ γ)
  where
   γ : e' ∘ e ∘ ⟨ X ⟩₂ ∼ ⟨ Z ⟩₂ ∘ e' ∘ e
   γ x = e' (e (⟨ X ⟩₂ x)) ≡⟨ ap e' (happly c x) ⟩
         e' (⟨ Y ⟩₂ (e x)) ≡⟨ happly c' (e x) ⟩
         ⟨ Z ⟩₂ (e' (e x)) ∎

to-≡-of-≅ : (X Y : Tℤ) {f g : X ≅ Y}
          → pr₁ f ∼ pr₁ g
          → f ≡ g
to-≡-of-≅ X Y h =
 to-subtype-≡
  (λ f' → ×-is-prop (being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀ f')
         (equiv-to-prop (≃-funext fe₀ _ _)
          (Π-is-prop fe₀ (λ _ → ⟨⟩-is-set Y))))
  (dfunext fe₀ h)

to-Tℤ-≡-comp : (X Y Z : Tℤ) (f : X ≅ Y) (g : Y ≅ Z)
             → to-Tℤ-≡ X Z (≅-comp-Tℤ X Y Z f g)
             ≡ to-Tℤ-≡ X Y f ∙ to-Tℤ-≡ Y Z g
to-Tℤ-≡-comp X Y Z f g =
 ϕ X Z (≅-comp-Tℤ X Y Z f g)                 ≡⟨ I    ⟩
 ϕ X Z (ψ X Z (p ∙ q))                       ≡⟨ II   ⟩
 p ∙ q                                       ≡⟨ refl ⟩
 ϕ X Y f ∙ ϕ Y Z g                           ∎
  where
   ϕ : (X Y : Tℤ) → X ≅ Y → X ≡ Y
   ϕ = to-Tℤ-≡
   ψ : (X Y : Tℤ) → X ≡ Y → X ≅ Y
   ψ X Y = ⌜ characterization-of-Tℤ-≡ X Y ⌝
   p : X ≡ Y
   p = ϕ X Y f
   q : Y ≡ Z
   q = ϕ Y Z g
   II = η X Z (p ∙ q)
    where
     η : (X Y : Tℤ) → ϕ X Y ∘ ψ X Y ∼ id
     η X Y = inverses-are-retractions (ψ X Y)
              (⌜⌝-is-equiv (characterization-of-Tℤ-≡ X Y))
   I = ap (ϕ X Z) γ
    -- The proofs below are done with to-≡-of-≅ (rather than directly) for
    -- type-checking efficiency reasons.
    where
     γ = ≅-comp-Tℤ X Y Z f g                 ≡⟨ to-≡-of-≅ X Z w      ⟩
         ≅-comp-Tℤ X Y Z (ψ X Y p) (ψ Y Z q) ≡⟨ (lemma X Y Z p q) ⁻¹ ⟩
         ψ X Z (p ∙ q)                       ∎
      where
       lemma : (X Y Z : Tℤ) (p : X ≡ Y) (q : Y ≡ Z)
             → ψ X Z (p ∙ q) ≡ ≅-comp-Tℤ X Y Z (ψ X Y p) (ψ Y Z q)
       lemma X Y Z refl refl = to-≡-of-≅ X Z (λ x → refl)
       w : pr₁ g ∘ pr₁ f ∼ pr₁ (ψ Y Z (to-Tℤ-≡ Y Z g)) ∘ pr₁ (ψ X Y p)
       w x = v (pr₁ f x) ∙ ap (pr₁ (ψ Y Z q)) (u x)
        where
         ε : (X Y : Tℤ) → ψ X Y ∘ ϕ X Y ∼ id
         ε X Y = inverses-are-sections (ψ X Y)
                  (⌜⌝-is-equiv (characterization-of-Tℤ-≡ X Y))
         u : pr₁ f ∼ pr₁ (ψ X Y p)
         u = happly (ap pr₁ ((ε X Y f) ⁻¹))
         v : pr₁ g ∼ pr₁ (ψ Y Z q)
         v = happly (ap pr₁ ((ε Y Z g) ⁻¹))


\end{code}

\begin{code}

Tℤ-action : (X : Tℤ) → ⟨ X ⟩ → ℤ → ⟨ X ⟩
Tℤ-action X x 𝟎       = x
Tℤ-action X x (pos n) = (⟨ X ⟩₂   ^ (succ n)) x
Tℤ-action X x (neg n) = (⟨ X ⟩₂⁻¹ ^ (succ n)) x

Tℤ-action-commutes-with-⟨⟩₂ : (X : Tℤ) (x : ⟨ X ⟩)
                            → Tℤ-action X (⟨ X ⟩₂ x)
                            ∼ ⟨ X ⟩₂ ∘ Tℤ-action X x
Tℤ-action-commutes-with-⟨⟩₂ X x 𝟎       = refl
Tℤ-action-commutes-with-⟨⟩₂ X x (pos n) =
 ap ⟨ X ⟩₂ ((commute-with-iterated-function ⟨ X ⟩₂ ⟨ X ⟩₂ (λ _ → refl) n x) ⁻¹)
Tℤ-action-commutes-with-⟨⟩₂ X x (neg n) = γ
 where
  γ : (⟨ X ⟩₂⁻¹ ^ (succ n)) (⟨ X ⟩₂ x) ≡ ⟨ X ⟩₂ ((⟨ X ⟩₂⁻¹ ^ (succ n)) x)
  γ = (commute-with-iterated-function ⟨ X ⟩₂ ⟨ X ⟩₂⁻¹ ϕ (succ n) x) ⁻¹
   where
    ϕ : ⟨ X ⟩₂ ∘ ⟨ X ⟩₂⁻¹ ∼ ⟨ X ⟩₂⁻¹ ∘ ⟨ X ⟩₂
    ϕ y = ⟨ X ⟩₂ (⟨ X ⟩₂⁻¹ y) ≡⟨ I  ⟩
          y                   ≡⟨ II ⟩
          ⟨ X ⟩₂⁻¹ (⟨ X ⟩₂ y) ∎
     where
      I  = inverses-are-sections ⟨ X ⟩₂ (⟨⟩₂-is-equiv X) y
      II = (inverses-are-retractions ⟨ X ⟩₂ (⟨⟩₂-is-equiv X) y) ⁻¹

Tℤ-action-commutes-with-⟨⟩₂-≡ : (X : Tℤ) (x : ⟨ X ⟩)
                              → Tℤ-action X (⟨ X ⟩₂ x) ≡ ⟨ X ⟩₂ ∘ Tℤ-action X x
Tℤ-action-commutes-with-⟨⟩₂-≡ X x = dfunext fe₀ (Tℤ-action-commutes-with-⟨⟩₂ X x)

Tℤ-action-base-is-shift : (x : ℤ) → Tℤ-action base x ∼ (λ y → y +ℤ x)
Tℤ-action-base-is-shift x 𝟎       = refl
Tℤ-action-base-is-shift x (pos n) = refl
Tℤ-action-base-is-shift x (neg n) = ap (λ - → (- ^ succ n) x) (ap ⌜_⌝⁻¹ ϕ)
      where
       ϕ : ⟨ base ⟩₂-≃ ≡ succ-ℤ-≃
       ϕ = to-subtype-≡ (being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀) refl

Tℤ-action-is-equiv : (X : Tℤ) (x : ⟨ X ⟩) → is-equiv (Tℤ-action X x)
Tℤ-action-is-equiv =
 Tℤ-prop-induction (λ X → Π-is-prop fe₀
                   (λ x → being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀ (Tℤ-action X x)))
                   γ
  where
   γ : (x : ℤ) → is-equiv (Tℤ-action base x)
   γ x = equiv-closed-under-∼ (λ y → y +ℤ x) (Tℤ-action base x)
          (+ℤ-is-equiv-right x) (Tℤ-action-base-is-shift x)

Tℤ-action-is-Tℤ-map : (X : Tℤ) (x : ⟨ X ⟩)
                    → (Tℤ-action X x ∘ succ-ℤ ≡ ⟨ X ⟩₂ ∘ Tℤ-action X x)
Tℤ-action-is-Tℤ-map = Tℤ-prop-induction i γ
 where
  i : (X : Tℤ)
    → is-prop ((x : ⟨ X ⟩) → (Tℤ-action X x ∘ succ-ℤ ≡ ⟨ X ⟩₂ ∘ Tℤ-action X x))
  i X = Π-is-prop fe₀
         (λ x → equiv-to-prop
                 (≃-funext fe₀ (Tℤ-action X x ∘ succ-ℤ) (⟨ X ⟩₂ ∘ Tℤ-action X x))
                 (Π-is-prop fe₀ (λ _ → ⟨⟩-is-set X)))
  γ : (x : ℤ)
    →  Tℤ-action base x ∘ succ-ℤ ≡ succ-ℤ ∘ Tℤ-action base x
  γ x = dfunext fe₀ h
   where
    h : Tℤ-action base x ∘ succ-ℤ ∼ succ-ℤ ∘ Tℤ-action base x
    h y = Tℤ-action base x (succ-ℤ y) ≡⟨ I   ⟩
          (succ-ℤ y) +ℤ x             ≡⟨ II  ⟩
          succ-ℤ (y +ℤ x)             ≡⟨ III ⟩
          succ-ℤ (Tℤ-action base x y) ∎
     where
      I   = Tℤ-action-base-is-shift x (succ-ℤ y)
      II  = right-shift-commutes-with-succ-ℤ x y
      III = ap succ-ℤ ((Tℤ-action-base-is-shift x y) ⁻¹)

Tℤ-action-≅ : (X : Tℤ) (x : ⟨ X ⟩) → base ≅ X
Tℤ-action-≅ X x =
 (Tℤ-action X x , Tℤ-action-is-equiv X x , Tℤ-action-is-Tℤ-map X x)

Tℤ-action-≡ : (X : Tℤ) (x : ⟨ X ⟩) → base ≡ X
Tℤ-action-≡ X x = to-Tℤ-≡ base X (Tℤ-action-≅ X x)

\end{code}

\begin{code}

Tℤ-action-lemma : (X : Tℤ) (x : ⟨ X ⟩)
                → Tℤ-action X (⟨ X ⟩₂ x)
                ≡ Tℤ-action X x ∘ succ-ℤ
Tℤ-action-lemma X x = Tℤ-action-commutes-with-⟨⟩₂-≡ X x
                    ∙ (Tℤ-action-is-Tℤ-map X x) ⁻¹

Tℤ-action-≡-lemma : (X : Tℤ) (x : ⟨ X ⟩)
                  → Tℤ-action-≡ X (⟨ X ⟩₂ x) ≡ loop ∙ Tℤ-action-≡ X x
Tℤ-action-≡-lemma X x = I ∙ II
{-
  Unfortunately, Agda doesn't quite like the types below and starts normalizing
  like crazy, resulting in extremely slow typechecking. Therefore, I have
  omitted the types in the proof, but left the equational reasoning to help
  human readers.
  I bet that the --experimental-lossy-unification flag would result in quick
  typechecking.

   Tℤ-action-≡ X (⟨ X ⟩₂ x)                                        ≡⟨ refl ⟩
   to-Tℤ-≡ base X (Tℤ-action-≅ X (⟨ X ⟩₂ x))                       ≡⟨ I    ⟩
   to-Tℤ-≡ base X (≅-comp-Tℤ base base X loop-≅ (Tℤ-action-≅ X x)) ≡⟨ II   ⟩
   to-Tℤ-≡ base base loop-≅ ∙ to-Tℤ-≡ base X (Tℤ-action-≅ X x)     ≡⟨ refl ⟩
   loop ∙ Tℤ-action-≡ X x                                          ∎
-}
  where
   I  = ap (to-Tℤ-≡ base X) ϕ
    where
     ϕ = to-≡-of-≅ base X (happly (Tℤ-action-lemma X x))
   II = to-Tℤ-≡-comp base base X loop-≅ (Tℤ-action-≅ X x)

\end{code}

\begin{code}

module _
        {A : 𝓤 ̇ }
        (r : Tℤ → A)
       where

 BBG-map : (X : Tℤ) → ⟨ X ⟩ → r base ≡ r X
 BBG-map X x = ap r (Tℤ-action-≡ X x)

 BBG-map-lemma : (X : Tℤ) (x : ⟨ X ⟩)
               → BBG-map X (⟨ X ⟩₂ x) ≡ ap r loop ∙ BBG-map X x
 BBG-map-lemma X x = BBG-map X (⟨ X ⟩₂ x)                      ≡⟨ refl ⟩
                     ap r (Tℤ-action-≡ X (⟨ X ⟩₂ x))           ≡⟨ I    ⟩
                     ap r (loop ∙ Tℤ-action-≡ X x)             ≡⟨ II   ⟩
                     ap r loop ∙ ap r (Tℤ-action-≡ X x)        ≡⟨ refl ⟩
                     ap r loop ∙ BBG-map X x                   ∎
  where
   I  = ap (ap r) (Tℤ-action-≡-lemma X x)
   II = ap-∙ r loop (Tℤ-action-≡ X x)

 module _
         (fe : funext 𝓤 𝓤)
        where

  open Tℤ-rec {𝓤} {A} fe

  ∼-to-Tℤ-rec : r ∼ Tℤ-rec (r base , ap r loop)
  ∼-to-Tℤ-rec X = ap pr₁ e
   where
    b₁ : BBG (r base , ap r loop) (X ⁻)
    b₁ = (r X , BBG-map X , BBG-map-lemma X)
    b₂ : BBG (r base , ap r loop) (X ⁻)
    b₂ = center (BBG-is-singleton (r base , ap r loop) X)
    e : b₁ ≡ b₂
    e = singletons-are-props (BBG-is-singleton (r base , ap r loop) X) b₁ b₂

\end{code}

\begin{code}

Tℤ-universal-property : funext 𝓤 𝓤 → funext 𝓤₁ 𝓤
                      → (A : 𝓤 ̇ )
                      → (Tℤ → A) ≃ (Σ a ꞉ A , a ≡ a)
Tℤ-universal-property {𝓤} fe fe₁ A = qinveq ϕ (ψ , η , ε)
 where
  open Tℤ-rec {𝓤} {A} fe
  ϕ : (Tℤ → A) → (Σ a ꞉ A , a ≡ a)
  ϕ f = (f base , ap f loop)
  ψ : (Σ a ꞉ A , a ≡ a) → (Tℤ → A)
  ψ (a , p) = Tℤ-rec (a , p)
  η : ψ ∘ ϕ ∼ id
  η f = dfunext fe₁ (λ X → ∼-to-Tℤ-rec f fe X ⁻¹)
  ε : ϕ ∘ ψ ∼ id
  ε = Tℤ-rec-comp

\end{code}

TO DO: Prove this from Tℤ-uniqueness-principle directly?

\begin{code}

module _
        (A : 𝓤 ̇ )
        (fe : funext 𝓤 𝓤)
       where

 open Tℤ-rec {𝓤} {A} fe

 Tℤ-uniqueness-principle-∼ : (f g : Tℤ → A)
                           → (f base , ap f loop) ≡ (g base , ap g loop)
                           → f ∼ g
 Tℤ-uniqueness-principle-∼ f g p X =
  f X                           ≡⟨ ∼-to-Tℤ-rec f fe X      ⟩
  Tℤ-rec (f base , ap f loop) X ≡⟨ ap (λ - → Tℤ-rec - X) p ⟩
  Tℤ-rec (g base , ap g loop) X ≡⟨ (∼-to-Tℤ-rec g fe X) ⁻¹ ⟩
  g X                           ∎

 Tℤ-uniqueness-principle-≡ : funext 𝓤₁ 𝓤
                           → (f g : Tℤ → A)
                           → (f base , ap f loop) ≡ (g base , ap g loop)
                           → f ≡ g
 Tℤ-uniqueness-principle-≡ fe' f g p = dfunext fe' (Tℤ-uniqueness-principle-∼ f g p)

 Tℤ-uniquess-principle : funext 𝓤₁ 𝓤
                       → (a : A) (p : a ≡ a)
                       → ∃! r ꞉ (Tℤ → A) , (r base , ap r loop) ≡ (a , p)
 Tℤ-uniquess-principle fe' a p =
  equivs-are-vv-equivs ⌜ e ⌝ (⌜⌝-is-equiv e) (a , p)
   where
    e : (Tℤ → A) ≃ (Σ a ꞉ A , a ≡ a)
    e = Tℤ-universal-property fe fe' A

\end{code}
