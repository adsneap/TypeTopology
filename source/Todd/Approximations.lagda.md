
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
                                    
open import Naturals.Order renaming (max to ℕmax) hiding (≤-refl ; ≤-trans)

𝔻 = ℤ[1/2]

-- SEQUENCES

-- Def 1.5
is-odcs : (ℤ → ℤ[1/2] × ℤ[1/2]) → 𝓤₀  ̇  
is-odcs ζ = ((n : ℤ) → pr₁ (ζ n) ≤ℤ[1/2] pr₂ (ζ n))
          × ((ϵ : 𝔻) → Σ n ꞉ ℤ , ((pr₂ (ζ n) - pr₁ (ζ n)) ≤ℤ[1/2] ϵ))
          × ((n : ℤ) → (pr₁ (ζ n) ≤ℤ[1/2] pr₁ (ζ (succℤ n)))
                     × (pr₂ (ζ (succℤ n)) ≤ℤ[1/2] pr₂ (ζ n)))

is-odcs-c₃-lemma-ns : (ζ : (ℤ → ℤ[1/2] × ℤ[1/2])) → ((c₁ , c₂ , c₃) : is-odcs ζ)
                    → (n₁ n₂ : ℤ) → (k : ℕ) → n₁ ℤ+ pos k ＝ n₂ → (pr₁ (ζ n₁) ≤ℤ[1/2] pr₁ (ζ n₂)) × (pr₂ (ζ n₂) ≤ℤ[1/2] pr₂ (ζ n₁))
is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ n₂ 0        e = transport (λ - → pr₁ (ζ n₁) ≤ pr₁ (ζ -)) e (≤-refl (pr₁ (ζ n₁)))
                                                      , transport (λ - → pr₂ (ζ -) ≤ pr₂ (ζ n₁)) e (≤-refl (pr₂ (ζ n₁)))
is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ n₂ 1 e = transport (λ - → pr₁ (ζ n₁) ≤ pr₁ (ζ -)) e (pr₁ (c₃ n₁))
                                               , transport (λ - → pr₂ (ζ -) ≤ pr₂ (ζ n₁)) e (pr₂ (c₃ n₁)) 
is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ n₂ (succ (succ k)) e with (is-odcs-c₃-lemma-ns ζ (c₁ , c₂ , c₃) n₁ (predℤ n₂) (succ k) (predsuccℤ (succℤ (n₁ +pos k)) ⁻¹ ∙ ap predℤ e))
... | (l₁ , l₂) = trans' (pr₁ (ζ n₁)) (pr₁ (ζ (predℤ n₂))) (pr₁ (ζ n₂)) l₁ (transport (λ - → pr₁ (ζ (predℤ n₂)) ≤ℤ[1/2] pr₁ (ζ -)) (succpredℤ n₂) (pr₁ (c₃ (predℤ n₂))))
                , trans' (pr₂ (ζ n₂)) (pr₂ (ζ (predℤ n₂))) (pr₂ (ζ n₁)) (transport (λ - → pr₂ (ζ -) ≤ℤ[1/2] pr₂ (ζ (predℤ n₂))) (succpredℤ n₂) (pr₂ (c₃ (predℤ n₂)))) l₂

is-odcs-c₃-lemma : (ζ : (ℤ → ℤ[1/2] × ℤ[1/2])) → ((c₁ , c₂ , c₃) : is-odcs ζ)
                 → (n₁ n₂ : ℤ) → n₁ ≤ n₂ → (pr₁ (ζ n₁) ≤ℤ[1/2] pr₁ (ζ n₂)) × (pr₂ (ζ n₂) ≤ℤ[1/2] pr₂ (ζ n₁))
is-odcs-c₃-lemma ζ c n₁ n₂ (k , e) = is-odcs-c₃-lemma-ns ζ c n₁ n₂ k e

postulate
 ℤ[1/2]-ordering-property : (a b c d : ℤ[1/2]) → (a - b) < (c - d) → (a < c) ∔ (d < b)

-- Lem 1.6
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
  inhabited-l = ∣ (pr₁ (ζ (pos 0)) - 1ℤ[1/2])
              , ∣ pos 0 , ℤ[1/2]<-neg (pr₁ (ζ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  inhabited-r : inhabited-right R
  inhabited-r = ∣ (pr₂ (ζ (pos 0)) + 1ℤ[1/2])
             , ∣ pos 0  , ℤ[1/2]<-+ (pr₂ (ζ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  rounded-l : rounded-left L
  rounded-l p = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n)) → ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n')))
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n)) → Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n')))
      I (n , p<ζn) = let (p' , p<p' , p'<ζn) = dense p (pr₁ (ζ n)) p<ζn
                     in p' , (p<p' , ∣ n , p'<ζn ∣)
    rtl : ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n)))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n))
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n)))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n))
      I (p' , p<p' , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (p' <ℤ[1/2] pr₁ (ζ n)) → Σ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n))
        II (n  , p'<ζn) = n , (trans p p' (pr₁ (ζ n)) p<p' p'<ζn)
      
  rounded-r : rounded-right R
  rounded-r q = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , pr₂ (ζ n) < q → ∃ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , pr₂ (ζ n) < q → Σ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
      I (n , ζn<q) = let (q' , ζn<q' , q'<q) = dense (pr₂ (ζ n)) q ζn<q
                     in q' , (q'<q , ∣ n , ζn<q' ∣)
    rtl : ∃ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
      I (q' , q'<q , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (pr₂ (ζ n) < q') → Σ n ꞉ ℤ , (pr₂ (ζ n) <ℤ[1/2] q)
        II (n , ζ<q') = n , (trans (pr₂ (ζ n)) q' q ζ<q' q'<q)
  
  is-disjoint : disjoint L R
  is-disjoint p q (tp<x , tx<q) = ∥∥-rec (<ℤ[1/2]-is-prop p q) I (binary-choice tp<x tx<q)
   where
    I : (Σ n ꞉ ℤ , (p <ℤ[1/2] pr₁ (ζ n))) × (Σ n' ꞉ ℤ , (pr₂ (ζ n') <ℤ[1/2] q))
      → p <ℤ[1/2] q
    I ((n , p<l) , (n' , r<q)) with ℤ-dichotomous n n'
    ... | inl n≤n' = let p<l' = ℤ[1/2]<-≤ p (pr₁ (ζ n)) (pr₁ (ζ n')) p<l (pr₁ (is-odcs-c₃-lemma ζ (c₁ , c₂ , c₃) n n' n≤n'))
                         l<q' = ℤ[1/2]≤-< (pr₁ (ζ n')) (pr₂ (ζ n')) q (c₁ n') r<q
                     in trans p (pr₁ (ζ n')) q p<l' l<q'
    ... | inr n'≤n = let p<r' = ℤ[1/2]<-≤ p (pr₁ (ζ n)) (pr₂ (ζ n)) p<l (c₁ n)
                         r<q' = ℤ[1/2]≤-< (pr₂ (ζ n)) (pr₂ (ζ n')) q (pr₂ (is-odcs-c₃-lemma ζ (c₁ , c₂ , c₃) n' n n'≤n)) r<q
                     in trans p (pr₂ (ζ n)) q p<r' r<q'
 
  is-located : located L R
  is-located p q p<q = I (c₂ (1/2 * (q - p)))
   where
    0<ε : 0ℤ[1/2] < (1/2 * (q - p))
    0<ε = <-pos-mult' 1/2 (q - p) 0<1/2ℤ[1/2] (diff-positive p q p<q)
    I : (Σ n ꞉ ℤ , ((pr₂ (ζ n) - pr₁ (ζ n)) ≤ℤ[1/2] (1/2 * (q - p)))) → (L p holds) ∨ (R q holds)
    I (n , l₁) = II (ℤ[1/2]-ordering-property (pr₂ (ζ n)) (pr₁ (ζ n)) q p l₂)
     where
      l₂ :(pr₂ (ζ n) - pr₁ (ζ n)) < (q - p)
      l₂ = ℤ[1/2]≤-< (pr₂ (ζ n) - pr₁ (ζ n)) (1/2 * (q - p)) (q - p) l₁ (ℤ[1/2]-1/2-< (q - p) (diff-positive p q p<q))
      II : pr₂ (ζ n) < q ∔ p < pr₁ (ζ n) → (L p holds) ∨ (R q holds)
      II (inl ζ<q) = ∣ inr ∣ n , ζ<q ∣ ∣
      II (inr p<ζ) = ∣ inl ∣ n , p<ζ ∣ ∣

-- Def 1.7
η η⁺² : ℤ × ℤ → ℤ[1/2]
η   = normalise
η⁺² (k , p) = normalise (k +pos 2 , p)

-- Def 1.8
η[_] : ℤ × ℤ → ℤ[1/2] × ℤ[1/2]
η[ (k , p) ] = η (k , p) , η⁺² (k , p)

-- Lem 1.9
||_|| : (ℤ → ℤ × ℤ) → (ℤ → 𝔻 × 𝔻)
|| ξ || = η[_] ∘ ξ

is-gbr : (ℤ → ℤ × ℤ) → 𝓤₀  ̇
is-gbr ξ = ((ϵ : 𝔻) → Σ n ꞉ ℤ , (normalise ((pos 1) , (predℤ (pr₂ (ξ n)))) ≤ ϵ))
         × ((n : ℤ) → (η (ξ n) ≤ η (ξ (succℤ n))) × (η⁺² (ξ (succℤ n)) ≤ η⁺² (ξ n)))

𝔾-gives-odcs : (ξ : ℤ → ℤ × ℤ) → is-gbr ξ → is-odcs || ξ ||
𝔾-gives-odcs ξ (ξc₁ , ξc₂) = c₁ , c₂ , ξc₂
 where
  c₁ : (n : ℤ) → pr₁ (|| ξ || n) ≤ℤ[1/2] pr₂ (|| ξ || n)
  c₁ n = <-is-≤ℤ[1/2] (pr₁ (|| ξ || n)) (pr₂ (|| ξ || n)) (normalise-< (ξ n))
  c₂ : (ϵ : 𝔻) → Σ n ꞉ ℤ , (pr₂ (|| ξ || n) - pr₁ (|| ξ || n)) ≤ℤ[1/2] ϵ
  c₂ ε with ξc₁ ε 
  ... | (n , l) = n , (transport (_≤ ε) (normalise-equality (ξ n)) l)

-- Lem 1.10
<_> : 𝕋 → (ℤ → ℤ × ℤ)
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

open import Todd.BelowAndAbove fe hiding (downLeft ; downMid ; downRight ; upLeft ; upRight ; _below_ ; _above_ ; Vec)

postulate
 normalise-succ : (z n : ℤ) → normalise (z , n) ≤ normalise (z ℤ+ z , succℤ n)

<>-is-odcs : (χ : 𝕋) → is-odcs || < χ > ||
<>-is-odcs (χ , b) = <>-gives-odcs (χ , b)

-- Def 1.11
⟦_⟧' : 𝕋 → ℝ-d
⟦ χ ⟧' = ⦅ _ , <>-gives-odcs χ ⦆

-- FUNCTIONS


-- JOINING

-- Def 1.14

J' : 𝔻 × 𝔻 → ℤ × ℤ × ℤ
J' (((a , p₁) , _) , ((b , p₂) , _)) = rec a downLeft  (abs (maxℤ (pos p₁) (pos p₂) ℤ- pos p₁))
                                     , rec b downRight (abs (maxℤ (pos p₁) (pos p₂) ℤ- pos p₂))
                                     , maxℤ (pos p₁) (pos p₂)

-- Def 1.15

_/2 : ℕ → ℕ
zero /2 = 0
succ zero /2 = 0
succ (succ x) /2 = succ (x /2)

{-# TERMINATING #-}
upValue : ℕ → ℕ -- roughly clog2(x+1) (0 1 2 4 8 16)
upValue 0 = 0
upValue (succ n) = succ (upValue (succ n /2))

-- need proofs that upValue provides correct covering

join : (ℤ → 𝔻 × 𝔻) → (ℤ → ℤ × ℤ)
join ζ n = rec a upRight m , p ℤ- pos m
 where
   abp = J' (ζ n)
   a =  pr₁        abp
   b = (pr₁ ∘ pr₂) abp
   p = (pr₂ ∘ pr₂) abp
   m = upValue (abs (b ℤ- a))

-- Lem 1.16

join-is-gbr : (ζ : ℤ → 𝔻 × 𝔻) → is-gbr (join ζ)
join-is-gbr ζ = {!!}

join-is-odcs : (ζ : ℤ → 𝔻 × 𝔻) → is-odcs || join ζ ||
join-is-odcs ζ = 𝔾-gives-odcs (join ζ) (join-is-gbr ζ)

-- Lem 1.17

_≡_ = _＝_

join-same-real : ((ζ , i) : Σ is-odcs) → (io : is-odcs || join ζ ||) → ⦅ ζ , i ⦆ ≡ ⦅ || join ζ || , io ⦆
join-same-real = {!!}

-- PRE-NORMALISING

-- Def 1.18

κ-prenorm : (κ : ℤ → ℤ) → 𝓤₀ ̇
κ-prenorm κ = ((n : ℤ) → κ n ≤ κ (succℤ n))
            × ((n : ℤ) → n ≤ κ n)

is-prenormalised : (ℤ → ℤ × ℤ) → 𝓤₀ ̇
is-prenormalised ζ = (n : ℤ) → pr₂ (ζ n) ≥ n

-- Def 1.19

prenorm-for_ : (ℤ → ℤ × ℤ) → 𝓤₀ ̇
prenorm-for χ = Σ κ ꞉ (ℤ → ℤ) , (is-prenormalised (χ ∘ κ))
                              × ((n : ℤ) → κ n ≤ κ (succℤ n))
                              × ((n : ℤ) → n ≤ κ n)

-- Lem 1.20

prenorm : (χ : ℤ → ℤ × ℤ) → prenorm-for χ → (ℤ → ℤ × ℤ)
prenorm χ (κ , i) = χ ∘ κ

prenorm-is-prenormalised : (χ : ℤ → ℤ × ℤ) → (κ : prenorm-for χ)
                         → is-prenormalised (prenorm χ κ)
prenorm-is-prenormalised χ (κ , κf , κs) = κf

normalise-≤-lemma : ((x , a) (y , b) : ℤ × ℤ)
                  → x ℤ* b ≤ y ℤ* a
                  → normalise (x , a) ≤ normalise (y , b)
normalise-≤-lemma = {!easy (but long proof)!}

prenorm-is-gbr-lemma : (a b : ℤ) → a ≤ b → normalise (pos 1 , b) ≤ normalise (pos 1 , a)
prenorm-is-gbr-lemma a b l =
 normalise-≤-lemma (pos 1 , b) (pos 1 , a)
  (transport₂ _≤_ (ℤ-mult-left-id a ⁻¹) (ℤ-mult-left-id b ⁻¹) l)

prenorm-is-gbr : (χ : ℤ → ℤ × ℤ)
               → (κ : prenorm-for χ)
               → is-gbr χ
               → is-gbr (prenorm χ κ)
prenorm-is-gbr χ (κ , κf , κs , κ≤) (c₁ , c₂) = c₁' , c₂'
 where
  c₁' : (ε : ℤ[1/2]) → Σ n ꞉ ℤ , normalise (pos 1 , predℤ (pr₂ (χ (κ n)))) ≤ ε
  c₁' ε = I (c₁ ε)
   where
    I : (Σ n  ꞉ ℤ , normalise (pos 1 , predℤ (pr₂ (χ n)))      ≤ ε)
       → Σ n' ꞉ ℤ , normalise (pos 1 , predℤ (pr₂ (χ (κ n')))) ≤ ε
    I (n , l') = n , trans' (normalise (pos 1 , predℤ (pr₂ (χ (κ n))))) (normalise (pos 1 , predℤ (pr₂ (χ n)))) ε l₂ l'
     where
      i : n ≤ κ n
      i = κ≤ n
      ii : (n₁ n₂ : ℤ) → n₁ ≤ n₂ → normalise (χ n₁) ≤ normalise (χ n₂) 
      ii n₁ n₂ l = {!induction using c₂!}
      iii : normalise (χ n) ≤ normalise (χ (κ n))
      iii = ii n (κ n) i
      iv : {!!}
      iv = {!!}

      
      {-
      i : (n₁ n₂ : ℤ) → n₁ ≤ n₂ → pr₂ (χ n₁) ≤ pr₂ (χ n₂) 
      i n₁ n₂ n₁≤n₂ = {!!}
      
      χn≤χκn : pr₂ (χ n) ≤ pr₂ (χ (κ n))
      χn≤χκn = i n (κ n) (κ≤ n)
      -}
      l₂ : normalise (pos 1 , predℤ (pr₂ (χ (κ n)))) ≤ℤ[1/2] normalise (pos 1 , predℤ (pr₂ (χ n)))
      l₂ = {!!} -- prenorm-is-gbr-lemma (predℤ (pr₂ (χ n))) (predℤ (pr₂ (χ (κ n))))
                -- (≤-predℤ' (pr₂ (χ n)) (pr₂ (χ (κ n))) χn≤χκn)

  c₂' : (n : ℤ)
      → (normalise (prenorm χ (κ , κf , κs , κ≤) n) ≤ normalise (prenorm χ (κ , κf , κs , κ≤) (succℤ n)))
      × (η⁺² (prenorm χ (κ , κf , κs , κ≤) (succℤ n))) ≤ (η⁺² (prenorm χ (κ , κf , κs , κ≤) n))
  c₂' n = I , II
   where
    induct₁ : (n₁ n₂ : ℤ) → n₁ ≤ n₂ → normalise (χ n₁) ≤ normalise (χ n₂)
    induct₁ n₁ n₂ n₁≤n₂ = {!--easy induction!}

    induct₂ : (n₁ n₂ : ℤ) → n₁ ≤ n₂ → η⁺² (χ n₂) ≤ η⁺² (χ n₁)
    induct₂ n₁ n₂ n₁≤n₂ = {!easy induction!}
    
    I : normalise (χ (κ n)) ≤ normalise (χ (κ (succℤ n)))
    I = induct₁ (κ n) (κ (succℤ n)) (κs n)

    II : η⁺² (χ (κ (succℤ n))) ≤ η⁺² (χ (κ n))
    II = induct₂ (κ n) (κ (succℤ n)) (κs n)
  
prenorm-is-odcs : (χ : ℤ → ℤ × ℤ)
                → (κ : prenorm-for χ)
                → is-gbr χ
                → is-odcs || prenorm χ κ ||
prenorm-is-odcs χ κ igbr = 𝔾-gives-odcs (prenorm χ κ) (prenorm-is-gbr χ κ igbr)

prenorm-same-real : (χ : ℤ → ℤ × ℤ)
                  → (i : is-odcs || χ ||)
                  → (κ : prenorm-for χ)
                  → (io : is-odcs || prenorm χ κ ||)
                  → ⦅ || χ || , i ⦆ ≡ ⦅ || prenorm χ κ || , io ⦆
prenorm-same-real χ i (κ , κps) io = ℝ-d-equality-from-left-cut ltr rtl
 where
  ltr : lower-cut-of ⦅ || χ || , i ⦆ ⊆ lower-cut-of ⦅ || prenorm χ (κ , κps) || , io ⦆
  ltr p = ∥∥-functor I
   where
    I : Σ n ꞉ ℤ , (p <ℤ[1/2] η (χ n))
      → Σ n ꞉ ℤ , (p <ℤ[1/2] η (χ (κ n)))
    I (n , p<ξn) = n , {!!}
  rtl : lower-cut-of ⦅ || prenorm χ (κ , κps) || , io ⦆ ⊆ lower-cut-of ⦅ || χ || , i ⦆
  rtl p = ∥∥-functor I
   where
    I : Σ n ꞉ ℤ , (p <ℤ[1/2] η (χ (κ n)))
      → Σ n ꞉ ℤ , (p <ℤ[1/2] η (χ n))
    I (n , p<χκn) = {!!}

-- Lem 1.21

is-normalised : (ℤ → ℤ × ℤ) → 𝓤₀ ̇
is-normalised ζ = (n : ℤ) → pr₂ (ζ n) ≡ n

-- Lem 1.23

norm : (χ : ℤ → ℤ × ℤ) → is-prenormalised χ → (ℤ → ℤ × ℤ)
norm χ ipχ n = rec (pr₁ (χ n)) upRight (abs (n ℤ- pr₂ (χ n))) , n

norm-is-normalised : (χ : ℤ → ℤ × ℤ) → (ipχ : is-prenormalised χ) → is-normalised (norm χ ipχ)
norm-is-normalised χ ipχ n = refl

normalised-are-prenormalised : (χ : ℤ → ℤ × ℤ) → is-normalised χ → is-prenormalised χ
normalised-are-prenormalised χ i n = 0 , (i n ⁻¹)

norm-is-prenormalised : (χ : ℤ → ℤ × ℤ)
                      → (ip : is-prenormalised χ)
                      → is-prenormalised (norm χ ip) 
norm-is-prenormalised χ ip = normalised-are-prenormalised (norm χ ip) (norm-is-normalised χ ip)

-- (χ : Z → Z x Z) → (ipx : is-prenormalised χ) → ((κ , _) : prenorm-for χ) → κ ∼ id
-- (χ : Z → Z x Z) → (ipx : is-prenormalised χ) → prenorm-for χ (i.e. id)
-- (χ : Z → Z x Z) → (ipx : is-prenormalised χ) → (κ : prenorm-for χ) → prenorm χ κ ∼ χ

norm-is-gbr : (χ : ℤ → ℤ × ℤ)
            → is-gbr χ
            → (ipχ : is-prenormalised χ)
            → is-gbr (norm χ ipχ)
norm-is-gbr χ igbrχ ipχ = {!!}

norm-is-odcs : (χ : ℤ → ℤ × ℤ)
             → is-gbr χ 
             → (ipχ : is-prenormalised χ)
             → is-odcs || norm χ ipχ ||
norm-is-odcs χ gbrχ ip = prenorm-is-odcs (norm χ ip) κ' (prenorm-is-gbr (norm χ ip) κ' (norm-is-gbr χ gbrχ ip))
 where
  κ' : prenorm-for norm χ ip
  κ' = id , (norm-is-prenormalised χ ip) , (λ n → 1 , refl) , (λ n → 0 , refl)
                   

norm-same-real : (χ : ℤ → ℤ × ℤ)
               → (i : is-odcs || χ ||)
               → (ip : is-prenormalised χ)
               → (io : is-odcs || norm χ ip ||)
               → ⦅ || χ || , i ⦆ ≡ ⦅ || norm χ ip || , io ⦆
norm-same-real χ i ip io = {!!}

-- Def 1.24

toTB : Σ is-normalised → 𝕋
toTB (χ , χin) = (λ n → pr₁ (χ n)) , {!!}

toTB-same-real : ((χ , χin) : Σ is-normalised)
               → (i : is-odcs || χ ||)
               → ⟦ toTB (χ , χin) ⟧' ≡ ⦅ || χ || , i ⦆
toTB-same-real = {!!}

```

To be re-organised and commented.

```agda

open import Todd.BuildingBlocks pt fe pe sq

record Approximations : 𝓤 ̇ where
 field
  n : ℕ
  C : Collection n
 open Collection C

-- Lem 1.12

 F' : Vec (Σ is-odcs) n → ℤ → ℤ[1/2] × ℤ[1/2]
 F' ζs n = (L (vec-map (λ (ζ , odcs) → ζ n) ζs))
         , (R (vec-map (λ (ζ , odcs) → ζ n) ζs))

 F'-is-odcs : (ζs : Vec (Σ is-odcs) n) → is-odcs (F' ζs)
 F'-is-odcs ζs = I , {!!} , {!!}
  where
   I : (n : ℤ) → pr₁ (F' ζs n) ≤ℤ[1/2] pr₂ (F' ζs n)
   I n = Condition-4 (vec-map (λ (ζ , odcs) → ζ n) ζs)
                     (vec-map (λ (ζ , odcs) → ζ n) ζs)
 
-- Thm 1.13

 F'-same-real : (ζs : Vec (Σ is-odcs) n)
              → (i : is-odcs (F' ζs))
              → F (vec-map ⦅_⦆ ζs) ≡ ⦅ F' ζs , i ⦆
 F'-same-real ζs i = {!!}

-- Def 1.25

 vζs : (xs : Vec 𝕋 n) → Vec (Σ is-odcs) n
 vζs xs = vec-map (λ t → || < t > || , (<>-is-odcs t)) xs

 vF' : (xs : Vec 𝕋 n) → ℤ → ℤ[1/2] × ℤ[1/2]
 vF' = F' ∘ vζs

 vJF' : (xs : Vec 𝕋 n) → ℤ → ℤ × ℤ
 vJF' = join ∘ vF'

 vPJF' : (xs : Vec 𝕋 n)
       → prenorm-for vJF' xs
       → ℤ → ℤ × ℤ
 vPJF' xs p = prenorm (vJF' xs) p

 vNPJF' : (xs : Vec 𝕋 n)
        → (p : prenorm-for vJF' xs)
        → is-prenormalised (vPJF' xs p)
        → ℤ → ℤ × ℤ
 vNPJF' xs p ip = norm (vPJF' xs p) ip

 F* : (xs : Vec 𝕋 n)
    → (pf : prenorm-for vJF' xs)
    → (ip : is-prenormalised (vPJF' xs pf))
    → (isn : is-normalised (vNPJF' xs pf ip))
    → 𝕋
 F* xs xsp ip isn = toTB (vNPJF' xs xsp ip , isn)

 F-same-real : (χs : Vec 𝕋 n)
             → (pf : prenorm-for vJF' χs)
             → (ip : is-prenormalised (vPJF' χs pf))
             → (isn : is-normalised (vNPJF' χs pf ip))
             → ⟦ F* χs pf ip isn ⟧' ≡ F (vec-map ⦅_⦆ (vζs χs))
 F-same-real χs pf ip isn = ⟦ F* χs pf ip isn ⟧'                   ＝⟨ toTB-same-real (vNPJF' χs pf ip , isn) jNPF'odcs      ⟩
                            ⦅ || vNPJF' χs pf ip || , jNPF'odcs ⦆  ＝⟨ norm-same-real (vPJF' χs pf) jPF'odcs ip jNPF'odcs ⁻¹ ⟩
                            ⦅ || vPJF' χs pf ||     , jPF'odcs  ⦆  ＝⟨ prenorm-same-real (vJF' χs) jF'odcs pf jPF'odcs ⁻¹    ⟩
                            ⦅ || vJF' χs ||         , jF'odcs   ⦆  ＝⟨ join-same-real (vF' χs , F'odcs) jF'odcs ⁻¹           ⟩                            
                            ⦅ vF' χs                , F'odcs    ⦆  ＝⟨ F'-same-real (vζs χs) F'odcs ⁻¹                       ⟩
                            F (vec-map ⦅_⦆ (vζs χs))               ∎
  where
   jNPF'odcs : is-odcs || norm (vPJF' χs pf) ip ||
   jNPF'odcs = norm-is-odcs (vPJF' χs pf) (prenorm-is-gbr (vJF' χs) pf (join-is-gbr (vF' χs))) ip
   jPF'odcs : is-odcs || prenorm (vJF' χs) pf ||
   jPF'odcs = prenorm-is-odcs (vJF' χs) pf (join-is-gbr (vF' χs))
   jF'odcs : is-odcs || join (F' (vζs χs)) ||
   jF'odcs = join-is-odcs (vF' χs)
   F'odcs : is-odcs (F' (vζs χs))
   F'odcs = F'-is-odcs (vζs χs)
   
```

