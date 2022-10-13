
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

module Todd.BuildingBlocks
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

ℕmin : ℕ → ℕ → ℕ
ℕmin 0 n               = 0
ℕmin (succ m) 0        = 0
ℕmin (succ m) (succ n) = succ (ℕmin m n)

ℤmax : ℤ → ℤ → ℤ
ℤmax (pos x) (pos y)         = pos (ℕmax x y)
ℤmax (pos x) (negsucc y)     = pos x
ℤmax (negsucc x) (pos y)     = pos y
ℤmax (negsucc x) (negsucc y) = negsucc (ℕmin x y)

record Collection (n : ℕ) : {!!} ̇ where
 field
  D : Vec ℤ[1/2] (succ n) → ℤ[1/2]
  L R : Vec (ℤ[1/2] × ℤ[1/2]) (succ n) → ℤ[1/2]
  Condition-1a : (a c x d b : Vec ℤ[1/2] (succ n))
               → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)
               → (L (zip (a , b)) ≤ℤ[1/2] L (zip (c , d)))
  Condition-1b : (c x d : Vec ℤ[1/2] (succ n))
               → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)             
               → (L (zip (c , d)) ≤ℤ[1/2] D x)
  Condition-1c : (c x d : Vec ℤ[1/2] (succ n))
               → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)              
               → (D x ≤ℤ[1/2] R (zip (c , d)))
  Condition-1d : (a c x d b : Vec ℤ[1/2] (succ n))
               → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)
               → (R (zip (c , d)) ≤ℤ[1/2] R (zip (a , b)))
               
  Condition-2 : (x : Vec ℤ[1/2] (succ n)) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε) → Σ (a , b) ꞉ Vec ℤ[1/2] (succ n) × Vec ℤ[1/2] (succ n) , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (L (zip (a , b))) (D x) ε 0<ε
  Condition-3 : (x : Vec ℤ[1/2] (succ n)) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε) → Σ (a , b) ꞉ Vec ℤ[1/2] (succ n) × Vec ℤ[1/2] (succ n) , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (R (zip (a , b))) (D x) ε 0<ε
  
 F : Vec ℝ-d (succ n) → ℝ-d
 F v = (Lc , Rc) , inhabited-l , inhabited-r , rounded-l , {!!} , is-disjoint , is-located
  where
   Lc Rc : 𝓟 ℤ[1/2] 
   Lc p = (∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , (pairwise-P' (λ (a , b) x → a < x × x < b) asbs v) × p < L asbs) , ∃-is-prop
   Rc q = (∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , (pairwise-P' (λ (a , b) x → a < x × x < b) asbs v) × R asbs < q) , ∃-is-prop
   
   inhabited-l : inhabited-left Lc
   inhabited-l = ∥∥-functor I (generate-asbs v) 
    where
     I : Σ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v
       → Σ p ꞉ ℤ[1/2] , ∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v × p < L asbs
     I (asbs , a<x<b) = ((L asbs) - 1ℤ[1/2]) , ∣ asbs , a<x<b , {!L asbs - 1 < L asbs!} ∣

   inhabited-r : inhabited-right Rc
   inhabited-r = ∥∥-functor I (generate-asbs v)
    where
     I : Σ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v
       → Σ q ꞉ ℤ[1/2] , ∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v × R asbs < q
     I (asbs , a<x<b) = (R asbs + 1ℤ[1/2]) , ∣ asbs , a<x<b , {!R < R + 1!} ∣

   rounded-l : rounded-left Lc
   rounded-l p = ltr , rtl
    where
     ltr : ∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v × p < L asbs
         → ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v × p' < L asbs)
     ltr tasbs = do
                (asbs , as<xs<bs) ← tasbs
                {!!}
     rtl : {!!}
     rtl = {!!} --just density/minus1

   is-disjoint : disjoint Lc Rc
   is-disjoint p q (p<x , x<q) = {!!}
   -- p < Lab
   --       Rab' < q

   -- Lab ≤ Dx ≤ Rab
   is-located : located Lc Rc
   is-located p q p<q = {!!}
   -- 0<q-p → 

 L' R' : Vec (ℤ × ℤ) (succ n) → ℤ × ℤ
 L' = {!!}
 R' = {!!}

 F* : Vec 𝕋 (succ n) → 𝕋
 F* x = {!!} 

 dyadic-function-equiv-to-real : (x : Vec ℤ[1/2] (succ n)) → ι (D x) ＝ F (vec-map ι x)
 dyadic-function-equiv-to-real x = ℝ-d-equality-from-left-cut ltr rtl
  where
   ltr : (p : ℤ[1/2]) → p ∈ lower-cut-of (ι (D x)) → p ∈ lower-cut-of (F (vec-map ι x))
   ltr p p<Dx = by-condition-3 (Condition-2 x ε 0<ε)
    where
     ε : ℤ[1/2] 
     ε = ℤ[1/2]-abs (p - D x)
     0<ε : 0ℤ[1/2] <ℤ[1/2] ε
     0<ε = {!!} -- positive since p<Dx
     by-condition-3 : Σ (a , b) ꞉ Vec ℤ[1/2] (succ n) × Vec ℤ[1/2] (succ n) , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (L (zip (a , b))) (D x) ε 0<ε
                    → p ∈ lower-cut-of (F (vec-map ι x))
     by-condition-3 ((a , b) , a<x , x<b , distance-proof) = ∣ (zip (a , b)) , V , p<Lab ∣
      where
       I : 0ℤ[1/2] ≤ (D x - L (zip (a , b)))
       I = {!since L ≤ D!}
       II : 0ℤ[1/2] ≤ (D x - p)
       II = {!Since p ≤ D!}
       III : (D x - L (zip (a , b))) < (D x - p)
       III = {!using I, II, and distance-proof!}
       IV : (- (L (zip (a , b)))) < (- p)
       IV = {!from III!}
       p<Lab : p < L (zip (a , b))
       p<Lab = <-swap' (L (zip (a , b))) p IV
       V : pairwise-P' (λ (a , b) x → a < x × x < b) (zip (a , b)) (vec-map ι x)
       V = dyadic-real-lemma a b (vec-map ι x) (vec-∈L-< a x a<x) (vec-∈R-< b x (vec-∈R-<-reorder b x x<b))
        
   rtl : (p : ℤ[1/2]) → p ∈ lower-cut-of (F (vec-map ι x)) → p ∈ lower-cut-of (ι (D x))
   rtl p p<Fx = ∥∥-rec (∈-is-prop (lower-cut-of (ι (D x))) p) I p<Fx
    where
     I : Σ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs (vec-map ι x) × p < L asbs → p < D x
     I (asbs , a<x<b , p<Lab) = ℤ[1/2]<-≤ p (L asbs) (D x) p<Lab (transport (λ - → (L -) ≤ℤ[1/2] D x) (zip-unzip asbs) II)
      where
       II : L (zip (unzip asbs)) ≤ℤ[1/2] D x
       II = Condition-1b (get-left asbs) x (get-right asbs) (dyadic-real-lemma' asbs x a<x<b)

 ternary-boehm-function-equiv-to-real : (α : Vec 𝕋 (succ n)) → ⟦ F* α ⟧ ＝ F (vec-map ⟦_⟧ α)
 ternary-boehm-function-equiv-to-real = {!!}

neg-D : Vec ℤ[1/2] 1 → ℤ[1/2]
neg-D (x ∷ []) = - x

neg-L : Vec (ℤ[1/2] × ℤ[1/2]) 1 → ℤ[1/2]
neg-L ((a , b) ∷ []) = - b

neg-R : Vec (ℤ[1/2] × ℤ[1/2]) 1 → ℤ[1/2]
neg-R ((a , b) ∷ []) = - a

neg-Condition-1a : (a c x d b : Vec ℤ[1/2] 1)
                 → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)
                 → (neg-L (zip (a , b)) ≤ℤ[1/2] neg-L (zip (c , d)))
neg-Condition-1a (a ∷ []) (c ∷ []) (x ∷ []) (d ∷ []) (b ∷ []) (a≤c , c≤x , x≤d , (d≤b , ⋆)) = ≤-swap d b d≤b

neg-Condition-1b : (c x d : Vec ℤ[1/2] 1)
                 → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)             
                 → (neg-L (zip (c , d)) ≤ℤ[1/2] neg-D x)
neg-Condition-1b (c ∷ []) (x ∷ []) (d ∷ []) (c≤x , (x≤d , ⋆)) = ≤-swap x d x≤d

neg-Condition-1c : (c x d : Vec ℤ[1/2] 1)
                 → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)              
                 → (neg-D x ≤ℤ[1/2] neg-R (zip (c , d)))
neg-Condition-1c (c ∷ []) (x ∷ []) (d ∷ []) ((c≤x , ⋆) , x≤d) = ≤-swap c x c≤x

neg-Condition-1d : (a c x d b : Vec ℤ[1/2] 1)
                 → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)              
                 → (neg-R (zip (c , d)) ≤ℤ[1/2] neg-R (zip (a , b)))
neg-Condition-1d (a ∷ []) (c ∷ []) (x ∷ []) (d ∷ []) (b ∷ []) ((a≤c , ⋆) , c≤x , x≤d , d≤b) = ≤-swap a c a≤c
 
neg-Condition-2 : (x : Vec ℤ[1/2] 1) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε)
                → Σ (a , b) ꞉ Vec ℤ[1/2] 1 × Vec ℤ[1/2] 1 , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (neg-L (zip (a , b))) (neg-D x) ε 0<ε
neg-Condition-2 (x ∷ []) ε 0<ε with (no-min x) 
... | (a , a<x) with dense x (x + ε) (ℤ[1/2]<-+ x ε 0<ε)
... | (b , x<b , b<x+ε) = ((a ∷ []) , (b ∷ [])) , ((a<x , ⋆) , (x<b , ⋆) , goal)
 where
  l₁ : (b - x) < ε
  l₁ = <-swap-consequence b x ε b<x+ε
  l₂ : metric b x < ε
  l₂ = transport (_< ε) (ℤ[1/2]-pos-abs x b x<b) l₁
  goal : metric (- b) (- x) < ε
  goal = ℤ[1/2]-metric-neg b x ε 0<ε l₂

neg-Condition-3 : (x : Vec ℤ[1/2] 1) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε)
                → Σ (a , b) ꞉ Vec ℤ[1/2] 1 × Vec ℤ[1/2] 1 , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (neg-R (zip (a , b))) (neg-D x) ε 0<ε
neg-Condition-3 (x ∷ []) ε 0<ε with no-max x
... | (b , x<b) with dense (x - ε) x (ℤ[1/2]<-neg x ε 0<ε)
... | (a , x-ε<a , a<x) = ((a ∷ []) , (b ∷ [])) , (a<x , ⋆) , (x<b , ⋆) , goal
 where 
  l₁ : x < (a + ε)
  l₁ = ℤ[1/2]<-neg' x ε a x-ε<a
  l₂ : (x - a) < ε
  l₂ = ℤ[1/2]<-+' x a ε l₁
  l₃ : ℤ[1/2]-abs (x - a) < ε
  l₃ = transport (_< ε) (ℤ[1/2]-pos-abs a x a<x) l₂
  l₄ : Bℤ[1/2] a x ε 0<ε
  l₄ = ℤ[1/2]-metric-comm x a ε 0<ε l₃
  goal : (metric (- a) (- x)) < ε
  goal = ℤ[1/2]-metric-neg a x ε 0<ε l₄

negation-collection : Collection 0
negation-collection = record
                        { D = neg-D
                        ; L = neg-L
                        ; R = neg-R
                        ; Condition-1a = neg-Condition-1a
                        ; Condition-1b = neg-Condition-1b
                        ; Condition-1c = neg-Condition-1c
                        ; Condition-1d = neg-Condition-1d
                        ; Condition-2 = neg-Condition-2
                        ; Condition-3 = neg-Condition-3
                        }

add-D : Vec ℤ[1/2] 2 → ℤ[1/2]
add-D (x ∷ y ∷ [])= x + y

add-L : Vec (ℤ[1/2] × ℤ[1/2]) 2 → ℤ[1/2]
add-L ((a₁ , b₁) ∷ (a₂ , b₂) ∷ []) = a₁ + a₂

add-R : Vec (ℤ[1/2] × ℤ[1/2]) 2 → ℤ[1/2]
add-R ((a₁ , b₁) ∷ (a₂ , b₂) ∷ []) = b₁ + b₂

add-condition-1a : (a c x d b : Vec ℤ[1/2] 2)
                 → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)
                 → add-L (zip (a , b)) ≤ℤ[1/2] add-L (zip (c , d))
add-condition-1a (a₁ ∷ a₂ ∷ []) (c₁ ∷ c₂ ∷ []) (x₁ ∷ x₂ ∷ []) (d₁ ∷ d₂ ∷ []) (b₁ ∷ b₂ ∷ [])
                 ((a₁≤c₁ , a₂≤c₂ , ⋆) , (c₁≤x₁ , c₂≤x₂ , ⋆) , (x₁≤d₁ , x₂≤d₂ , ⋆) , (d₁≤b₁ , d₂≤b₂ , ⋆))
 = ℤ[1/2]≤-adding a₁ c₁ a₂ c₂ a₁≤c₁ a₂≤c₂

add-condition-1b : (c x d : Vec ℤ[1/2] 2)
                 → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)
                 → add-L (zip (c , d)) ≤ℤ[1/2] add-D x
add-condition-1b (c₁ ∷ c₂ ∷ []) (x₁ ∷ x₂ ∷ []) (d₁ ∷ d₂ ∷ [])
                 ((c₁≤x₁ , c₂≤x₂ , ⋆) , (x₁≤d₁ , x₂≤d₂ , ⋆))
 = ℤ[1/2]≤-adding c₁ x₁ c₂ x₂ c₁≤x₁ c₂≤x₂

add-condition-1c : (c x d : Vec ℤ[1/2] 2)
                 → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)
                 → add-D x ≤ℤ[1/2] add-R (zip (c , d))
add-condition-1c (c₁ ∷ c₂ ∷ []) (x₁ ∷ x₂ ∷ []) (d₁ ∷ d₂ ∷ [])
                 ((c₁≤x₁ , c₂≤x₂ , ⋆) , (x₁≤d₁ , x₂≤d₂ , ⋆)) = ℤ[1/2]≤-adding x₁ d₁ x₂ d₂ x₁≤d₁ x₂≤d₂

add-condition-1d : (a c x d b : Vec ℤ[1/2] 2)
                 → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)
                 → add-R (zip (c , d)) ≤ℤ[1/2] add-R (zip (a , b))
add-condition-1d (a₁ ∷ a₂ ∷ []) (c₁ ∷ c₂ ∷ []) (x₁ ∷ x₂ ∷ []) (d₁ ∷ d₂ ∷ []) (b₁ ∷ b₂ ∷ [])
                 ((a₁≤c₁ , a₂≤c₂ , ⋆) , (c₁≤x₁ , c₂≤x₂ , ⋆) , (x₁≤d₁ , x₂≤d₂ , ⋆) , (d₁≤b₁ , d₂≤b₂ , ⋆))
 = ℤ[1/2]≤-adding d₁ b₁ d₂ b₂ d₁≤b₁ d₂≤b₂

add-condition-2 : (x : Vec ℤ[1/2] 2) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε)
                → Σ (a , b) ꞉ Vec ℤ[1/2] 2 × Vec ℤ[1/2] 2 , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (add-L (zip (a , b))) (add-D x) ε 0<ε
add-condition-2 (x₁ ∷ x₂ ∷ []) ε l = I 
 where
  l₂ : 0ℤ[1/2] < (1/2 * ε)
  l₂ = <-pos-mult' 1/2 ε 0<1/2ℤ[1/2] l
  I : Σ (a , b) ꞉ Vec ℤ[1/2] 2 × Vec ℤ[1/2] 2 , (a Vecℤ[1/2]< (x₁ ∷ x₂ ∷ [])) × ((x₁ ∷ x₂ ∷ []) Vecℤ[1/2]< b) × Bℤ[1/2] (add-L (zip (a , b))) (add-D (x₁ ∷ x₂ ∷ [])) ε l
  I with dense (x₁ - (1/2 * ε)) x₁ (ℤ[1/2]<-neg x₁ (1/2 * ε) l₂)
  ... | a₁ , (x-ε/2<a₁ , a₁<x₁) with dense (x₂ - (1/2 * ε)) x₂ (ℤ[1/2]<-neg x₂ (1/2 * ε) l₂)
  ... | a₂ , (x-ε/2<a₂ , a₂<x₂) with no-max x₁
  ... | b₁ , x₁<b₁ with no-max x₂
  ... | b₂ , x₂<b₂ = ((a₁ ∷ a₂ ∷ []) , b₁ ∷ b₂ ∷ []) , ((a₁<x₁ , a₂<x₂ , ⋆) , (x₁<b₁ , x₂<b₂ , ⋆) , goal)
   where
    l₁ : ((x₁ + x₂) - ε) < (a₁ + a₂)
    l₁ = transport (_< (a₁ + a₂)) e₁ (ℤ[1/2]<-adding (x₁ - (1/2 * ε)) a₁ (x₂ - (1/2 * ε)) a₂ x-ε/2<a₁ x-ε/2<a₂)
     where
      e₁ : (x₁ - (1/2 * ε)) + (x₂ - (1/2 * ε)) ＝ ((x₁ + x₂) - ε)
      e₁ = ((x₁ - (1/2 * ε)) + (x₂ - (1/2 * ε)))         ＝⟨ ℤ[1/2]+-assoc (x₁ - (1/2 * ε)) x₂ (- (1/2 * ε)) ⁻¹ ⟩
           (((x₁ - (1/2 * ε)) + x₂) + (- (1/2 * ε)))     ＝⟨ ap (_+ (- (1/2 * ε))) (ℤ[1/2]+-assoc x₁ (- (1/2 * ε)) x₂) ⟩
           ((x₁ + ((- (1/2 * ε)) + x₂)) + (- (1/2 * ε))) ＝⟨ ap (λ z → ((x₁ + z) + (- (1/2 * ε)))) (ℤ[1/2]+-comm (- (1/2 * ε)) x₂) ⟩
           ((x₁ + (x₂ + (- (1/2 * ε)))) + (- (1/2 * ε))) ＝⟨ ap (_+ (- (1/2 * ε))) (ℤ[1/2]+-assoc x₁ x₂ (- (1/2 * ε)) ⁻¹) ⟩
           (((x₁ + x₂) + (- (1/2 * ε))) + (- (1/2 * ε))) ＝⟨ ℤ[1/2]+-assoc (x₁ + x₂) (- (1/2 * ε)) (- (1/2 * ε)) ⟩
           ((x₁ + x₂) + ((- (1/2 * ε)) - (1/2 * ε)))     ＝⟨ ap ((x₁ + x₂) +_) (ℤ[1/2]-minus-dist (1/2 * ε) (1/2 * ε) ⁻¹) ⟩
           ((x₁ + x₂) - ((1/2 * ε) + (1/2 * ε)))         ＝⟨ ap (λ z → ((x₁ + x₂) - z)) (ℤ[1/2]-dist 1/2 1/2 ε) ⟩
           (x₁ + x₂) - ((1/2 + 1/2) * ε)                       ＝⟨ ap (λ z → (x₁ + x₂) - (z * ε)) 1/2+1/2ℤ[1/2] ⟩
           (x₁ + x₂) - (1ℤ[1/2] * ε)                           ＝⟨ ap (λ z → (x₁ + x₂) - z) (ℤ[1/2]-mult-left-id ε) ⟩
           ((x₁ + x₂) - ε) ∎

    l₃ : (a₁ + a₂) < ((x₁ + x₂) + ε)
    l₃ = trans (a₁ + a₂) (x₁ + x₂) ((x₁ + x₂) + ε) (ℤ[1/2]<-adding a₁ x₁ a₂ x₂ a₁<x₁ a₂<x₂) (ℤ[1/2]<-+ (x₁ + x₂) ε l)

    l₄ : ((a₁ + a₂) - (x₁ + x₂)) < ε
    l₄ = ℤ[1/2]<-+' (a₁ + a₂) (x₁ + x₂) ε l₃
    
    l₅ : (- ε) < (((a₁ + a₂) - (x₁ + x₂)))
    l₅ = ℤ[1/2]<-rearrange (x₁ + x₂) (- ε) (a₁ + a₂) l₁

    goal : Bℤ[1/2] (a₁ + a₂) (x₁ + x₂) ε l
    goal = ℤ[1/2]<-to-abs ((a₁ + a₂) - (x₁ + x₂)) ε (l₅ , l₄)

add-condition-3 : (x : Vec ℤ[1/2] 2) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε)
                → Σ (a , b) ꞉ Vec ℤ[1/2] 2 × Vec ℤ[1/2] 2 , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (add-R (zip (a , b))) (add-D x) ε 0<ε
add-condition-3 (x₁ ∷ x₂ ∷ []) ε l = I
 where
  l₂ : 0ℤ[1/2] < (1/2 * ε)
  l₂ = <-pos-mult' 1/2 ε 0<1/2ℤ[1/2] l
  I : Σ (a , b) ꞉ Vec ℤ[1/2] 2 × Vec ℤ[1/2] 2 , (a Vecℤ[1/2]< (x₁ ∷ x₂ ∷ [])) × ((x₁ ∷ x₂ ∷ []) Vecℤ[1/2]< b) × Bℤ[1/2] (add-R (zip (a , b))) (add-D (x₁ ∷ x₂ ∷ [])) ε l
  I with dense x₁ (x₁ + (1/2 * ε)) (ℤ[1/2]<-+ x₁ (1/2 * ε) l₂)
  ... | b₁ , (x₁<b₁ , b₁<x₁+ε/2) with dense x₂ (x₂ + (1/2 * ε)) (ℤ[1/2]<-+ x₂ (1/2 * ε) l₂)
  ... | b₂ , (x₂<b₂ , b₂<x₂+ε/2) with no-min x₁
  ... | a₁ , a₁<x₁ with no-min x₂
  ... | a₂ , a₂<x₂ = ((a₁ ∷ a₂ ∷ []) , (b₁ ∷ b₂ ∷ [])) , ((a₁<x₁ , a₂<x₂ , ⋆) , ((x₁<b₁ , x₂<b₂ , ⋆) , goal))
   where
    l₅ :(b₁ + b₂) < ((x₁ + (1/2 * ε)) + (x₂ + (1/2 * ε)))
    l₅ = ℤ[1/2]<-adding b₁ (x₁ + (1/2 * ε)) b₂ (x₂ + (1/2 * ε)) b₁<x₁+ε/2 b₂<x₂+ε/2
    l₆ : (b₁ + b₂) < ((x₁ + x₂) + ε)
    l₆ = transport ((b₁ + b₂) <_) e₁ (ℤ[1/2]<-adding b₁ (x₁ + (1/2 * ε)) b₂ (x₂ + (1/2 * ε)) b₁<x₁+ε/2 b₂<x₂+ε/2)
     where
      e₁ : ((x₁ + (1/2 * ε)) + (x₂ + (1/2 * ε))) ＝ ((x₁ + x₂) + ε)
      e₁ = ((x₁ + (1/2 * ε)) + (x₂ + (1/2 * ε)))  ＝⟨ ℤ[1/2]+-assoc (x₁ + (1/2 * ε)) x₂ (1/2 * ε) ⁻¹ ⟩
            (((x₁ + (1/2 * ε)) + x₂) + (1/2 * ε)) ＝⟨ ap (_+ (1/2 * ε)) (ℤ[1/2]+-assoc x₁ (1/2 * ε) x₂) ⟩
            ((x₁ + ((1/2 * ε) + x₂)) + (1/2 * ε)) ＝⟨ ap (λ z → (x₁ + z) + (1/2 * ε)) (ℤ[1/2]+-comm (1/2 * ε) x₂) ⟩
            ((x₁ + (x₂ + (1/2 * ε))) + (1/2 * ε)) ＝⟨ ap (_+ (1/2 * ε)) (ℤ[1/2]+-assoc x₁ x₂ (1/2 * ε) ⁻¹) ⟩
            (((x₁ + x₂) + (1/2 * ε)) + (1/2 * ε)) ＝⟨ ℤ[1/2]+-assoc (x₁ + x₂) (1/2 * ε) (1/2 * ε) ⟩
            ((x₁ + x₂) + ((1/2 * ε) + (1/2 * ε))) ＝⟨ ap ((x₁ + x₂) +_) (ℤ[1/2]-dist 1/2 1/2 ε) ⟩
            ((x₁ + x₂) + ((1/2 + 1/2) * ε))       ＝⟨ ap (λ z → (x₁ + x₂) + (z * ε)) 1/2+1/2ℤ[1/2] ⟩
            ((x₁ + x₂) + (1ℤ[1/2] * ε))           ＝⟨ ap ((x₁ + x₂) +_) (ℤ[1/2]-mult-left-id ε) ⟩
            ((x₁ + x₂) + ε) ∎
    l₃ : (- ε) < ((b₁ + b₂) - (x₁ + x₂))
    l₃ = trans (- ε) 0ℤ[1/2] ((b₁ + b₂) - (x₁ + x₂))
          (transport ((- ε) <_) (ℤ[1/2]-minus-zero ⁻¹) (<-swap 0ℤ[1/2] ε l))
           (diff-positive (x₁ + x₂) (b₁ + b₂) (ℤ[1/2]<-adding x₁ b₁ x₂ b₂ x₁<b₁ x₂<b₂))
    l₄ : ((b₁ + b₂) - (x₁ + x₂)) < ε
    l₄ = <-swap-consequence (b₁ + b₂) (x₁ + x₂) ε l₆
    goal : Bℤ[1/2] (b₁ + b₂) (x₁ + x₂) ε l
    goal = ℤ[1/2]<-to-abs ((b₁ + b₂) - (x₁ + x₂)) ε (l₃ , l₄)
    
addition-collection : Collection 1
addition-collection = record
                        { D = add-D
                        ; L = add-L
                        ; R = add-R
                        ; Condition-1a = add-condition-1a
                        ; Condition-1b = add-condition-1b
                        ; Condition-1c = add-condition-1c
                        ; Condition-1d = add-condition-1d
                        ; Condition-2 = add-condition-2
                        ; Condition-3 = add-condition-3
                        }

open Collection

tbr- : 𝕋 → 𝕋
tbr- x = F* negation-collection (x ∷ [])


```
