Andrew Sneap, 17 February 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Addition
open import Dyadics.Negation
open import Dyadics.Type
open import Dyadics.Order
open import Integers.Addition renaming (_+_ to _ℤ+_ ; _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Order
open import Integers.Type
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Exponentiation
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Notation.Order
open import UF.Base hiding (_≈_)

module Dyadics.Multiplication where

\end{code}

Instead of defining multiplication by pattern matching, we define it
by using the reducing function. This has efficiency implications, but
avoiding pattern matching helps to reduce the size of proofs.

We use an intermediate _*'_ relation (as in the approach with rationals).

\begin{code}

_*'_ : (p q : ℤ × ℕ) → ℤ × ℕ
(p , a) *' (q , b) = p ℤ* q , a ℕ+ b

ℤ[1/2]*'-comm : (p q : ℤ × ℕ) → p *' q ＝ q *' p
ℤ[1/2]*'-comm (p , a) (q , b) = ap₂ _,_ I II
 where
  I : p ℤ* q ＝ q ℤ* p
  I = ℤ*-comm p q
  II : a ℕ+ b ＝ b ℕ+ a
  II = addition-commutativity a b

infixl 33 _*'_

_*_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
(p , _) * (q , _) = normalise-pos (p *' q)

infixl 33 _*_

\end{code}

Commutativity for multiplication is trivial (as usual), relying only
on commutativity properties of integer multiplication and natural
number addition.

\begin{code}

ℤ[1/2]*-comm : (p q : ℤ[1/2]) → (p * q) ＝ (q * p)
ℤ[1/2]*-comm ((p , a) , α) ((q , b) , β) = γ
 where
  γ : (((p , a) , α) * ((q , b) , β)) ＝ (((q , b) , β) * ((p , a) , α))
  γ = ((p , a) , α) * ((q , b) , β)   ＝⟨ refl  ⟩
      normalise-pos (p ℤ* q , a ℕ+ b) ＝⟨ i ⟩
      normalise-pos (q ℤ* p , b ℕ+ a) ＝⟨ refl ⟩
      ((q , b) , β) * ((p , a) , α)   ∎
   where
    i = ap normalise-pos (ℤ[1/2]*'-comm (p , a) (q , b))

\end{code}

Looking towards the associativity proof, we expect to need the proof
that multiplication respects the normalisation function on dyadic
rationals.

We will also need the prove associativity of the intermediate
multiplication operation.

\begin{code}

ℤ[1/2]-rearrangement-lemma : (p q : ℤ) (a b : ℕ)
 → p ℤ* q ℤ* pos (2^ (a ℕ+ b)) ＝ p ℤ* pos (2^ a) ℤ* q ℤ* pos (2^ b)
ℤ[1/2]-rearrangement-lemma p q a b = γ
 where
  γ : p ℤ* q ℤ* pos (2^ (a ℕ+ b)) ＝ p ℤ* pos (2^ a) ℤ* q ℤ* pos (2^ b)
  γ = p ℤ* q ℤ* pos (2^ (a ℕ+ b))          ＝⟨ i   ⟩
      p ℤ* q ℤ* pos (2^ a ℕ* 2^ b)         ＝⟨ ii  ⟩
      p ℤ* q ℤ* (pos (2^ a) ℤ* pos (2^ b)) ＝⟨ iii ⟩
      p ℤ* q ℤ* pos (2^ a) ℤ* pos (2^ b)   ＝⟨ iv  ⟩
      p ℤ* (q ℤ* pos (2^ a)) ℤ* pos (2^ b) ＝⟨ v   ⟩
      p ℤ* (pos (2^ a) ℤ* q) ℤ* pos (2^ b) ＝⟨ vi  ⟩
      p ℤ* pos (2^ a) ℤ* q ℤ* pos (2^ b)   ∎
   where
    i   = ap (λ - →  p ℤ* q ℤ* pos -) (prod-of-powers 2 a b ⁻¹)
    ii  = ap (p ℤ* q ℤ*_) (pos-multiplication-equiv-to-ℕ (2^ a) (2^ b) ⁻¹)
    iii = ℤ*-assoc (p ℤ* q) (pos (2^ a)) (pos (2^ b)) ⁻¹
    iv  = ap (_ℤ* pos (2^ b)) (ℤ*-assoc p q (pos (2^ a)))
    v   = ap (λ - → p ℤ* - ℤ* pos (2^ b)) (ℤ*-comm q (pos (2^ a)))
    vi  = ap (_ℤ* pos (2^ b)) (ℤ*-assoc p (pos (2^ a)) q ⁻¹)

ℤ[1/2]*'-≈' : (p q r : ℤ × ℕ) → p ≈' q → (p *' r) ≈' (q *' r)
ℤ[1/2]*'-≈' (p , a) (q , b) (r , c) e = γ
 where
  e' : p ℤ* pos (2^ b) ＝ q ℤ* pos (2^ a) -- Unfolded goal type
  e' = e
  
  γ : p ℤ* r ℤ* pos (2^ (b ℕ+ c)) ＝ q ℤ* r ℤ* pos (2^ (a ℕ+ c))
  γ = p ℤ* r ℤ* pos (2^ (b ℕ+ c))          ＝⟨ i   ⟩
      p ℤ* pos (2^ b) ℤ* r ℤ* pos (2^ c)   ＝⟨ ii  ⟩
      q ℤ* pos (2^ a) ℤ* r ℤ* pos (2^ c)   ＝⟨ iii ⟩      
      q ℤ* r ℤ* pos (2^ (a ℕ+ c)) ∎
   where
    i   = ℤ[1/2]-rearrangement-lemma p r b c
    ii  = ap (λ - → - ℤ* r ℤ* pos (2^ c)) e'
    iii = ℤ[1/2]-rearrangement-lemma q r a c ⁻¹

ℤ[1/2]*-normalise-pos : (p q : ℤ × ℕ)
 → normalise-pos (p *' q) ＝ normalise-pos p * normalise-pos q
ℤ[1/2]*-normalise-pos p q = ≈'-to-＝ (p *' q) (p' *' q') γ
 where
  p' = from-ℤ[1/2] (normalise-pos p)
  q' = from-ℤ[1/2] (normalise-pos q)

  I : p ≈' p'
  I = ≈'-normalise-pos p

  II : q ≈' q'
  II = ≈'-normalise-pos q

  III : (p *' q) ≈' (p' *' q)
  III = ℤ[1/2]*'-≈' p p' q I

  IV : (q *' p') ≈' (q' *' p')
  IV = ℤ[1/2]*'-≈' q q' p' II

  V : (p' *' q) ≈' (p' *' q')
  V = transport₂ _≈'_ (ℤ[1/2]*'-comm q p') (ℤ[1/2]*'-comm q' p') IV

  γ : (p *' q) ≈' (p' *' q')
  γ = ≈'-trans (p *' q) (p' *' q) (p' *' q') III V

ℤ[1/2]*'-assoc : (p q r : ℤ × ℕ) → p *' q *' r ＝ p *' (q *' r)
ℤ[1/2]*'-assoc (p , a) (q , b) (r , c) = γ
 where
  γ : (p , a) *' (q , b) *' (r , c) ＝ (p , a) *' ((q , b) *' (r , c))
  γ = (p , a) *' (q , b) *' (r , c)   ＝⟨ refl ⟩
      (p ℤ* q , a ℕ+ b) *' (r , c)    ＝⟨ refl ⟩
      p ℤ* q ℤ* r , a ℕ+ b ℕ+ c       ＝⟨ i    ⟩
      p ℤ* (q ℤ* r) , a ℕ+ b ℕ+ c     ＝⟨ ii   ⟩
      p ℤ* (q ℤ* r) , a ℕ+ (b ℕ+ c)   ＝⟨ refl ⟩
      (p , a) *' (q ℤ* r , b ℕ+ c)    ＝⟨ refl ⟩
      (p , a) *' ((q , b) *' (r , c)) ∎
   where
    i = ap (_, a ℕ+ b ℕ+ c) (ℤ*-assoc p q r)
    ii = ap (p ℤ* (q ℤ* r) ,_) (addition-associativity a b c)

\end{code}

Now associativity follows, since normalisation of a dyadic gives the
same dyadic, and using the above two proofs.

\begin{code}

ℤ[1/2]*-assoc : (p q r : ℤ[1/2]) → p * q * r ＝ p * (q * r)
ℤ[1/2]*-assoc (p , α) (q , β) (r , δ) = γ
 where
  γ : (p , α) * (q , β) * (r , δ) ＝ (p , α) * ((q , β) * (r , δ))
  γ = (p , α) * (q , β) * (r , δ)              ＝⟨ refl ⟩
      normalise-pos (p *' q) * (r , δ)         ＝⟨ i    ⟩
      normalise-pos (p *' q) * normalise-pos r ＝⟨ ii   ⟩
      normalise-pos ((p *' q) *' r)            ＝⟨ iii  ⟩ 
      normalise-pos (p *' (q *' r))            ＝⟨ iv   ⟩ 
      normalise-pos p * normalise-pos (q *' r) ＝⟨ v    ⟩
      (p , α) * normalise-pos (q *' r)         ＝⟨ refl ⟩
      (p , α) * ((q , β) * (r , δ))            ∎
   where
    i = ap (λ - → (normalise-pos (p *' q)) * -) (ℤ[1/2]-to-normalise-pos (r , δ))
    ii =  ℤ[1/2]*-normalise-pos (p *' q) r ⁻¹
    iii = ap normalise-pos (ℤ[1/2]*'-assoc p q r)
    iv = ℤ[1/2]*-normalise-pos p (q *' r)
    v = ap (_* normalise-pos (q *' r)) (ℤ[1/2]-to-normalise-pos (p , α) ⁻¹)

\end{code}

Now we prove the zero and unit laws for multiplication. In each case
we prove one side, and the other follows by commutativity.

\begin{code}

ℤ[1/2]*-zero-left-base : (p : ℤ[1/2]) → 0ℤ[1/2] * p ＝ 0ℤ[1/2]
ℤ[1/2]*-zero-left-base (p , α) = γ
 where
  x = pr₁ p -- numerator   of p
  a = pr₂ p -- denominator of p
  
  γ : 0ℤ[1/2] * (p , α) ＝ 0ℤ[1/2]
  γ = 0ℤ[1/2] * (p , α)                           ＝⟨ i    ⟩
      0ℤ[1/2] * normalise-pos p                   ＝⟨ refl ⟩
      normalise-pos (pos 0 , 0) * normalise-pos p ＝⟨ ii   ⟩
      normalise-pos ((pos 0 , 0) *' p)            ＝⟨ refl ⟩
      normalise-pos ((pos 0 , 0) *' (x , a))      ＝⟨ refl ⟩
      normalise-pos (pos 0 ℤ* x , 0 ℕ+ a)         ＝⟨ iii  ⟩
      normalise-pos (pos 0 , 0 ℕ+ a)              ＝⟨ iv   ⟩
      normalise-pos (pos 0 , a)                   ＝⟨ v    ⟩
      0ℤ[1/2] ∎
   where
    i   = ap (0ℤ[1/2] *_) (ℤ[1/2]-to-normalise-pos (p , α))
    ii  = ℤ[1/2]*-normalise-pos (pos 0 , 0) p ⁻¹
    iii = ap (λ - → normalise-pos (- , 0 ℕ+ a) ) (ℤ-zero-left-base x)
    iv  = ap (λ - → normalise-pos (pos 0 , -)) (zero-left-neutral a)
    v   = ℤ[1/2]-numerator-zero-is-zero' a

ℤ[1/2]*-zero-right-base : (p : ℤ[1/2]) → p * 0ℤ[1/2] ＝ 0ℤ[1/2]
ℤ[1/2]*-zero-right-base p = ℤ[1/2]*-comm p 0ℤ[1/2] ∙ ℤ[1/2]*-zero-left-base p

ℤ[1/2]*-mult-left-id : (p : ℤ[1/2]) → 1ℤ[1/2] * p ＝ p
ℤ[1/2]*-mult-left-id (p , α) = γ
 where
  x = pr₁ p -- numerator   of p
  a = pr₂ p -- denominator of p

  I : (pos 1 , 0) *' (x , a) ＝ (x , a)
  I = (pos 1 , 0) *' (x , a) ＝⟨ refl ⟩
      pos 1 ℤ* x , 0 ℕ+ a    ＝⟨ ap (_, 0 ℕ+ a) (ℤ-mult-left-id x) ⟩
      x , 0 ℕ+ a             ＝⟨ ap (x ,_) (zero-left-neutral a) ⟩
      x , a ∎
  
  γ : 1ℤ[1/2] * (p , α) ＝ (p , α)
  γ = 1ℤ[1/2] * (p , α)                           ＝⟨ i    ⟩
      1ℤ[1/2] * normalise-pos p                   ＝⟨ ii   ⟩
      normalise-pos (pos 1 , 0) * normalise-pos p ＝⟨ iii  ⟩
      normalise-pos ((pos 1 , 0) *' (x , a))      ＝⟨ iv   ⟩
      normalise-pos (x , a)                       ＝⟨ refl ⟩
      normalise-pos p                             ＝⟨ v    ⟩      
      (p , α) ∎
   where
    i  = ap (1ℤ[1/2] *_) (ℤ[1/2]-to-normalise-pos (p , α))
    ii  = ap (_* normalise-pos p) (ℤ[1/2]-to-normalise-pos 1ℤ[1/2])
    iii = ℤ[1/2]*-normalise-pos (pos 1 , 0) p ⁻¹
    iv  = ap normalise-pos I
    v   = ℤ[1/2]-to-normalise-pos (p , α) ⁻¹

ℤ[1/2]*-mult-right-id : (p : ℤ[1/2]) → p * 1ℤ[1/2] ＝ p
ℤ[1/2]*-mult-right-id p = ℤ[1/2]*-comm p 1ℤ[1/2] ∙ ℤ[1/2]*-mult-left-id p

ℤ[1/2]-distributivity-lemma : (p q r : ℤ × ℕ)
                            → p *' (q +' r) ≈' p *' q +' p *' r
ℤ[1/2]-distributivity-lemma (p , a) (q , b) (r , c) = γ
 where
  a' = pos (2^ a)
  b' = pos (2^ b)
  c' = pos (2^ c)

  ac = pos (2^ (a ℕ+ c))
  ca = pos (2^ (c ℕ+ a))
  ab = pos (2^ (a ℕ+ b))
  ba = pos (2^ (b ℕ+ a))
  abc = pos (2^ (a ℕ+ (b ℕ+ c)))
  abac = pos (2^ (a ℕ+ b ℕ+ (a ℕ+ c)))

  lem₁ : (x y : ℕ) → pos (2^ (x ℕ+ y)) ＝ pos (2^ x) ℤ* pos (2^ y)
  lem₁ x y = 
   pos (2^ (x ℕ+ y))        ＝⟨ ap pos (prod-of-powers 2 x y ⁻¹)               ⟩
   pos (2^ x ℕ* 2^ y)       ＝⟨ pos-multiplication-equiv-to-ℕ (2^ x) (2^ y) ⁻¹ ⟩
   pos (2^ x) ℤ* pos (2^ y) ∎

  lem₂ : (w x : ℤ) (y z : ℕ) → w ℤ* x ℤ* pos (2^ y) ℤ* pos (2^ z)
       ＝ w ℤ* x ℤ* pos (2^ (y ℕ+ z))
  lem₂ w x y z =
   w ℤ* x ℤ* y' ℤ* z'            ＝⟨ i ⟩
   w ℤ* x ℤ* (y' ℤ* z')         ＝⟨ ii ⟩
   w ℤ* x ℤ* pos (2^ y ℕ* 2^ z) ＝⟨ iii ⟩
   w ℤ* x ℤ* pos (2^ (y ℕ+ z))  ∎
    where
     y'  = pos (2^ y)
     z'  = pos (2^ z)
     i   = ℤ*-assoc (w ℤ* x) y' z'
     ii  = ap (λ - → w ℤ* x ℤ* -) (pos-multiplication-equiv-to-ℕ (2^ y) (2^ z))
     iii = ap (λ - → w ℤ* x ℤ* pos -) (prod-of-powers 2 y z)
 
  I : (p ℤ* q ℤ* c' ℤ+ p ℤ* r ℤ* b') ℤ* a' ＝ p ℤ* q ℤ* ac ℤ+ p ℤ* r ℤ* ab
  I = (p ℤ* q ℤ* c' ℤ+ p ℤ* r ℤ* b') ℤ* a'     ＝⟨ i   ⟩
      p ℤ* q ℤ* c' ℤ* a' ℤ+ p ℤ* r ℤ* b' ℤ* a' ＝⟨ ii  ⟩
      p ℤ* q ℤ* c' ℤ* a' ℤ+ p ℤ* r ℤ* ba       ＝⟨ iii ⟩
      p ℤ* q ℤ* ca ℤ+ p ℤ* r ℤ* ba             ＝⟨ iv  ⟩
      p ℤ* q ℤ* ac ℤ+ p ℤ* r ℤ* ba             ＝⟨ v ⟩
      p ℤ* q ℤ* ac ℤ+ p ℤ* r ℤ* ab             ∎
   where
    ivₐₚ : c ℕ+ a ＝ a ℕ+ c
    ivₐₚ = addition-commutativity c a
    vₐₚ : b ℕ+ a ＝ a ℕ+ b
    vₐₚ = addition-commutativity b a
    
    i   = distributivity-mult-over-ℤ (p ℤ* q ℤ* c') (p ℤ* r ℤ* b') a'
    ii  = ap (p ℤ* q ℤ* c' ℤ* a' ℤ+_) (lem₂ p r b a)
    iii = ap (_ℤ+ p ℤ* r ℤ* ba) (lem₂ p q c a)
    iv  = ap (λ - → p ℤ* q ℤ* pos (2^ -) ℤ+ p ℤ* r ℤ* ba) ivₐₚ
    v   = ap (λ - → p ℤ* q ℤ* ac ℤ+ p ℤ* r ℤ* pos (2^ -)) vₐₚ

  IIᵢ : b ℕ+ (a ℕ+ c) ＝ a ℕ+ (b ℕ+ c)
  IIᵢ = b ℕ+ (a ℕ+ c) ＝⟨ addition-associativity b a c ⁻¹         ⟩
        b ℕ+ a ℕ+ c   ＝⟨ ap (_ℕ+ c) (addition-commutativity b a) ⟩
        a ℕ+ b ℕ+ c   ＝⟨ addition-associativity a b c            ⟩
        a ℕ+ (b ℕ+ c) ∎

  II : abac ＝ a' ℤ* abc
  II = pos (2^ (a ℕ+ b ℕ+ (a ℕ+ c)))          ＝⟨ i   ⟩
       pos (2^ (a ℕ+ (b ℕ+ (a ℕ+ c))))        ＝⟨ ii  ⟩
       pos (2^ a) ℤ* pos (2^ (b ℕ+ (a ℕ+ c))) ＝⟨ iii ⟩
       pos (2^ a) ℤ* pos (2^ (a ℕ+ (b ℕ+ c))) ∎
   where
    i   = ap (pos ∘ 2^) (addition-associativity a b (a ℕ+ c))
    ii  = lem₁ a (b ℕ+ (a ℕ+ c))
    iii = ap (λ z → pos (2^ a) ℤ* pos (2^ z)) IIᵢ

  III : p ℤ* (q ℤ* c' ℤ+ r ℤ* b') ＝ p ℤ* q ℤ* c' ℤ+ p ℤ* r ℤ* b'
  III = p ℤ* (q ℤ* c' ℤ+ r ℤ* b')        ＝⟨ i   ⟩
        p ℤ* (q ℤ* c') ℤ+ p ℤ* (r ℤ* b') ＝⟨ ii  ⟩
        p ℤ* q ℤ* c' ℤ+ p ℤ* (r ℤ* b')   ＝⟨ iii ⟩
        p ℤ* q ℤ* c' ℤ+ p ℤ* r ℤ* b'     ∎
   where
    i   = distributivity-mult-over-ℤ' (q ℤ* c') (r ℤ* b') p
    ii  = ap (_ℤ+ p ℤ* (r ℤ* b')) (ℤ*-assoc p q c') ⁻¹
    iii = ap (p ℤ* q ℤ* c' ℤ+_) (ℤ*-assoc p r b' ⁻¹)

  γ : p ℤ* (q ℤ* c' ℤ+ r ℤ* b') ℤ* abac
    ＝ (p ℤ* q ℤ* ac ℤ+ p ℤ* r ℤ* ab) ℤ* abc
  γ = p ℤ* (q ℤ* c' ℤ+ r ℤ* b') ℤ* abac             ＝⟨ i   ⟩
      p ℤ* (q ℤ* c' ℤ+ r ℤ* b') ℤ* (a' ℤ* abc)      ＝⟨ ii  ⟩
      (p ℤ* q ℤ* c' ℤ+ p ℤ* r ℤ* b') ℤ* (a' ℤ* abc) ＝⟨ iii ⟩
      (p ℤ* q ℤ* c' ℤ+ p ℤ* r ℤ* b') ℤ* a' ℤ* abc   ＝⟨ iv  ⟩
      (p ℤ* q ℤ* ac ℤ+ p ℤ* r ℤ* ab) ℤ* abc         ∎
   where
    i   = ap (p ℤ* (q ℤ* c' ℤ+ r ℤ* b') ℤ*_) II
    ii  = ap (_ℤ* (a' ℤ* abc)) III
    iii = ℤ*-assoc (p ℤ* q ℤ* c' ℤ+ p ℤ* r ℤ* b') a' (abc) ⁻¹
    iv  = ap (_ℤ* abc) I

ℤ[1/2]-distributivity : (p q r : ℤ[1/2]) → p * (q + r) ＝ p * q + p * r
ℤ[1/2]-distributivity (p , α) (q , β) (r , δ) = γ
 where
  I : p , α ＝ normalise-pos p
  I = ℤ[1/2]-to-normalise-pos (p , α)
  
  γ : (p , α) * ((q , β) + (r , δ)) ＝ (p , α) * (q , β) + (p , α) * (r , δ)
  γ = (p , α) * ((q , β) + (r , δ))                   ＝⟨ refl ⟩
      (p , α) * normalise-pos (q +' r)                ＝⟨ i    ⟩
      normalise-pos p * normalise-pos (q +' r)        ＝⟨ ii   ⟩
      normalise-pos (p *' (q +' r))                   ＝⟨ iii  ⟩
      normalise-pos (p *' q +' p *' r)                ＝⟨ iv   ⟩
      normalise-pos (p *' q) + normalise-pos (p *' r) ＝⟨ refl ⟩      
      (p , α) * (q , β) + (p , α) * (r , δ)           ∎
   where
    iiiₐₚ : p *' (q +' r) ≈' p *' q +' p *' r
    iiiₐₚ = ℤ[1/2]-distributivity-lemma p q r
    
    i   = ap (_* normalise-pos (q +' r)) I
    ii  = ℤ[1/2]*-normalise-pos p (q +' r) ⁻¹
    iii = ≈'-to-＝ (p *' (q +' r)) (p *' q +' p *' r) iiiₐₚ
    iv  = ℤ[1/2]+-normalise-pos (p *' q) (p *' r)

ℤ[1/2]-distributivity' : (p q r : ℤ[1/2]) → (p + q) * r ＝ p * r + q * r 
ℤ[1/2]-distributivity' p q r = γ
 where
  γ : (p + q) * r ＝ p * r + q * r
  γ = (p + q) * r   ＝⟨ ℤ[1/2]*-comm (p + q) r           ⟩
      r * (p + q)   ＝⟨ ℤ[1/2]-distributivity r p q      ⟩
      r * p + r * q ＝⟨ ap (_+ r * q) (ℤ[1/2]*-comm r p) ⟩
      p * r + r * q ＝⟨ ap (p * r +_) (ℤ[1/2]*-comm r q) ⟩ 
      p * r + q * r ∎

ℤ[1/2]-negation-dist-over-mult : (p q : ℤ[1/2]) → (- p) * q ＝ - (p * q)
ℤ[1/2]-negation-dist-over-mult ((p , a) , α) ((q , b) , β) = γ
 where
  γ : (- ((p , a) , α)) * ((q , b) , β) ＝ - ((p , a) , α) * ((q , b) , β)
  γ = (- ((p , a) , α)) * ((q , b) , β)                ＝⟨ refl ⟩
      normalise-pos (ℤ- p , a) * ((q , b) , β)         ＝⟨ i    ⟩
      normalise-pos (ℤ- p , a) * normalise-pos (q , b) ＝⟨ ii   ⟩
      normalise-pos ((ℤ- p , a) *' (q , b))            ＝⟨ refl ⟩
      normalise-pos ((ℤ- p) ℤ* q , (a ℕ+ b))           ＝⟨ refl ⟩
      normalise-pos ((ℤ- p) ℤ* q , a ℕ+ b)             ＝⟨ iii  ⟩
      normalise-pos (ℤ- p ℤ* q , a ℕ+ b)               ＝⟨ iv   ⟩
      - normalise-pos (p ℤ* q , a ℕ+ b)                ＝⟨ refl ⟩      
      - normalise-pos ((p , a) *' (q , b))             ＝⟨ refl ⟩
      - ((p , a) , α) * ((q , b) , β)                  ∎
   where
    iₐₚ : (q , b) , β ＝ normalise-pos (q , b)
    iₐₚ = ℤ[1/2]-to-normalise-pos ((q , b) , β)
    
    i   = ap (normalise-pos (ℤ- p , a) *_) iₐₚ
    ii  = ℤ[1/2]*-normalise-pos (ℤ- p , a) (q , b) ⁻¹
    iii = ap (λ - → normalise-pos (- , a ℕ+ b) ) (negation-dist-over-mult' p q)
    iv  = minus-normalise-pos (p ℤ* q) (a ℕ+ b) ⁻¹

ℤ[1/2]<'-pos-multiplication-preserves-order : (p q : ℤ × ℕ)
                                           → (pos 0 , 0) < p
                                           → (pos 0 , 0) < q
                                           → (pos 0 , 0) < p *' q
ℤ[1/2]<'-pos-multiplication-preserves-order (p , a) (q , b) l₁ l₂ = γ
 where
  I : pos 0 < p
  I = transport (_< p) (ℤ-zero-left-base (pos (2^ a))) l₁

  II : pos 0 < q
  II = transport (_< q) (ℤ-zero-left-base (pos (2^ b))) l₂

  III : pos 0 < p ℤ* q
  III = ℤ<-pos-multiplication-preserves-order p q I II

  γ : pos 0 ℤ* pos (2^ (a ℕ+ b)) < p ℤ* q
  γ = transport (_< p ℤ* q) (ℤ-zero-left-base (pos (2^ (a ℕ+ b))) ⁻¹) III

ℤ[1/2]<-pos-multiplication-preserves-order : (p q : ℤ[1/2])
                                           → 0ℤ[1/2] < p
                                           → 0ℤ[1/2] < q
                                           → 0ℤ[1/2] < p * q
ℤ[1/2]<-pos-multiplication-preserves-order (p , _) (q , _) l₁ l₂ = γ
 where
  I : (pos 0 , 0) < p *' q
  I = ℤ[1/2]<'-pos-multiplication-preserves-order p q l₁ l₂
  
  γ : normalise-pos (pos 0 , 0) < normalise-pos (p *' q)
  γ = normalise-pos-< (pos 0 , 0) (p *' q) I

ℤ[1/2]≤-pos-multiplication-preserves-order : (p q : ℤ[1/2])
                                           → 0ℤ[1/2] ≤ p
                                           → 0ℤ[1/2] ≤ q
                                           → 0ℤ[1/2] ≤ p * q
ℤ[1/2]≤-pos-multiplication-preserves-order p q l₁ l₂
 = I (ℤ[1/2]≤-split 0ℤ[1/2] p l₁) (ℤ[1/2]≤-split 0ℤ[1/2] q l₂)
 where
  I : 0ℤ[1/2] < p ∔ (0ℤ[1/2] ＝ p)
    → 0ℤ[1/2] < q ∔ (0ℤ[1/2] ＝ q)
    → 0ℤ[1/2] ≤ p * q
  I (inl l₃) (inl l₄) = ℤ[1/2]<-coarser-than-≤ 0ℤ[1/2] (p * q) γ
   where
    γ : 0ℤ[1/2] < p * q
    γ = ℤ[1/2]<-pos-multiplication-preserves-order p q l₃ l₄
  I (inr e) (inl l₃)  = transport (0ℤ[1/2] ≤_) γ (ℤ[1/2]≤-refl 0ℤ[1/2])
   where
    γ : 0ℤ[1/2] ＝ p * q
    γ = 0ℤ[1/2]      ＝⟨ ℤ[1/2]*-zero-left-base q ⁻¹ ⟩
        0ℤ[1/2] * q  ＝⟨ ap (_* q) e                 ⟩
        p * q        ∎
  I (inl l₃) (inr e)  = transport (0ℤ[1/2] ≤_) γ (ℤ[1/2]≤-refl 0ℤ[1/2])
   where
    γ : 0ℤ[1/2] ＝ p * q
    γ = 0ℤ[1/2]     ＝⟨ ℤ[1/2]*-zero-right-base p ⁻¹ ⟩
        p * 0ℤ[1/2] ＝⟨ ap (p *_) e                  ⟩
        p * q       ∎
  I (inr e₁) (inr e₂) = transport (0ℤ[1/2] ≤_) γ (ℤ[1/2]≤-refl 0ℤ[1/2])
   where
    γ : 0ℤ[1/2] ＝ p * q
    γ = 0ℤ[1/2]     ＝⟨ ℤ[1/2]*-zero-left-base q ⁻¹ ⟩
        0ℤ[1/2] * q ＝⟨ ap (_* q) e₁                ⟩
        p * q       ∎

ℤ[1/2]<-pos-multiplication-preserves-order' : (p q r : ℤ[1/2])
                                            → p < q
                                            → 0ℤ[1/2] < r
                                            → p * r < q * r
ℤ[1/2]<-pos-multiplication-preserves-order' p q r l₁ l₂ = γ
 where
  I : 0ℤ[1/2] < q - p
  I = ℤ[1/2]<-diff-positive p q l₁

  II : 0ℤ[1/2] < (q - p) * r
  II = ℤ[1/2]<-pos-multiplication-preserves-order (q - p) r I l₂

  III : 0ℤ[1/2] + p * r < (q - p) * r + p * r
  III = ℤ[1/2]<-addition-preserves-order 0ℤ[1/2] ((q - p) * r) (p * r) II

  IV : 0ℤ[1/2] + p * r ＝ p * r
  IV = ℤ[1/2]-zero-left-neutral (p * r)

  V : (q - p) * r + p * r ＝ q * r
  V = (q - p) * r + p * r         ＝⟨ i   ⟩
      q * r + (- p) * r + p * r   ＝⟨ ii  ⟩
      q * r + ((- p) * r + p * r) ＝⟨ iii ⟩
      q * r + ((- p * r) + p * r) ＝⟨ iv  ⟩
      q * r + 0ℤ[1/2]             ＝⟨ v   ⟩
      q * r ∎
   where
    i   = ap (_+ p * r) (ℤ[1/2]-distributivity' q (- p) r)
    ii  = ℤ[1/2]+-assoc (q * r) ((- p) * r) (p * r)
    iii = ap (λ - → q * r + (- + p * r)) (ℤ[1/2]-negation-dist-over-mult p r)
    iv  = ap (q * r +_) (ℤ[1/2]+-inverse-sum-to-zero' (p * r))
    v   = ℤ[1/2]-zero-right-neutral (q * r)

  γ : p * r < q * r
  γ = transport₂ _<_ IV V III

ℤ[1/2]-dense-up : (p q : ℤ[1/2]) → p < q → p < p + 1/2ℤ[1/2] * (q - p)
ℤ[1/2]-dense-up p q l = γ
 where
  I : 0ℤ[1/2] < q - p
  I = ℤ[1/2]<-diff-positive p q l
  
  II : 0ℤ[1/2] < 1/2ℤ[1/2] * (q - p)
  II = ℤ[1/2]<-pos-multiplication-preserves-order
        1/2ℤ[1/2] (q - p) ℤ[1/2]-0<1/2 I

  γ : p < p + 1/2ℤ[1/2] * (q - p)
  γ = ℤ[1/2]<-+ p (1/2ℤ[1/2] * (q - p)) II

ℤ[1/2]-dense-down : (p q : ℤ[1/2]) → p < q → p + 1/2ℤ[1/2] * (q - p) < q
ℤ[1/2]-dense-down p q l = γ
 where
  I : 0ℤ[1/2] < q - p
  I = ℤ[1/2]<-diff-positive p q l
  
  II : 0ℤ[1/2] < 1/2ℤ[1/2] * (q - p)
  II = ℤ[1/2]<-pos-multiplication-preserves-order
        1/2ℤ[1/2] (q - p) ℤ[1/2]-0<1/2 I

  III : p + 1/2ℤ[1/2] * (q - p) < p + 1/2ℤ[1/2] * (q - p) + 1/2ℤ[1/2] * (q - p)
  III = ℤ[1/2]<-+ (p + 1/2ℤ[1/2] * (q - p)) (1/2ℤ[1/2] * (q - p)) II

  IV : p + 1/2ℤ[1/2] * (q - p) + 1/2ℤ[1/2] * (q - p) ＝ q
  IV = p + 1/2ℤ[1/2] * (q - p) + 1/2ℤ[1/2] * (q - p)   ＝⟨ i    ⟩
       p + (1/2ℤ[1/2] * (q - p) + 1/2ℤ[1/2] * (q - p)) ＝⟨ ii   ⟩
       p + (1/2ℤ[1/2] + 1/2ℤ[1/2]) * (q - p)           ＝⟨ refl ⟩
       p + 1ℤ[1/2] * (q - p)                           ＝⟨ iii  ⟩
       p + (q - p)                                     ＝⟨ iv   ⟩
       p + ((- p) + q)                                 ＝⟨ v    ⟩
       p - p + q                                       ＝⟨ vi   ⟩
       0ℤ[1/2] + q                                     ＝⟨ vii  ⟩
       q ∎
   where
    i   = ℤ[1/2]+-assoc p (1/2ℤ[1/2] * (q - p)) (1/2ℤ[1/2] * (q - p))
    ii  = ap (p +_) (ℤ[1/2]-distributivity' 1/2ℤ[1/2] 1/2ℤ[1/2] (q - p) ⁻¹)
    iii = ap (p +_) (ℤ[1/2]*-mult-left-id (q - p))
    iv  = ap (p +_) (ℤ[1/2]+-comm q (- p))
    v   = ℤ[1/2]+-assoc p (- p) q ⁻¹
    vi  = ap (_+ q) (ℤ[1/2]+-inverse-sum-to-zero p)
    vii = ℤ[1/2]-zero-left-neutral q

  γ : p + 1/2ℤ[1/2] * (q - p) < q
  γ = transport (p + 1/2ℤ[1/2] * (q - p) <_) IV III

ℤ[1/2]-dense : (p q : ℤ[1/2]) → p < q → Σ k ꞉ ℤ[1/2] , (p < k < q)
ℤ[1/2]-dense p q l = k , γ₁ , γ₂
 where
  k : ℤ[1/2]
  k = p + 1/2ℤ[1/2] * (q - p)
  
  γ₁ : p < k
  γ₁ = ℤ[1/2]-dense-up p q l

  γ₂ : k < q
  γ₂ = ℤ[1/2]-dense-down p q l


\end{code}
