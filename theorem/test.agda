{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Rationals.HITQ
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat renaming (_·_ to _*_)
open import Cubical.Data.Int renaming (_·_ to _*ℤ_; _+_ to _+ℤ_)
open import Data.Unit
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Relation.Nullary.Base
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Empty using (⊥)

module theorem.test where

_^ℤ_ : ℤ → ℕ → ℤ
a ^ℤ zero = 1
a ^ℤ (suc n) = a *ℤ (a ^ℤ n) 

isGCDℤ : ℤ → ℤ → ℕ → Type₀
isGCDℤ (pos n) (pos m) = isGCD n m
isGCDℤ (pos n) (negsuc m) = isGCD n (suc m)
isGCDℤ (negsuc n) (pos m) = isGCD (suc n) m
isGCDℤ (negsuc n) (negsuc m) = isGCD (suc n) (suc m)

data PythTriple : ℤ → ℤ → ℤ → Set where
  PT : ∀ a b c {p} →
       ((a *ℤ a) +ℤ (b *ℤ b) ≡ (c *ℤ c)) →
       isGCDℤ a b p →
       isGCDℤ (pos p) c 1 →
       ¬ (a ≡ 0) →
       ¬ (b ≡ 0) →
       PythTriple a b c

PythTripleGen : ℤ → ℤ → ℤ → ℕ × ℕ → Type₀
PythTripleGen a b c (m , n) =
  (a ≡ pos m *ℤ pos m - pos n *ℤ pos n)
  × (b ≡ 2 *ℤ pos m *ℤ pos n)
  × (c ≡ pos m *ℤ pos m +ℤ pos n *ℤ pos n)
  
·DistR- : (x y z : ℤ) → x *ℤ (y - z) ≡ x *ℤ y - x *ℤ z
·DistR- x y z =
  x *ℤ (y +ℤ (- z)) ≡⟨ ·DistR+ x y (- z) ⟩
  (x *ℤ y) +ℤ (x *ℤ - z) ≡⟨ cong (λ z → x *ℤ y +ℤ z) (sym (-DistR· x z)) ⟩
  (x *ℤ y) +ℤ (- (x *ℤ z)) ≡⟨⟩
  (x *ℤ y) - (x *ℤ z) ∎

lemmaCubeDiff : (a b : ℤ) → (a +ℤ b) *ℤ (a - b) ≡ (a *ℤ a) - (b *ℤ b) 
lemmaCubeDiff a b =
  (a +ℤ b) *ℤ (a - b) ≡⟨ ·DistL+ a b (a - b) ⟩
  a *ℤ (a - b) +ℤ b *ℤ (a - b) ≡⟨ cong (λ x → a *ℤ (a - b) +ℤ x) (·DistR- b a b) ⟩
  a *ℤ (a - b) +ℤ (b *ℤ a - b *ℤ b) ≡⟨ cong (λ x → x +ℤ (b *ℤ a - b *ℤ b)) (·DistR- a a b) ⟩
  (a *ℤ a +ℤ - (a *ℤ b)) +ℤ (b *ℤ a +ℤ - (b *ℤ b)) ≡⟨ sym (+Assoc (a *ℤ a) (- (a *ℤ b)) (b *ℤ a +ℤ - (b *ℤ b))) ⟩
  a *ℤ a +ℤ (- (a *ℤ b) +ℤ (b *ℤ a +ℤ - (b *ℤ b))) ≡⟨ cong (λ x → a *ℤ a +ℤ x) (+Assoc (- (a *ℤ b)) (b *ℤ a) (- (b *ℤ b))) ⟩
  a *ℤ a +ℤ ((- (a *ℤ b) +ℤ b *ℤ a) +ℤ - (b *ℤ b)) ≡⟨ cong (λ x → a *ℤ a +ℤ ((- (a *ℤ b) +ℤ x) +ℤ - (b *ℤ b))) (·Comm b a) ⟩
  a *ℤ a +ℤ ((- (a *ℤ b) +ℤ (a *ℤ b)) +ℤ - (b *ℤ b)) ≡⟨ cong (λ x → a *ℤ a +ℤ (x +ℤ - (b *ℤ b))) (-Cancel' (a *ℤ b)) ⟩
  a *ℤ a +ℤ (0 +ℤ - (b *ℤ b)) ≡⟨ cong (λ x → a *ℤ a +ℤ x) (sym (pos0+ (- (b *ℤ b)))) ⟩
  (a *ℤ a) - (b *ℤ b) ∎

{-
reduceToGenerator : ∀ {a b c} → PythTriple a b c → Σ (ℕ × ℕ) (PythTripleGen a b c)
reduceToGenerator (PT a b c prf gcd1 gcd2 aNZ bNZ) =
  let
    c+a/b = con (c +ℤ a) b bNZ
  in
    {!!}

fermat4ℤ : (x y z : ℤ) → ¬ x ≡ 0 → ¬ y ≡ 0 → ¬ ((x ^ℤ 4) +ℤ (y ^ℤ 4) ≡ (z ^ℤ 4))
fermat4ℤ x y z px py = {!!}
-}
