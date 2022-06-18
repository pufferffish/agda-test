{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Rationals.HITQ
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat renaming (_·_ to _*_)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Int renaming (_·_ to _*ℤ_; _+_ to _+ℤ_)
open import Data.Unit hiding (_≤_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Relation.Nullary.Base
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Empty as ⊥

module theorem.test where

_^ℤ_ : ℤ → ℕ → ℤ
a ^ℤ zero = 1
a ^ℤ (suc n) = a *ℤ (a ^ℤ n) 

·DistR- : (x y z : ℤ) → x *ℤ (y - z) ≡ x *ℤ y - x *ℤ z
·DistR- x y z =
  x *ℤ (y +ℤ (- z)) ≡⟨ ·DistR+ x y (- z) ⟩
  (x *ℤ y) +ℤ (x *ℤ - z) ≡⟨ cong (x *ℤ y +ℤ_) (sym (-DistR· x z)) ⟩
  (x *ℤ y) - (x *ℤ z) ∎

lemmaSquareDiff : ∀ a b → (a +ℤ b) *ℤ (a - b) ≡ (a *ℤ a) - (b *ℤ b) 
lemmaSquareDiff a b =
  (a +ℤ b) *ℤ (a - b) ≡⟨ ·DistL+ a b (a - b) ⟩
  a *ℤ (a - b) +ℤ b *ℤ (a - b) ≡⟨ cong (a *ℤ (a - b) +ℤ_) (·DistR- b a b) ⟩
  a *ℤ (a - b) +ℤ (b *ℤ a - b *ℤ b) ≡⟨ cong (_+ℤ (b *ℤ a - b *ℤ b)) (·DistR- a a b) ⟩
  (a *ℤ a +ℤ - (a *ℤ b)) +ℤ (b *ℤ a +ℤ - (b *ℤ b)) ≡⟨ sym (+Assoc (a *ℤ a) (- (a *ℤ b)) (b *ℤ a +ℤ - (b *ℤ b))) ⟩
  a *ℤ a +ℤ (- (a *ℤ b) +ℤ (b *ℤ a +ℤ - (b *ℤ b))) ≡⟨ cong (a *ℤ a +ℤ_) (+Assoc (- (a *ℤ b)) (b *ℤ a) (- (b *ℤ b))) ⟩
  a *ℤ a +ℤ ((- (a *ℤ b) +ℤ b *ℤ a) +ℤ - (b *ℤ b)) ≡⟨ cong (λ x → a *ℤ a +ℤ ((- (a *ℤ b) +ℤ x) +ℤ - (b *ℤ b))) (·Comm b a) ⟩
  a *ℤ a +ℤ ((- (a *ℤ b) +ℤ (a *ℤ b)) +ℤ - (b *ℤ b)) ≡⟨ cong (λ x → a *ℤ a +ℤ (x +ℤ - (b *ℤ b))) (-Cancel' (a *ℤ b)) ⟩
  a *ℤ a +ℤ (0 +ℤ - (b *ℤ b)) ≡⟨ cong (λ x → a *ℤ a +ℤ x) (sym (pos0+ (- (b *ℤ b)))) ⟩
  (a *ℤ a) - (b *ℤ b) ∎

pos∸ : ∀ m n → n ≤ m → pos m - pos n ≡ pos (m ∸ n)
pos∸ zero zero prf = refl
pos∸ zero (suc n) prf = ⊥.rec (¬-<-zero prf)
pos∸ (suc m) zero prf =
  pos (suc m) ≡⟨ pos0+ (pos (suc m)) ⟩
  (- pos zero) +ℤ pos (suc m) ≡⟨ +Comm (- pos zero) (pos (suc m)) ⟩
  pos (suc m) - pos zero ∎
pos∸ (suc m) (suc zero) prf =
  pos (suc m) - pos 1 ∎
pos∸ (suc m) (suc (suc n)) prf =
  predℤ (pos (suc m) +negsuc n) ≡⟨ predℤ+negsuc n (pos (suc m)) ⟩
  predℤ (sucℤ (pos m)) +negsuc n ≡⟨ cong (_+negsuc n) (predSuc (pos m)) ⟩
  pos m - (pos (suc n)) ≡⟨ pos∸ m (suc n) (pred-≤-pred prf) ⟩
  pos (suc m ∸ suc (suc n)) ∎

≤² : ∀ {m n} → m ≤ n → (m * m) ≤ (n * n)
≤² {m} {n} prf =
  ≤-trans (≤-trans (≤-·k {_} {_} {m} prf) (0 , (·-comm n m))) (≤-·k {_} {_} {n} prf)

lemmaSquareDiffℕ : ∀ (a b : ℕ) → b ≤ a → (a + b) * (a ∸ b) ≡ (a * a) ∸ (b * b)
lemmaSquareDiffℕ a b prf =
  injPos
    (pos ((a + b) * (a ∸ b)) ≡⟨ pos·pos (a + b) (a ∸ b) ⟩
    pos (a + b) *ℤ pos (a ∸ b) ≡⟨ cong (_*ℤ pos (a ∸ b)) (pos+ a b) ⟩
    (pos a +ℤ pos b) *ℤ pos (a ∸ b) ≡⟨ cong ((pos a +ℤ pos b) *ℤ_) (sym (pos∸ a b prf)) ⟩
    (pos a +ℤ pos b) *ℤ (pos a - pos b) ≡⟨ lemmaSquareDiff (pos a) (pos b) ⟩
    (pos a *ℤ pos a) - (pos b *ℤ pos b) ≡⟨ cong (λ x → x - (pos b *ℤ pos b)) (sym (pos·pos a a)) ⟩
    (pos (a * a)) - (pos b *ℤ pos b) ≡⟨ cong (λ x → (pos (a * a)) - x) (sym (pos·pos b b)) ⟩
    pos (a * a) - pos (b * b) ≡⟨ pos∸ (a * a) (b * b) (≤² prf) ⟩
    pos ((a * a) ∸ (b * b)) ∎)

isGCDℤ : ℤ → ℤ → ℕ → Type₀
isGCDℤ (pos n) (pos m) = isGCD n m
isGCDℤ (pos n) (negsuc m) = isGCD n (suc m)
isGCDℤ (negsuc n) (pos m) = isGCD (suc n) m
isGCDℤ (negsuc n) (negsuc m) = isGCD (suc n) (suc m)

Squareℕ : ℕ → Type₀
Squareℕ n = Σ[ k ∈ ℕ ] k * k ≡ n

gcdAssoc : ∀ a b c → gcd (gcd a b) c ≡ gcd a (gcd b c)
gcdAssoc a b c =
  let
    (gbc|b , gbc|c) , d|gbc = gcdIsGCD b c
    (gab|a , gab|b) , d|gab = gcdIsGCD a b

    (f|gab , f|c) , d|f = gcdIsGCD (gcd a b) c
    (e|a , e|gbc) , d|e = gcdIsGCD a (gcd b c)

    e|b = ∣-trans e|gbc gbc|b
    e|c = ∣-trans e|gbc gbc|c
    e|gab = d|gab (gcd a (gcd b c)) (e|a , e|b)
    e|f = d|f (gcd a (gcd b c)) (e|gab , e|c)

    f|a = ∣-trans f|gab gab|a
    f|b = ∣-trans f|gab gab|b
    f|gbc = d|gbc (gcd (gcd a b) c) (f|b , f|c)
    f|e = d|e (gcd (gcd a b) c) (f|a , f|gbc)
  in antisym∣ f|e e|f

gcdComm : ∀ a b → gcd a b ≡ gcd b a
gcdComm a b = isGCD→gcd≡ (symGCD (gcdIsGCD b a))

gcd² : ∀ a b → gcd (a * a) (b * b) ≡ (gcd a b) * (gcd a b)
gcd² a b = {!!}

squareCoprimeLemma' : ∀ a b → Squareℕ (b * a) → gcd a b ≡ 1 → Squareℕ a
squareCoprimeLemma' a b (m , sqrPrf) cpPrf =
  gcd a m , sym
    (a ≡⟨ sym (·-identityˡ a) ⟩
    1 * a ≡⟨ cong (_* a) (sym cpPrf) ⟩
    (gcd a b) * a ≡⟨ sym (gcd-factorʳ a b a) ⟩
    gcd (a * a) (b * a) ≡⟨ cong (gcd (a * a)) (sym sqrPrf) ⟩
    gcd (a * a) (m * m) ≡⟨ gcd² a m ⟩
    gcd a m * gcd a m ∎)

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
  (n < m)
  × (a ≡ pos m *ℤ pos m - pos n *ℤ pos n)
  × (b ≡ 2 *ℤ pos m *ℤ pos n)
  × (c ≡ pos m *ℤ pos m +ℤ pos n *ℤ pos n)

reduceToGenerator : ∀ {a b c} → PythTriple a b c → Σ (ℕ × ℕ) (PythTripleGen a b c)
reduceToGenerator (PT a b c prf gcd1 gcd2 aNZ bNZ) =
  let
    lemma1 = -- (b ^ 2) = (c + a)(c - a)
      sym (plusMinus (a *ℤ a) (b *ℤ b))
      ∙ sym (cong (λ x → x - a *ℤ a) (+Comm (a *ℤ a) (b *ℤ b)))
      ∙ cong (λ x → x - a *ℤ a) prf
      ∙ sym (lemmaSquareDiff c a)
    lemma2 =
      cong (λ x → con x (b *ℤ b)) lemma1
  in
    {!!}

{-
fermat4ℤ : (x y z : ℤ) → ¬ x ≡ 0 → ¬ y ≡ 0 → ¬ ((x ^ℤ 4) +ℤ (y ^ℤ 4) ≡ (z ^ℤ 4))
fermat4ℤ x y z px py = {!!}
-}
