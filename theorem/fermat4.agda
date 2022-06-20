{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Data.Nat as N renaming (_·_ to _*_)
open import Cubical.Data.Int as Z renaming (_·_ to _*Z_; _+_ to _+Z_)
open import Cubical.HITs.Rationals.QuoQ as Q
  renaming (_·_ to _*Q_; _+_ to _+Q_; -_ to -Q_; _-_ to _-Q_)
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Order
open import Cubical.Data.NatPlusOne
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing.Instances.QuoQ
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRingSolver.Reflection
open import Cubical.Data.Int.MoreInts.QuoInt as Z'
  using (ℤ→Int; Int→ℤ)
  renaming (_+_ to _+Z'_; _·_ to _*Z'_)
open import theorem.lemmas

module theorem.fermat4 where

data PythTriple : ℕ → ℕ → ℕ → Type where
  PT : ∀ a b c {p} →
       ((a * a) N.+ (b * b) ≡ (c * c)) →
       isGCD a b p → isGCD p c 1 →
       ¬ (a ≡ 0) → ¬ (b ≡ 0) →
       PythTriple a b c

to+1 : (a : ℕ) → ¬ (a ≡ 0) → ℕ₊₁
to+1 (suc n) _ = 1+ n
to+1 zero prf = ⊥.rec (prf refl)

private
  lemmaQ1 : ∀ a → (prf : ¬ (a ≡ 0)) → [ Int→ℤ (pos a) / to+1 a prf ] ≡ 1
  lemmaQ1 zero prf = ⊥.rec (prf refl)
  lemmaQ1 (suc a) prf =
    let
      c = to+1 (suc a) prf
    in
      (subst⁻ (λ x → [ Int→ℤ (pos (suc a)) / c ] ≡ [ x *Z' 1 / c ·₊₁ 1 ]) (the (Int→ℤ (pos (suc a)) ≡ ℕ₊₁→ℤ c) refl)
      (subst⁻ (λ x → [ Int→ℤ (pos (suc a)) / c ] ≡ [ (Int→ℤ (pos (suc a))) *Z' 1 / x ]) (·₊₁-identityʳ (to+1 (suc a) prf))
      (subst⁻ (λ x → [ Int→ℤ (pos (suc a)) / c ] ≡ [ x / c ]) (Z'.·-identityʳ (Int→ℤ (pos (suc a)))) refl))) ∙ (ℚ-cancelˡ c)

  mIsPos : ∀ m → Z'.sign (Int→ℤ (pos m)) ≡ Z'.spos
  mIsPos zero = refl
  mIsPos (suc m) = refl

  lemmaZ1' : ∀ a b → Int→ℤ (pos a *Z pos b) ≡ (Int→ℤ (pos a)) *Z' (Int→ℤ (pos b))
  lemmaZ1' a b =
    sym
      (cong (λ x → Z'.signed (x Z'.·S (Z'.sign (Int→ℤ (pos b)))) (a * b)) (mIsPos a)
      ∙ cong (λ x → Z'.signed (Z'.spos Z'.·S x) (a * b)) (mIsPos b)
      ∙ cong Int→ℤ (pos·pos a b))

  lemmaZ1'' : ∀ a b → Int→ℤ (pos (suc a) *Z negsuc b) ≡ (Int→ℤ (pos (suc a))) *Z' (Int→ℤ (negsuc b))
  lemmaZ1'' a b =
    cong Int→ℤ (pos·negsuc (suc a) b) ∙ cong (λ x → Int→ℤ (- x)) (sym (pos·pos (suc a) (suc b)))

  lemmaZ1 : ∀ a b → Int→ℤ (a *Z b) ≡ (Int→ℤ a) *Z' (Int→ℤ b)
  lemmaZ1 (pos a) (pos b) = lemmaZ1' a b
  lemmaZ1 (negsuc a) (negsuc b) =
    Int→ℤ (negsuc a *Z negsuc b) ≡⟨ cong Int→ℤ (negsuc·negsuc a b) ⟩
    Int→ℤ (pos (suc a) *Z pos (suc b)) ≡⟨ lemmaZ1' (suc a) (suc b) ⟩
    (Int→ℤ (negsuc a)) *Z' (Int→ℤ (negsuc b)) ∎
  lemmaZ1 (pos zero) (negsuc _) = Z'.posneg
  lemmaZ1 (negsuc a) (pos zero) =
    Int→ℤ (negsuc a *Z 0) ≡⟨ cong Int→ℤ (·Comm (negsuc a) 0) ⟩
    Z'.signed Z'.spos 0 ≡⟨ Z'.posneg ⟩
    Z'.signed Z'.sneg 0 ≡⟨ cong (Z'.signed Z'.sneg) (0≡m·0 (suc a)) ⟩
    Z'.signed Z'.sneg (suc a * 0) ≡⟨⟩
    (Int→ℤ (negsuc a)) *Z' (Int→ℤ (pos zero)) ∎
  lemmaZ1 (pos (suc a)) (negsuc b) = lemmaZ1'' a b
  lemmaZ1 (negsuc a) (pos (suc b)) =
    Int→ℤ (negsuc a *Z pos (suc b)) ≡⟨ cong Int→ℤ (·Comm (negsuc a) (pos (suc b))) ⟩
    Int→ℤ (pos (suc b) *Z negsuc a) ≡⟨ lemmaZ1'' b a ⟩
    (Int→ℤ (pos (suc b))) *Z' (Int→ℤ (negsuc a)) ≡⟨ Z'.·-comm (Int→ℤ (pos (suc b))) (Int→ℤ (negsuc a)) ⟩
    _ ∎

  -- lemmaQ1 : ∀ a b c d → [ a / b ] *Q [ c / d ] ≡ 1 → [ a / b ] ≡ [ d / c ]

PythTripleGen : ℕ → ℕ → ℕ → ℕ × ℕ → Type₀
PythTripleGen a b c (m , n) =
  (n < m) × (a ≡ m * m ∸ n * n) × (b ≡ 2 * m * n) × (c ≡ m * m + n * n)

reduceToGenerator : ∀ {a b c} → PythTriple a b c → Σ (ℕ × ℕ) (PythTripleGen a b c)
reduceToGenerator (PT a zero c prf gcd1 gcd2 aNZ bNZ) = ⊥.rec (bNZ refl)
reduceToGenerator (PT zero b c prf gcd1 gcd2 aNZ bNZ) = ⊥.rec (aNZ refl)
reduceToGenerator (PT (suc a') (suc b') c prf gcd1 gcd2 aNZ bNZ) =
  let
    a = suc a'
    b = suc b'
    lemma1 =
      pos a *Z pos a +Z pos b *Z pos b ≡⟨ cong (_+Z pos b *Z pos b) (sym (pos·pos a a)) ⟩
      pos (a * a) +Z pos b *Z pos b ≡⟨ cong (pos (a * a) +Z_) (sym (pos·pos b b)) ⟩
      pos (a * a) +Z pos (b * b) ≡⟨ sym (pos+ (a * a) (b * b)) ⟩
      pos (a * a + b * b) ≡⟨ cong pos prf ⟩
      _ ∎
    bb = to+1 (b * b) (x²≠0 bNZ)
    lemma2 =
      the (1 ≡ [ Int→ℤ ((pos c +Z pos a) *Z (pos c - pos a)) / bb ])
      (sym (lemmaQ1 (b * b) (x²≠0 bNZ)) ∙ cong (λ x → [ Int→ℤ x / bb ])
      (pos·pos b b
      ∙ sym (plusMinus (pos a *Z pos a) (pos b *Z pos b))
      ∙ sym (cong (_- pos a *Z pos a) (+Comm (pos a *Z pos a) (pos b *Z pos b)))
      ∙ cong (_- pos a *Z pos a) lemma1
      ∙ cong (_- pos a *Z pos a) (pos·pos c c)
      ∙ sym (lemmaSquareDiff (pos c) (pos a))))
    lemma3 =
      [ Int→ℤ ((pos c +Z pos a) *Z (pos c - pos a)) / bb ] ≡⟨ cong (λ x → [ x / bb ]) (lemmaZ1 (pos c +Z pos a) (pos c - pos a)) ⟩
      [ (Int→ℤ (pos c +Z pos a)) / 1+ b' ] *Q [ (Int→ℤ (pos c - pos a)) / 1+ b' ] ∎
  in
    {!!}
{-
fermat4ℤ : (x y z : ℤ) → ¬ x ≡ 0 → ¬ y ≡ 0 → ¬ ((x ^ℤ 4) +ℤ (y ^ℤ 4) ≡ (z ^ℤ 4))
fermat4ℤ x y z px py = {!!}
-}
