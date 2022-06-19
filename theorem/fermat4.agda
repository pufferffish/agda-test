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
open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.MoreInts.QuoInt as Z'
  using (ℤ→Int; Int→ℤ)
  renaming (_+_ to _+Z'_)
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
  lemmaQ1 (suc a) prf = {!!}

PythTripleGen : ℕ → ℕ → ℕ → ℕ × ℕ → Type₀
PythTripleGen a b c (m , n) =
  (n < m) × (a ≡ m * m ∸ n * n) × (b ≡ 2 * m * n) × (c ≡ m * m + n * n)

reduceToGenerator : ∀ {a b c} → PythTriple a b c → Σ (ℕ × ℕ) (PythTripleGen a b c)
reduceToGenerator (PT a b c prf gcd1 gcd2 aNZ bNZ) =
  let
    lemma1 =
      pos a *Z pos a +Z pos b *Z pos b ≡⟨ cong (_+Z pos b *Z pos b) (sym (pos·pos a a)) ⟩
      pos (a * a) +Z pos b *Z pos b ≡⟨ cong (pos (a * a) +Z_) (sym (pos·pos b b)) ⟩
      pos (a * a) +Z pos (b * b) ≡⟨ sym (pos+ (a * a) (b * b)) ⟩
      pos (a * a + b * b) ≡⟨ cong pos prf ⟩
      _ ∎
    lemma2 = -- (b ^ 2) = (c + a)(c - a)
      pos·pos b b
      ∙ sym (plusMinus (pos a *Z pos a) (pos b *Z pos b))
      ∙ sym (cong (_- pos a *Z pos a) (+Comm (pos a *Z pos a) (pos b *Z pos b)))
      ∙ cong (_- pos a *Z pos a) lemma1
      ∙ cong (_- pos a *Z pos a) (pos·pos c c)
      ∙ sym (lemmaSquareDiff (pos c) (pos a))
    bb = to+1 (b * b) (x²≠0 bNZ)
    lemma3 = cong (λ x → [ Int→ℤ x / bb ]) lemma2
    test =
      [ Int→ℤ ((pos c +Z pos a) *Z (pos c - pos a)) / bb  ] ≡⟨⟩
      {!!}
  in
    {!!}
{-
fermat4ℤ : (x y z : ℤ) → ¬ x ≡ 0 → ¬ y ≡ 0 → ¬ ((x ^ℤ 4) +ℤ (y ^ℤ 4) ≡ (z ^ℤ 4))
fermat4ℤ x y z px py = {!!}
-}