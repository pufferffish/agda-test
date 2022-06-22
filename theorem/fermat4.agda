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
  renaming (_+_ to _+Z'_; _·_ to _*Z'_; -_ to -Z'_)
open import Cubical.Algebra.Field
open import Cubical.Algebra.Field.Instances.QuoQ
open import Cubical.Data.Bool as Bool using (Bool; not; notnot)
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
  lemmaQZCancel : ∀ x → x +Z' (-Z' x) ≡ Z'.pos zero
  lemmaQZCancel (Z'.signed Bool.false zero) = sym (Z'.posneg)
  lemmaQZCancel (Z'.signed Bool.true zero) = refl
  lemmaQZCancel (Z'.signed Bool.false (suc n)) =
    Z'.sucℤ ((Z'.pos n) +Z' (Z'.neg (suc n))) ≡⟨ cong Z'.sucℤ (Z'.+-comm (Z'.pos n) (Z'.neg (suc n))) ⟩
    Z'.sucℤ (Z'.predℤ ((Z'.neg n) +Z' (Z'.pos n))) ≡⟨ Z'.sucPredℤ ((Z'.neg n) +Z' (Z'.pos n)) ⟩
    (Z'.neg n) +Z' (Z'.pos n) ≡⟨ lemmaQZCancel (Z'.neg n) ⟩
    Z'.pos zero ∎
  lemmaQZCancel (Z'.signed Bool.true (suc n)) =
    Z'.predℤ ((Z'.neg n) +Z' (Z'.pos (suc n))) ≡⟨ cong Z'.predℤ (Z'.+-comm (Z'.neg n) (Z'.pos (suc n))) ⟩
    Z'.predℤ (Z'.sucℤ ((Z'.pos n) +Z' (Z'.neg n))) ≡⟨ Z'.predSucℤ (Z'.pos n +Z' Z'.neg n) ⟩
    Z'.pos n +Z' Z'.neg n ≡⟨ lemmaQZCancel (Z'.pos n) ⟩
    Z'.pos zero ∎
  lemmaQZCancel (Z'.posneg i) j = Z'.posneg (~ i ∧ ~ j)

open CommRingStr using (0r ; 1r ; isCommRing) renaming (_+_ to _+r_; _·_ to _*r_; -_ to -r_)

QℤCommRing : CommRing ℓ-zero
fst QℤCommRing = Z'.ℤ
0r (snd QℤCommRing) = 0
1r (snd QℤCommRing) = 1
_+r_ (snd QℤCommRing) = _+Z'_
_*r_ (snd QℤCommRing) = _*Z'_
-r snd QℤCommRing = -Z'_
isCommRing (snd QℤCommRing) = isCommRingQℤ
  where abstract
  isCommRingQℤ : IsCommRing 0 1 _+Z'_ _*Z'_ (-Z'_)
  isCommRingQℤ = makeIsCommRing Z'.isSetℤ Z'.+-assoc Z'.+-identityʳ lemmaQZCancel Z'.+-comm Z'.·-assoc Z'.·-identityʳ (λ x y z → sym (Z'.·-distribˡ x y z)) Z'.·-comm

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

  lemmaQ2 : ∀ a b → [ ℕ₊₁→ℤ a / b ] *Q [ ℕ₊₁→ℤ b / a ] ≡ 1
  lemmaQ2 a b =
    [ ℕ₊₁→ℤ (a ·₊₁ b) / b ·₊₁ a ] ≡⟨ cong (λ x → [ ℕ₊₁→ℤ x / b ·₊₁ a ]) (·₊₁-comm a b)⟩
    [ (ℕ₊₁→ℤ (b ·₊₁ a)) / b ·₊₁ a ] ≡⟨ cong (λ x → [ x / b ·₊₁ a ]) (sym (Z'.·-identityʳ (ℕ₊₁→ℤ (b ·₊₁ a))))⟩
    [ (ℕ₊₁→ℤ (b ·₊₁ a)) *Z' 1 / b ·₊₁ a ] ≡⟨ cong (λ x → [ (ℕ₊₁→ℤ (b ·₊₁ a)) *Z' 1 / x ]) (sym (·₊₁-identityʳ (b ·₊₁ a))) ⟩
    [ (ℕ₊₁→ℤ (b ·₊₁ a)) *Z' 1 / (b ·₊₁ a) ·₊₁ 1 ] ≡⟨ ℚ-cancelˡ (b ·₊₁ a) ⟩
    1 ∎

  lemmaQ3 : ∀ {a b c d} → [ a / b ] *Q [ ℕ₊₁→ℤ c / d ] ≡ 1 → [ a / b ] ≡ [ ℕ₊₁→ℤ d / c ]
  lemmaQ3 {a} {b} {c} {d} prf =
    cong (λ (x , _) → x)
    (Units.inverseUniqueness ℚCommRing [ ℕ₊₁→ℤ c / d ] ([ a / b ] , Q.·-comm [ ℕ₊₁→ℤ c / d ] [ a / b ] ∙ prf) ([ ℕ₊₁→ℤ d / c ] , lemmaQ2 c d))

  lemmaQ4 : ∀ a b c → [ a / b ] +Q [ c / b ] ≡ [ a +Z' c / b ]
  lemmaQ4 a b c =
    [ (a *Z' ℕ₊₁→ℤ b) +Z' (c *Z' ℕ₊₁→ℤ b) / b ·₊₁ b ] ≡⟨ cong (λ x → [ x / b ·₊₁ b ]) (Z'.·-distribʳ a c (ℕ₊₁→ℤ b)) ⟩
    [ (a +Z' c) *Z' ℕ₊₁→ℤ b / b ·₊₁ b ] ≡⟨ ℚ-cancelʳ b ⟩
    [ a +Z' c / b ] ∎

  lemmaZ2' : ∀ a b → pos a - pos b ≡ pos (suc a) - pos (suc b)
  lemmaZ2' a b = sym (pos- a b) ∙ pos- (suc a) (suc b)

  lemmaZ2 : ∀ a b → (Int→ℤ (pos a)) +Z' (-Z' (Int→ℤ (pos b))) ≡ Int→ℤ (pos a - pos b)
  lemmaZ2 zero zero = sym Z'.posneg
  lemmaZ2 zero (suc b) = cong Int→ℤ (pos0+ (negsuc b))
  lemmaZ2 (suc a) zero = Z'.+-zeroʳ Z'.sneg (Z'.pos (suc a))
  lemmaZ2 (suc a) (suc b) =
    Z'.sucℤ ((Z'.pos a) +Z' (Z'.neg (suc b))) ≡⟨ Z'.sucℤ-+ʳ (Z'.pos a) (Z'.neg (suc b)) ⟩
    (Z'.pos a) +Z' (Z'.neg b) ≡⟨ lemmaZ2 a b ⟩
    Int→ℤ (pos a - pos b) ≡⟨ cong Int→ℤ (lemmaZ2' a b) ⟩
    _ ∎

  lemmaZ3 : ∀ a b → Int→ℤ (pos a) +Z' Int→ℤ (pos b) ≡ Z'.pos (a + b)
  lemmaZ3 zero b = refl
  lemmaZ3 (suc a) b = cong Z'.sucℤ (lemmaZ3 a b)

  lemmaZ4 : ∀ c a → (c +Z' a) +Z' (c +Z' (-Z' a)) ≡ c +Z' c
  lemmaZ4 = solve QℤCommRing

  lemmaZ5 : ∀ a → 2 *Z' a ≡ a +Z' a
  lemmaZ5 a =
    (1 +Z' 1) *Z' a ≡⟨ sym (Z'.·-distribʳ 1 1 a) ⟩
    (1 *Z' a +Z' 1 *Z' a) ≡⟨ cong (λ x → x +Z' x) (Z'.·-identityˡ a) ⟩
    a +Z' a ∎

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
    lemma2' =
      Int→ℤ (pos c +Z pos a) ≡⟨⟩
      Int→ℤ (pos c +Z pos a) ≡⟨ cong Int→ℤ (sym (pos+ c a)) ⟩
      Z'.pos (c + suc a') ≡⟨ cong Z'.pos (+-suc c a') ⟩
      Z'.pos (suc (c + a')) ≡⟨⟩
      ℕ₊₁→ℤ (1+ (c + a')) ∎
    lemma2 =
      the ([ (Int→ℤ (pos c - pos a)) / 1+ b' ] *Q [ (Int→ℤ (pos c +Z pos a)) / 1+ b' ] ≡ 1)
      ((Q.·-comm [ (Int→ℤ (pos c - pos a)) / 1+ b' ] [ (Int→ℤ (pos c +Z pos a)) / 1+ b' ]) ∙ sym
      ((sym (lemmaQ1 (b * b) (x²≠0 bNZ)) ∙ cong (λ x → [ Int→ℤ x / bb ])
      (pos·pos b b
      ∙ sym (plusMinus (pos a *Z pos a) (pos b *Z pos b))
      ∙ sym (cong (_- pos a *Z pos a) (+Comm (pos a *Z pos a) (pos b *Z pos b)))
      ∙ cong (_- pos a *Z pos a) lemma1
      ∙ cong (_- pos a *Z pos a) (pos·pos c c)
      ∙ sym (lemmaSquareDiff (pos c) (pos a)))
      ∙ cong (λ x → [ x / bb ]) (lemmaZ1 (pos c +Z pos a) (pos c - pos a)))))
    lemma4 =
      lemmaQ3 {Int→ℤ (pos c - pos a)} {1+ b'}
      (cong (λ x → [ (Int→ℤ (pos c - pos a)) / 1+ b' ] *Q [ x / 1+ b' ]) (sym lemma2') ∙ lemma2)
    n/m = [ (Int→ℤ (pos c - pos a)) / 1+ b' ]
    m/n = [ ℕ₊₁→ℤ (1+ (c + a')) / 1+ b' ]
    2c/b =
      m/n +Q n/m ≡⟨ lemmaQ4 (ℕ₊₁→ℤ (1+ (c + a'))) (1+ b') (Int→ℤ (pos c - pos a)) ⟩
      [ (Z'.pos (suc (c + a'))) +Z' (Int→ℤ (pos c - pos a)) / 1+ b' ] ≡⟨ cong (λ x → [ (Z'.pos x) +Z' (Int→ℤ (pos c - pos a)) / 1+ b' ]) (sym (+-suc c a')) ⟩
      [ (Z'.pos (c + a)) +Z' (Int→ℤ (pos c - pos a)) / 1+ b' ] ≡⟨ cong (λ x → [ (Z'.pos (c + a)) +Z' x / 1+ b' ]) (sym (lemmaZ2 c a)) ⟩
      [ (Z'.pos (c + a)) +Z' ((Int→ℤ (pos c)) +Z' (-Z' (Int→ℤ (pos a)))) / 1+ b' ] ≡⟨ cong (λ x → [ x +Z' ((Int→ℤ (pos c)) +Z' (-Z' (Int→ℤ (pos a)))) / 1+ b' ]) (sym (lemmaZ3 c a)) ⟩
      [ (Int→ℤ (pos c) +Z' Int→ℤ (pos a)) +Z' ((Int→ℤ (pos c)) +Z' (-Z' (Int→ℤ (pos a)))) / 1+ b' ] ≡⟨ cong (λ x → [ x / 1+ b' ]) (lemmaZ4 (Int→ℤ (pos c)) (Int→ℤ (pos a))) ⟩
      [ Int→ℤ (pos c) +Z' Int→ℤ (pos c) / 1+ b' ] ≡⟨ cong (λ x → [ x / 1+ b' ]) (sym (lemmaZ5 (Int→ℤ (pos c)))) ⟩
      [ 2 *Z' Int→ℤ (pos c) / 1+ b' ] ≡⟨ cong (λ x → [ 2 *Z' Int→ℤ (pos c) / x ]) (sym (·₊₁-identityˡ (1+ b'))) ⟩
      2 *Q [ Int→ℤ (pos c) / 1+ b' ] ∎
    2a/b =
      m/n -Q n/m ≡⟨ {!!} ⟩
      2 *Q [ Z'.pos a / 1+ b' ] ∎
  in
    {!!}
{-
fermat4ℤ : (x y z : ℤ) → ¬ x ≡ 0 → ¬ y ≡ 0 → ¬ ((x ^ℤ 4) +ℤ (y ^ℤ 4) ≡ (z ^ℤ 4))
fermat4ℤ x y z px py = {!!}
-}
