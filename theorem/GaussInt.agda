{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Function 
open import Cubical.Foundations.Prelude
open import Cubical.Data.Int renaming (_·_ to _*ℤ_; _+_ to _+ℤ_; -_ to -ℤ_; _-_ to _-ℤ_)
open import Cubical.Data.Nat hiding (_+_ ; _·_) renaming (isEven to isEvenℕ ; isOdd to isOddℕ)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRingSolver.Reflection
open import Cubical.Algebra.CommRing.Properties

module theorem.GaussInt where

ℤ[i] : Type
ℤ[i] = ℤ × ℤ

i : ℤ[i]
i = (0 , 1)

infix  8 -_
infixl 7 _·_
infixl 6 _+_ _-_

_+_ : ℤ[i] → ℤ[i] → ℤ[i]
(a , b) + (c , d) = (a +ℤ c) , (b +ℤ d)

_·_ : ℤ[i] → ℤ[i] → ℤ[i]
(a , b) · (c , d) = ((a *ℤ c) -ℤ (b *ℤ d)) , ((a *ℤ d) +ℤ (b *ℤ c))

norm : ℤ[i] → ℕ
norm (a , b) = abs (a *ℤ a +ℤ b *ℤ b)

-_ : ℤ[i] → ℤ[i]
- (a , b) = (-ℤ a , -ℤ b)

_-_ : ℤ[i] → ℤ[i] → ℤ[i]
(a , b) - (c , d) = (a -ℤ c) , (b -ℤ d)

instance
  fromNatℤ[i] : HasFromNat ℤ[i]
  fromNatℤ[i] = record { Constraint = λ _ → Unit ; fromNat = λ n → (pos n , 0) }

instance
  fromNegℤ[i] : HasFromNeg ℤ[i]
  fromNegℤ[i] = record { Constraint = λ _ → Unit ; fromNeg = λ n → (neg n , 0) }

discreteℤ[i] : Discrete ℤ[i]
discreteℤ[i] = discreteΣ discreteℤ (λ _ → discreteℤ)

isSetℤ[i] : isSet ℤ[i]
isSetℤ[i] = Discrete→isSet discreteℤ[i]

-involutive : ∀ z → - (- z) ≡ z
-involutive (a , b) = cong₂ _,_ (-Involutive a) (-Involutive b)

-- Additive proofs
+-Comm : ∀ m n → m + n ≡ n + m
+-Comm (a , b) (c , d) = cong₂ _,_ (+Comm a c) (+Comm b d)

+-Assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-Assoc (a , b) (c , d) (e , f) = cong₂ _,_ (+Assoc a c e) (+Assoc b d f)

minusCancel : ∀ m → m - m ≡ 0
minusCancel (a , b) = cong₂ _,_ (-Cancel a) (-Cancel b)

minusCancel' : ∀ m → - m + m ≡ 0
minusCancel' (a , b) = cong₂ _,_ (-Cancel' a) (-Cancel' b)

0+id : ∀ m → m + 0 ≡ m
0+id _ = refl

+0id : ∀ m → 0 + m ≡ m
+0id m = +-Comm 0 m ∙ 0+id m

-- Multiplicative proofs
·-Comm : ∀ m n → m · n ≡ n · m
·-Comm (a , b) (c , d) =
  cong (_, ((a *ℤ d) +ℤ (b *ℤ c))) (cong₂ _-ℤ_ (·Comm a c) (·Comm b d))
  ∙ cong (((c *ℤ a) -ℤ (d *ℤ b)) ,_) (cong₂ _+ℤ_ (·Comm a d) (·Comm b c))
  ∙ cong (((c *ℤ a) -ℤ (d *ℤ b)) ,_) (+Comm (d *ℤ a) (c *ℤ b))

private
  the : ∀ {ℓ} → (A : Type ℓ) → A → A
  the _ x = x

  lemmaAR : ∀ a b c d e f → (a *ℤ c +ℤ -ℤ (b *ℤ d)) *ℤ e +ℤ -ℤ ((a *ℤ d +ℤ b *ℤ c) *ℤ f) ≡ ((a *ℤ ((c *ℤ e) -ℤ (d *ℤ f))) -ℤ (b *ℤ ((c *ℤ f) +ℤ (d *ℤ e))))
  lemmaAR = solve ℤCommRing

  lemmaAI : ∀ a b c d e f → (a *ℤ c +ℤ -ℤ (b *ℤ d)) *ℤ f +ℤ (a *ℤ d +ℤ b *ℤ c) *ℤ e ≡ ((a *ℤ ((c *ℤ f) +ℤ (d *ℤ e))) +ℤ (b *ℤ ((c *ℤ e) -ℤ (d *ℤ f))))
  lemmaAI = solve ℤCommRing

  lemmaDRR : ∀ a b c d e f → (a +ℤ c) *ℤ e +ℤ -ℤ ((b +ℤ d) *ℤ f) ≡ a *ℤ e +ℤ -ℤ (b *ℤ f) +ℤ (c *ℤ e +ℤ -ℤ (d *ℤ f))
  lemmaDRR = solve ℤCommRing

  lemmaDRI : ∀ a b c d e f → (a +ℤ c) *ℤ f +ℤ (b +ℤ d) *ℤ e ≡ a *ℤ f +ℤ b *ℤ e +ℤ (c *ℤ f +ℤ d *ℤ e)
  lemmaDRI = solve ℤCommRing

  lemmaDLR : ∀ a b c d e f → a *ℤ (c +ℤ e) +ℤ -ℤ (b *ℤ (d +ℤ f)) ≡ a *ℤ c +ℤ -ℤ (b *ℤ d) +ℤ (a *ℤ e +ℤ -ℤ (b *ℤ f))
  lemmaDLR = solve ℤCommRing

  lemmaDLI : ∀ a b c d e f → a *ℤ (d +ℤ f) +ℤ b *ℤ (c +ℤ e) ≡ a *ℤ d +ℤ b *ℤ c +ℤ (a *ℤ f +ℤ b *ℤ e)
  lemmaDLI = solve ℤCommRing

·-Assoc : ∀ m n o → m · (n · o) ≡ (m · n) · o
·-Assoc (a , b) (c , d) (e , f) = sym (cong₂ _,_ (lemmaAR a b c d e f) (lemmaAI a b c d e f))

1·id : ∀ m → 1 · m ≡ m
1·id _ = refl

·1id : ∀ m → m · 1 ≡ m
·1id m = ·-Comm m 1 ∙ 1·id m

·+DistR : ∀ m n o → (m + n) · o ≡ m · o + n · o
·+DistR (a , b) (c , d) (e , f) = cong₂ _,_ (lemmaDRR a b c d e f) (lemmaDRI a b c d e f)

·+DistL : ∀ m n o → m · (n + o) ≡ m · n + m · o
·+DistL (a , b) (c , d) (e , f) = cong₂ _,_ (lemmaDLR a b c d e f) (lemmaDLI a b c d e f)

-- Ring instance
open CommRingStr using (0r ; 1r ; isCommRing) renaming (_+_ to _+r_; _·_ to _*r_; -_ to -r_)

ℤ[i]CommRing : CommRing ℓ-zero
fst ℤ[i]CommRing = ℤ[i]
0r (snd ℤ[i]CommRing) = 0
1r (snd ℤ[i]CommRing) = 1
_+r_ (snd ℤ[i]CommRing) = _+_
_*r_ (snd ℤ[i]CommRing) = _·_
-r snd ℤ[i]CommRing = -_
isCommRing (snd ℤ[i]CommRing) = isCommRingℤ[i]
  where abstract
  isCommRingℤ[i] : IsCommRing 0 1 _+_ _·_ (-_)
  isCommRingℤ[i] = makeIsCommRing isSetℤ[i] +-Assoc (λ _ → refl) minusCancel +-Comm ·-Assoc ·1id ·+DistL ·-Comm
