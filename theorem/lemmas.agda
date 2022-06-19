{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Function 
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Rationals.QuoQ.Base
-- open import Cubical.HITs.Rationals.QuoQ.Properties as ℚ
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat renaming (_·_ to _*_)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Int renaming (_·_ to _*ℤ_; _+_ to _+ℤ_)
open import Data.Unit hiding (_≤_)
open import Cubical.Foundations.Transport
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRingSolver.Reflection
open import Cubical.Relation.Nullary.Base
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Data.Sum
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Int.Divisibility
  hiding (∣-zeroˡ)
  renaming (_∣_ to _∣ℤ_; gcdIsGCD to gcdIsGCDℤ; ∣-trans to ∣-transℤ)

module theorem.lemmas where

the : ∀ {ℓ} → (A : Type ℓ) → A → A
the _ x = x

private
  lemma1 : ∀ r s b k n → (r *ℤ b +ℤ s *ℤ k) *ℤ n ≡ b *ℤ (r *ℤ n) +ℤ s *ℤ (k *ℤ n)
  lemma1 = solve ℤCommRing
  
  lemma2 : ∀ r s a b n → b *ℤ (r *ℤ n) +ℤ s *ℤ (a *ℤ b) ≡ b *ℤ (r *ℤ n +ℤ s *ℤ a)
  lemma2 = solve ℤCommRing

  lemma3 : ∀ p q a b → 
           ((b *ℤ p *ℤ p *ℤ q) +ℤ (a *ℤ p *ℤ p *ℤ p) +ℤ (2 *ℤ p *ℤ p *ℤ q *ℤ b)) *ℤ (a *ℤ a) +ℤ (2 *ℤ p *ℤ q *ℤ q *ℤ a +ℤ b *ℤ q *ℤ q *ℤ q +ℤ a *ℤ p *ℤ q *ℤ q) *ℤ (b *ℤ b)
           ≡ (p *ℤ a) *ℤ ((p *ℤ a +ℤ q *ℤ b) *ℤ (p *ℤ a +ℤ q *ℤ b)) +ℤ (q *ℤ b) *ℤ ((p *ℤ a +ℤ q *ℤ b) *ℤ (p *ℤ a +ℤ q *ℤ b))
  lemma3 = solve ℤCommRing

  lemma4 : ∀ r s m n → (- r) *ℤ m +ℤ (- s) *ℤ n ≡ - (r *ℤ m +ℤ s *ℤ n)
  lemma4 = solve ℤCommRing

  lemma5 : ∀ a b → (a + b) ∸ a ≡ b
  lemma5 zero b = refl
  lemma5 (suc a) b = lemma5 a b

  lemma6 : ∀ m → m + m * suc m ≡ (m + m) + (m * m)
  lemma6 m =
    m + m * suc m ≡⟨ cong (m +_) (·-suc m m) ⟩
    m + (m + m * m) ≡⟨ +-assoc m m (m * m) ⟩
    _ ∎

  lemmaSquareDiff : ∀ a b → (a +ℤ b) *ℤ (a - b) ≡ (a *ℤ a) - (b *ℤ b) 
  lemmaSquareDiff = solve ℤCommRing

  rearrangeSqr : ∀ {a b c} → a * b ≡ c → (a * a) * (b * b) ≡ c * c
  rearrangeSqr {a} {b} {c} prf =
    (a * a) * (b * b) ≡⟨ sym (·-assoc a a (b * b)) ⟩
    a * (a * (b * b)) ≡⟨ cong (a *_) (·-assoc a b b) ⟩
    a * ((a * b) * b) ≡⟨ cong (λ x → a * (x * b)) prf ⟩
    a * (c * b) ≡⟨ cong (a *_) (·-comm c b) ⟩
    a * (b * c) ≡⟨ ·-assoc a b c ⟩
    (a * b) * c ≡⟨ cong (_* c) prf ⟩
    c * c ∎

_^ℤ_ : ℤ → ℕ → ℤ
a ^ℤ zero = 1
a ^ℤ (suc n) = a *ℤ (a ^ℤ n) 

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

≤+≤ : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
≤+≤ {a} {b} {c} {d} ( k , prf1 ) ( j , prf2 ) =
  let
    q =
      (k + a) + (j + c) ≡⟨ sym (+-assoc k a (j + c)) ⟩
      k + (a + (j + c)) ≡⟨ cong (k +_) (+-comm a (j + c)) ⟩
      k + ((j + c) + a) ≡⟨ cong (k +_) (sym (+-assoc j c a)) ⟩
      k + (j + (c + a)) ≡⟨ +-assoc k j (c + a) ⟩
      (k + j) + (c + a) ≡⟨ cong ((k + j) +_) (+-comm c a) ⟩
      (k + j) + (a + c) ∎
  in (k + j) , (sym q ∙ cong₂ _+_ prf1 prf2)

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

inj-·sm' : ∀ {k l n} → ¬ (k ≡ 0) → l * k ≡ n * k → l ≡ n
inj-·sm' {k} k≠0 prf with k
... | (suc k') = inj-·sm {_} {k'} prf
... |  zero    = ⊥.rec (k≠0 refl)

inj-sm·' : ∀ {k l n} → ¬ (k ≡ 0) → k * l ≡ k * n → l ≡ n
inj-sm·' {k} k≠0 prf with k
... | (suc k') = inj-sm· {k'} prf
... |  zero    = ⊥.rec (k≠0 refl)

x²≠0 : ∀ {x} → ¬ (x ≡ 0) → ¬ (x * x ≡ 0)
x²≠0 {x} eat prf = eat (inj-sm·' eat (prf ∙ 0≡m·0 x))

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

|bézout| : ∀ {m n} → (t : Bézout m n) → abs (Bézout.gcd t) ≡ 1 → Σ[ t' ∈ Bézout m n ] Bézout.gcd t' ≡ 1
|bézout| {m} {n} t coprime =
  let
    g = Bézout.gcd t
    r = Bézout.coef₁ t
    s = Bézout.coef₂ t
    eq = the (r *ℤ m +ℤ s *ℤ n ≡ g) (Bézout.identity t)
  in
    case abs→⊎ g 1 coprime return (λ _ → Σ[ t' ∈ Bézout m n ] Bézout.gcd t' ≡ 1) of
    λ { (inl prf) → t , prf
      ; (inr prf) → let eq' = lemma4 r s m n ∙ cong -_ (eq ∙ prf)
                    in bezout (- r) (- s) 1 eq' (∣ m , ·Rid _ ∣₁ , ∣ n , ·Rid _ ∣₁) , refl  }

coprimeToBezout : ∀ {m n} → isGCD m n 1 → Σ[ t ∈ Bézout (pos m) (pos n) ] Bézout.gcd t ≡ 1
coprimeToBezout {m} {n} (_ , d|1) =
  let
    bi = bézout (pos m) (pos n)
    eq = Bézout.identity bi
    g = Bézout.gcd bi
    r = Bézout.coef₁ bi
    s = Bézout.coef₂ bi
    (gcd|ℤn , gcd|ℤa) = Bézout.isCD bi
    |gcd|=1 = antisym∣ (d|1 (abs g) (∣→∣ℕ gcd|ℤn , ∣→∣ℕ gcd|ℤa)) (∣-oneˡ (abs g))
  in |bézout| bi |gcd|=1

euclidLemma : ∀ n a b → n ∣ (a * b) → isGCD n a 1 → n ∣ b 
euclidLemma n a b n|ab coprime =
  let
    k , kn≡ab = ∣-untrunc n|ab
    bi , gcd=1 = coprimeToBezout coprime
    eq = Bézout.identity bi
    g = Bézout.gcd bi
    r = Bézout.coef₁ bi
    s = Bézout.coef₂ bi
    poskn≡ab =
      pos k *ℤ pos n ≡⟨ sym (pos·pos k n) ⟩
      pos (k * n) ≡⟨ cong pos kn≡ab ⟩
      pos (a * b) ≡⟨ pos·pos a b ⟩
      pos a *ℤ pos b ∎
    k' = r *ℤ pos b +ℤ s *ℤ pos k
    factor =
      k' *ℤ pos n ≡⟨ lemma1 r s (pos b) (pos k) (pos n) ⟩
      pos b *ℤ (r *ℤ pos n) +ℤ s *ℤ (pos k *ℤ pos n) ≡⟨ cong (λ x → pos b *ℤ (r *ℤ pos n) +ℤ s *ℤ x) poskn≡ab ⟩
      pos b *ℤ (r *ℤ pos n) +ℤ s *ℤ (pos a *ℤ pos b) ≡⟨ lemma2 r s (pos a) (pos b) (pos n) ⟩
      pos b *ℤ (r *ℤ pos n +ℤ s *ℤ pos a) ≡⟨ cong (pos b *ℤ_) eq ⟩
      pos b *ℤ g ≡⟨ cong (pos b *ℤ_) gcd=1 ⟩
      pos b *ℤ 1 ≡⟨ ·Rid (pos b) ⟩
      pos b ∎
  in ∣ abs k' , sym (abs· k' (pos n)) ∙ cong abs factor ∣₁

gcd0≡0 : ∀ m n → isGCD m n 0 → (m ≡ 0) × (n ≡ 0)
gcd0≡0 m n ((0|m , 0|n) , _) = sym (∣-zeroˡ 0|m) , sym (∣-zeroˡ 0|n)

gcd≠0 : ∀ {m n d} → isGCD m (suc n) d → ¬ (d ≡ 0)
gcd≠0 {m} {n} {d} prf d≡0 =
  snotz (snd (gcd0≡0 m (suc n) (subst⁻ (isGCD m (suc n)) (sym d≡0) prf)))

bézout²≡1 : ∀ {a b} → (t : Bézout a b) → Bézout.gcd t ≡ 1 → Σ[ t' ∈ Bézout (a *ℤ a) (b *ℤ b) ] Bézout.gcd t' ≡ 1
bézout²≡1 {a} {b} base coprime =
  let
    p = Bézout.coef₁ base
    q = Bézout.coef₂ base
    pa = p *ℤ a
    qb = q *ℤ b
    eq = Bézout.identity base ∙ coprime
    eq2 = cong₂ _*ℤ_ eq eq
    eqAP = cong (pa *ℤ_) eq2 ∙ ·Rid pa
    eqQB = cong (qb *ℤ_) eq2 ∙ ·Rid qb
    p' = (b *ℤ p *ℤ p *ℤ q) +ℤ (a *ℤ p *ℤ p *ℤ p) +ℤ (2 *ℤ p *ℤ p *ℤ q *ℤ b)
    q' = 2 *ℤ p *ℤ q *ℤ q *ℤ a +ℤ b *ℤ q *ℤ q *ℤ q +ℤ a *ℤ p *ℤ q *ℤ q
  in bezout p' q' 1 (lemma3 p q a b ∙ cong₂ _+ℤ_ eqAP eqQB ∙ eq) (∣ a *ℤ a , ·Rid _ ∣₁ , ∣ b *ℤ b , ·Rid _ ∣₁) , refl

isGCD-cancel : ∀ k {m n d} → ¬ (k ≡ 0) → isGCD (m * k) (n * k) (d * k) → isGCD m n d
isGCD-cancel k k≠0 prf with k
... | (suc k') = isGCD-cancelʳ k' prf
... |  zero    = ⊥.rec (k≠0 refl)

gcd² : ∀ a b → gcd (a * a) (b * b) ≡ (gcd a b) * (gcd a b)
gcd² a 0 =
  gcd (a * a) 0 ≡⟨ isGCD→gcd≡ (zeroGCD (a * a)) ⟩
  a * a ≡⟨ cong (λ x → x * x) (sym (isGCD→gcd≡ (zeroGCD a))) ⟩
  (gcd a 0) * (gcd a 0) ∎
gcd² a (suc b') =
  let
    b = suc b'
    d = gcd a b
    gcdAB = the (isGCD a b d) (gcdIsGCD a b)
    (d|a , d|b) , cf|d = gcdAB
    a' , a'd=a = ∣-untrunc d|a
    b' , b'd=b = ∣-untrunc d|b
    gcdA'B' =
      subst⁻ (isGCD (a' * d) (b' * d)) (·-identityˡ d)
      (subst⁻ (λ x → isGCD (a' * d) x d) b'd=b
      (subst⁻ (λ x → isGCD x b d) a'd=a gcdAB))
    bi , gcd=1 = coprimeToBezout (the (isGCD a' b' 1) (isGCD-cancel d (gcd≠0 gcdAB) gcdA'B'))
    base , gcd2=1 = bézout²≡1 bi gcd=1

    d' = gcd (a' * a') (b' * b')
    (d'|a'2 , d'|b'2) , _ = the (isGCD (a' * a') (b' * b') d') (gcdIsGCD (a' * a') (b' * b'))
    d'|a'2ℤ = subst⁻ (λ x → pos d' ∣ℤ x) (sym (pos·pos a' a')) (∣ℕ→∣ d'|a'2)
    d'|b'2ℤ = subst⁻ (λ x → pos d' ∣ℤ x) (sym (pos·pos b' b')) (∣ℕ→∣ d'|b'2)
    d'=1 = the (d' ≡ 1) (antisym∣ (∣→∣ℕ (gcdIsGCDℤ base d'|a'2ℤ d'|b'2ℤ)) (∣-oneˡ d'))
    gcdA'B'2 = subst⁻ (isGCD (a' * a') (b' * b')) (sym d'=1) (gcdIsGCD (a' * a') (b' * b'))
  in isGCD→gcd≡
     (subst⁻ (isGCD (a * a) (b * b)) (sym (·-identityˡ (d * d)))
     (subst⁻ (λ x → isGCD (a * a) x (1 * (d * d))) (sym (rearrangeSqr {b'} {d} b'd=b))
     (subst⁻ (λ x → isGCD x ((b' * b') * (d * d)) (1 * (d * d))) (sym (rearrangeSqr {a'} {d} a'd=a)) (isGCD-multʳ (d * d) gcdA'B'2))))

squareCoprimeLemma' : ∀ a b → Squareℕ (b * a) → gcd a b ≡ 1 → Squareℕ a
squareCoprimeLemma' a b (m , sqrPrf) cpPrf =
  gcd a m , sym
    (a ≡⟨ sym (·-identityˡ a) ⟩
    1 * a ≡⟨ cong (_* a) (sym cpPrf) ⟩
    (gcd a b) * a ≡⟨ sym (gcd-factorʳ a b a) ⟩
    gcd (a * a) (b * a) ≡⟨ cong (gcd (a * a)) (sym sqrPrf) ⟩
    gcd (a * a) (m * m) ≡⟨ gcd² a m ⟩
    gcd a m * gcd a m ∎)

data PythTriple : ℕ → ℕ → ℕ → Type where
  PT : ∀ a b c {p} →
       ((a * a) + (b * b) ≡ (c * c)) →
       isGCD a b p → isGCD p c 1 →
       ¬ (a ≡ 0) → ¬ (b ≡ 0) →
       PythTriple a b c

to+1 : (a : ℕ) → ¬ (a ≡ 0) → ℕ₊₁
to+1 (suc n) _ = 1+ n
to+1 zero prf = ⊥.rec (prf refl)

PythTripleGen : ℕ → ℕ → ℕ → ℕ × ℕ → Type₀
PythTripleGen a b c (m , n) =
  (n < m) × (a ≡ m * m ∸ n * n) × (b ≡ 2 * m * n) × (c ≡ m * m + n * n)

reduceToGenerator : ∀ {a b c} → PythTriple a b c → Σ (ℕ × ℕ) (PythTripleGen a b c)
reduceToGenerator (PT a b c prf gcd1 gcd2 aNZ bNZ) =
  let
    lemma1 =
      pos a *ℤ pos a +ℤ pos b *ℤ pos b ≡⟨ cong (_+ℤ pos b *ℤ pos b) (sym (pos·pos a a)) ⟩
      pos (a * a) +ℤ pos b *ℤ pos b ≡⟨ cong (pos (a * a) +ℤ_) (sym (pos·pos b b)) ⟩
      pos (a * a) +ℤ pos (b * b) ≡⟨ sym (pos+ (a * a) (b * b)) ⟩
      pos (a * a + b * b) ≡⟨ cong pos prf ⟩
      _ ∎
    lemma2 = -- (b ^ 2) = (c + a)(c - a)
      pos·pos b b
      ∙ sym (plusMinus (pos a *ℤ pos a) (pos b *ℤ pos b))
      ∙ sym (cong (_- pos a *ℤ pos a) (+Comm (pos a *ℤ pos a) (pos b *ℤ pos b)))
      ∙ cong (_- pos a *ℤ pos a) lemma1
      ∙ cong (_- pos a *ℤ pos a) (pos·pos c c)
      ∙ sym (lemmaSquareDiff (pos c) (pos a))
    bb = to+1 (b * b) (x²≠0 bNZ)
  in
    {!!}
{-
fermat4ℤ : (x y z : ℤ) → ¬ x ≡ 0 → ¬ y ≡ 0 → ¬ ((x ^ℤ 4) +ℤ (y ^ℤ 4) ≡ (z ^ℤ 4))
fermat4ℤ x y z px py = {!!}
-}
