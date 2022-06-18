{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Function 
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Rationals.HITQ
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat renaming (_·_ to _*_)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Int renaming (_·_ to _*ℤ_; _+_ to _+ℤ_)
open import Data.Unit hiding (_≤_)
open import Cubical.Foundations.Transport
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Relation.Nullary.Base
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Data.Sum
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Divisibility
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Int.Divisibility
  hiding (∣-zeroˡ)
  renaming (_∣_ to _∣ℤ_; gcdIsGCD to gcdIsGCDℤ; ∣-trans to ∣-transℤ)

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

rearrange¹· : {T : Type}
              → (_·_ : T → T → T)
              → (∀ x y → x · y ≡ y · x)
              → (∀ x y z → x · (y · z) ≡ (x · y) · z)
              → ∀ (a b c : T)
              → a · (b · c) ≡ c · (b · a)
rearrange¹· _·_ comm assoc a b c =
  a · (b · c) ≡⟨ cong (a ·_) (comm b c) ⟩
  a · (c · b) ≡⟨ comm a (c · b) ⟩
  (c · b) · a ≡⟨ sym (assoc c b a) ⟩
  c · (b · a) ∎

rearrange²· : {T : Type}
              → (_·_ : T → T → T)
              → (∀ x y → x · y ≡ y · x)
              → (∀ x y z → x · (y · z) ≡ (x · y) · z)
              → ∀ (a b c : T)
              → a · (b · c) ≡ b · (c · a)
rearrange²· _·_ comm assoc a b c =
  a · (b · c) ≡⟨ cong (a ·_) (comm b c) ⟩
  a · (c · b) ≡⟨ assoc a c b ⟩
  (a · c) · b ≡⟨ cong (_· b) (comm a c) ⟩
  (c · a) · b ≡⟨ comm (c · a) b ⟩
  b · (c · a) ∎

rearrange³· : {T : Type}
              → (_·_ : T → T → T)
              → (∀ x y → x · y ≡ y · x)
              → (∀ x y z → x · (y · z) ≡ (x · y) · z)
              → ∀ (a b : T)
              → (a · b) · (a · b) ≡ (b · b) · (a · a)
rearrange³· _·_ comm assoc a b =
  (a · b) · (a · b) ≡⟨ sym (assoc a b (a · b)) ⟩
  a · (b · (a · b)) ≡⟨ cong (λ x → a · (b · x)) (comm a b) ⟩
  a · (b · (b · a)) ≡⟨ cong (a ·_) (assoc b b a) ⟩
  a · ((b · b) · a) ≡⟨ comm a ((b · b) · a) ⟩
  ((b · b) · a) · a ≡⟨ sym (assoc (b · b) a a) ⟩
  (b · b) · (a · a) ∎

rearrange¹ℤ* : ∀ a b c → a *ℤ (b *ℤ c) ≡ c *ℤ (b *ℤ a)
rearrange¹ℤ* = rearrange¹· _*ℤ_ ·Comm ·Assoc 

rearrange²ℤ* : ∀ a b c → a *ℤ (b *ℤ c) ≡ b *ℤ (c *ℤ a)
rearrange²ℤ* = rearrange²· _*ℤ_ ·Comm ·Assoc

rearrange¹ℕ* : ∀ a b c → a * (b * c) ≡ c * (b * a)
rearrange¹ℕ* = rearrange¹· _*_ ·-comm ·-assoc 

rearrange²ℕ* : ∀ a b c → a * (b * c) ≡ b * (c * a)
rearrange²ℕ* = rearrange²· _*_ ·-comm ·-assoc

rearrange³ℕ* : ∀ a b → (a * b) * (a * b) ≡ (b * b) * (a * a)
rearrange³ℕ* = rearrange³· _*_ ·-comm ·-assoc

euclidLemma : ∀ n a b → n ∣ (a * b) → isGCD n a 1 → n ∣ b 
euclidLemma n a b n|ab (_ , d|1) =
  let
    k , kn≡ab = ∣-untrunc n|ab
    bi = bézout (pos n) (pos a)
    eq = Bézout.identity bi
    g = Bézout.gcd bi
    r = Bézout.coef₁ bi
    s = Bézout.coef₂ bi
    (gcd|ℤn , gcd|ℤa) = Bézout.isCD bi
    gcd≡±1 = abs→⊎ g 1 (antisym∣ (d|1 (abs g) (∣→∣ℕ gcd|ℤn , ∣→∣ℕ gcd|ℤa)) (∣-oneˡ (abs g)))
    poskn≡ab =
      pos k *ℤ pos n ≡⟨ sym (pos·pos k n) ⟩
      pos (k * n) ≡⟨ cong pos kn≡ab ⟩
      pos (a * b) ≡⟨ pos·pos a b ⟩
      pos a *ℤ pos b ∎
    k' = r *ℤ pos b +ℤ s *ℤ pos k
    factor± =
      k' *ℤ pos n ≡⟨ ·Comm k' (pos n) ⟩
      pos n *ℤ k' ≡⟨ ·DistR+ (pos n) (r *ℤ pos b) (s *ℤ pos k) ⟩
      pos n *ℤ (r *ℤ pos b) +ℤ pos n *ℤ (s *ℤ pos k) ≡⟨ cong (_+ℤ pos n *ℤ (s *ℤ pos k)) (rearrange¹ℤ* (pos n) r (pos b)) ⟩
      pos b *ℤ (r *ℤ pos n) +ℤ pos n *ℤ (s *ℤ pos k) ≡⟨ cong (pos b *ℤ (r *ℤ pos n) +ℤ_) (rearrange²ℤ* (pos n) s (pos k)) ⟩
      pos b *ℤ (r *ℤ pos n) +ℤ s *ℤ (pos k *ℤ pos n) ≡⟨ cong (λ x → pos b *ℤ (r *ℤ pos n) +ℤ s *ℤ x) poskn≡ab ⟩
      pos b *ℤ (r *ℤ pos n) +ℤ s *ℤ (pos a *ℤ pos b) ≡⟨ cong (pos b *ℤ (r *ℤ pos n) +ℤ_) (rearrange¹ℤ* s (pos a) (pos b)) ⟩
      pos b *ℤ (r *ℤ pos n) +ℤ pos b *ℤ (pos a *ℤ s) ≡⟨ cong (λ x → pos b *ℤ (r *ℤ pos n) +ℤ pos b *ℤ x) (·Comm (pos a) s) ⟩
      pos b *ℤ (r *ℤ pos n) +ℤ pos b *ℤ (s *ℤ pos a) ≡⟨ sym (·DistR+ (pos b) (r *ℤ (pos n)) (s *ℤ (pos a))) ⟩
      pos b *ℤ (r *ℤ pos n +ℤ s *ℤ pos a) ≡⟨ cong (pos b *ℤ_) eq ⟩
      pos b *ℤ g ∎
    factor = ⊎→abs _ b (case gcd≡±1 return (λ _ → (k' *ℤ pos n ≡ pos b) ⊎ (k' *ℤ pos n ≡ - (pos b))) of
      λ { (inl prf) → inl
            (k' *ℤ pos n ≡⟨ factor± ⟩
            pos b *ℤ g ≡⟨ cong (pos b *ℤ_) prf ⟩
            pos b *ℤ 1 ≡⟨ ·Rid (pos b) ⟩
            pos b ∎)
        ; (inr prf) → inr
            (k' *ℤ pos n ≡⟨ factor± ⟩
            pos b *ℤ g ≡⟨ cong (pos b *ℤ_) prf ⟩
            pos b *ℤ negsuc 0 ≡⟨ pos·negsuc b 0 ⟩
            - (pos b *ℤ 1) ≡⟨ cong (-_) (·Rid (pos b)) ⟩
            - (pos b) ∎) })
  in ∣ abs k' , sym (abs· k' (pos n)) ∙ factor ∣₁

gcd0≡0 : ∀ m n → isGCD m n 0 → (m ≡ 0) × (n ≡ 0)
gcd0≡0 m n ((0|m , 0|n) , _) = sym (∣-zeroˡ 0|m) , sym (∣-zeroˡ 0|n)

gcd≠0 : ∀ {m n d} → isGCD m (suc n) d → ¬ (d ≡ 0)
gcd≠0 {m} {n} {d} prf d≡0 =
  snotz (snd (gcd0≡0 m (suc n) (subst⁻ (isGCD m (suc n)) (sym d≡0) prf)))

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

the : ∀ {ℓ} → (A : Type ℓ) → A → A
the _ x = x

gcd² : ∀ a b → gcd (a * a) (b * b) ≡ (gcd a b) * (gcd a b)
gcd² a 0 =
  gcd (a * a) (0 * 0) ≡⟨⟩
  gcd (a * a) 0 ≡⟨ isGCD→gcd≡ (zeroGCD (a * a)) ⟩
  a * a ≡⟨ cong (λ x → x * x) (sym (isGCD→gcd≡ (zeroGCD a))) ⟩
  (gcd a 0) * (gcd a 0) ∎
gcd² a (suc b') =
  let
    b = suc b'
    gcdAB = gcd a b
    gcdAB2 = gcd (a * a) (b * b)
    gcdAB²≠0 = x²≠0 (gcd≠0 (gcdIsGCD a b))
    gcdAB2≠0 = gcd≠0 (gcdIsGCD (a * a) (b * b))
    (gcd1|a , gcd1|b) , d|gcd1 = gcdIsGCD a b
    (gcd2|a , gcd2|b) , d|gcd2 = gcdIsGCD (a * a) (b * b)
    r , eqa1 = ∣-untrunc gcd1|a
    s , eqb1 = ∣-untrunc gcd1|b
    p , eqa2 = ∣-untrunc gcd2|a
    q , eqb2 = ∣-untrunc gcd2|b
    eqn1 =
      a * (a * (b * b)) ≡⟨ cong (λ x → a * (a * x)) (sym eqb2) ⟩
      a * (a * (q * gcdAB2)) ≡⟨ cong (λ x → x * (x * (q * gcdAB2))) (sym eqa1) ⟩
      (r * gcdAB) * ((r * gcdAB) * (q * gcdAB2)) ≡⟨ ·-assoc (r * gcdAB) (r * gcdAB) (q * gcdAB2) ⟩
      ((r * gcdAB) * (r * gcdAB)) * (q * gcdAB2) ≡⟨ cong (_* (q * gcdAB2)) (rearrange³ℕ* r gcdAB) ⟩
      (gcdAB * gcdAB) * (r * r) * (q * gcdAB2) ≡⟨ sym (·-assoc (gcdAB * gcdAB) (r * r) (q * gcdAB2))  ⟩
      (gcdAB * gcdAB) * ((r * r) * (q * gcdAB2)) ∎
    eqn2 =
      a * (a * (b * b)) ≡⟨ ·-assoc a a (b * b) ⟩
      (a * a) * (b * b) ≡⟨ cong (_* (b * b)) (sym eqa2) ⟩
      (p * gcdAB2) * (b * b) ≡⟨ cong (λ x → (p * gcdAB2) * (x * x)) (sym eqb1) ⟩
      (p * gcdAB2) * ((s * gcdAB) * (s * gcdAB)) ≡⟨ cong ((p * gcdAB2) *_) (rearrange³ℕ* s gcdAB) ⟩
      (p * gcdAB2) * ((gcdAB * gcdAB) * (s * s)) ≡⟨ ·-comm (p * gcdAB2) ((gcdAB * gcdAB) * (s * s)) ⟩
      (gcdAB * gcdAB) * (s * s) * (p * gcdAB2) ≡⟨ sym (·-assoc (gcdAB * gcdAB) (s * s) (p * gcdAB2)) ⟩
      (gcdAB * gcdAB) * ((s * s) * (p * gcdAB2)) ∎
    eqn3 =
      (r * r) * (q * gcdAB2) ≡⟨ inj-sm·' gcdAB²≠0 (sym eqn1 ∙ eqn2) ⟩
      (s * s) * (p * gcdAB2) ≡⟨ ·-assoc (s * s) p gcdAB2 ⟩
      ((s * s) * p) * gcdAB2 ∎
    eqn4 =
      (r * r) * (q * gcdAB2) ≡⟨ ·-assoc (r * r) q gcdAB2 ⟩
      ((r * r) * q) * gcdAB2 ∎
    eqn5 = the ((s * s) * p ≡ (r * r) * q) (inj-·sm' gcdAB2≠0 (sym eqn3 ∙ eqn4))
  in {!!}

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
