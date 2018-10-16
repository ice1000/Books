{-# OPTIONS --without-K #-}
module Wow-It-is-FV where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Primitive

levelEq : lzero ≡ lzero
levelEq = refl

levelEq′ : lsuc lzero ≡ lsuc lzero
levelEq′ = refl

trans : {l : Level} {Q : Set l} {a b c : Q}
      → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

J : {A : Set} (P : (x y : A) → x ≡ y → Set)
  → ((x : A) → P x x refl)
  → (x y : A) (xy : x ≡ y) → P x y xy
J P p x .x refl = p x

cong : {A B : Set} (f : A → B)
     → {m n : A} → m ≡ n → f m ≡ f n
cong f refl = refl

sym : {A : Set} {m n : A} → m ≡ n → n ≡ m
sym refl = refl

theorem : suc zero + suc zero ≡ _
theorem = refl

theorem′ : 1 + 1 ≡ 2
theorem′ = refl

trivialEq : {a : _} {A : Set a} → A ≡ A
trivialEq = refl

trivialEq′ : ∀ {a} {A : Set a} → A ≡ A
trivialEq′ = refl

trivialEq′′ : ∀ a b → a + b ≡ a + b
trivialEq′′ a b = refl

trans′ : ∀ {a} {A : Set a} (a b c : A)
       → a ≡ b → b ≡ c → a ≡ c
trans′ a .a c refl bc = bc

data _<=_ : (a b : Nat) → Set where
  0ltn : ∀ {n}   → 0 <= n
  nltm : ∀ {n m} → n <= m → suc n <= suc m

7lt13 : 7 <= 13
7lt13 = nltm (nltm (nltm (nltm (nltm (nltm (nltm 0ltn))))))

abc : ∀ {a b c} → a <= b → b <= c → a <= c
abc 0ltn bc = 0ltn
abc (nltm ab) (nltm bc) = nltm (abc ab bc)

data ⊥ : Set where

ridiculous : ⊥ → ⊥
ridiculous a = a

ridiculous′ : 1 ≡ 0 → ⊥
ridiculous′ ()

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

4lt3 : 4 <= 3 → ⊥
4lt3 (nltm (nltm (nltm ())))

infix 3 ¬_
¬_ : ∀ {a} → Set a → Set a
¬ P = P → ⊥

_!=_ : ∀ {a} {A : Set a} → A → A → Set a
x != y = ¬ x ≡ y

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ refl ⟩ c = c

_QED : ∀ {A : Set} (x : A) → x ≡ x
_ QED = refl

lemma₀ : ∀ n → n + 0 ≡ n
lemma₀ zero = refl
lemma₀ (suc n) = cong suc (lemma₀ n)

lemma₁ : ∀ n m → suc (n + m) ≡ n + suc m
lemma₁ zero _ = refl
lemma₁ (suc n) m = cong suc (lemma₁ n m)

comm : ∀ n m → n + m ≡ m + n
comm zero n = sym (lemma₀ n)
comm (suc n) m = suc n + m
  ≡⟨ refl ⟩ suc (n + m)
  ≡⟨ cong suc (comm n m) ⟩ suc (m + n)
  ≡⟨ lemma₁ m n ⟩ m + suc n QED

infixr 2 _≡⟨_⟩_
infix 3 _QED
