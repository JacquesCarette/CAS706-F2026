```agda
module CAS706.part1.Quantifiers where
```

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary.Negation using (¬_)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import CAS706.part1.Isomorphism using (_≃_; extensionality; ∀-extensionality;
  ≃-sym)
open import Function.Base using (_∘_)

-- since we're using copatterns (and the textbook didn't), it is useful to
open _≃_
```

## Universals

```agda
∀-elim : ∀ {A : Set} {B : A → Set} → (L : ∀ (x : A) → B x) → (M : A)
  → B M
∀-elim L M = L M
```

## Existentials

Constructive existential, with evidence:
```agda
record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B proj₁
```
A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
```agda
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) → ∃[ x ] B x
  → C
∃-elim f ⟨ a , Ba ⟩ = f a Ba

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying .to = λ { f ⟨ a , Ba ⟩ → f a Ba }
∀∃-currying .from = λ f a Ba → f ⟨ a , Ba ⟩
∀∃-currying .from∘to = λ f → refl
∀∃-currying .to∘from = λ f → refl
```

## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations](/Relations/):
```agda
open import CAS706.part1.Relations using (even; odd; zero; suc)
```

Equvalence of two obvious ways of defining even/odd:
```agda
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ zero = ⟨ 0 , refl ⟩
even-∃ (suc odd-n) with ⟨ k , k*2+1≡n ⟩ ← odd-∃ odd-n =
  ⟨ suc k , Eq.cong suc k*2+1≡n ⟩

odd-∃ (suc even-n) with ⟨ k , k*2≡n ⟩ ← even-∃ even-n =
  ⟨ k , Eq.cong suc k*2≡n ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ = zero
∃-even ⟨ suc m , refl ⟩ = suc (∃-odd ⟨  m , refl ⟩)

∃-odd ⟨ m , refl ⟩ = suc (∃-even ⟨  m , refl ⟩)
```

## Existentials, Universals, and Negation

We can do this 'directly' but also notice that this is something
we've seen, ∀∃-currying with C = ⊥
```agda
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set} → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = ≃-sym ∀∃-currying
```

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```agda
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
```

## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
