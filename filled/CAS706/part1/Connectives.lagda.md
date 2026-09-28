```agda
module CAS706.part1.Connectives where
```

_Propositions as Types_:

  * _conjunction_ is _product_,
  * _disjunction_ is _sum_,
  * _true_ is _unit type_,
  * _false_ is _empty type_,
  * _implication_ is _function space_.


## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat.Base using (ℕ)
open import Function.Base using (_∘_)

{-# OPTIONS --allow-unsolved-metas #-}
open import CAS706.part1.Isomorphism using (_≃_; _≲_; extensionality; ≃-trans)
open CAS706.part1.Isomorphism.≃-Reasoning
```

## Conjunction is product

```agda
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x
proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , x₁ ⟩ = refl

infixr 2 _×_
```

Alternatively (and actually much better):
```agda
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
```
Because, in part:
```agda
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ _ = refl
```


```agda
data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
```

A "proof" that `Bool × Tri` has 6 members:
```agda
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6
```

```agda
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm ._≃_.to a×b = ⟨ proj₂ a×b , proj₁ a×b ⟩
×-comm ._≃_.from b×a = ⟨ proj₂ b×a , proj₁ b×a ⟩
×-comm ._≃_.from∘to a×b = η-× a×b
×-comm ._≃_.to∘from b×a = η-× b×a

×-comm′ : ∀ {A B : Set} → A ×′ B ≃ B ×′ A
×-comm′ ._≃_.to a×b = ⟨ proj₂′ a×b , proj₁′ a×b ⟩′
×-comm′ ._≃_.from b×a = ⟨ proj₂′ b×a , proj₁′ b×a ⟩′
×-comm′ ._≃_.from∘to a×b = refl
×-comm′ ._≃_.to∘from b×a = refl

```

```agda
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = {!!}

×-assoc′ : ∀ {A B C : Set} → (A ×′ B) ×′ C ≃ A ×′ (B ×′ C)
×-assoc′ = {!!}
```

## Truth is unit

```agda
data ⊤ : Set where  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
```

Alternatively:
```agda
record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl -- not obvious

truth′ : ⊤′
truth′ = _
```

```agda
⊤-count : ⊤ → ℕ
⊤-count tt = 1
```

```agda
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ ._≃_.to ⊤×a = proj₂ ⊤×a
⊤-identityˡ ._≃_.from a = ⟨ tt , a ⟩
⊤-identityˡ ._≃_.from∘to ⟨ tt , a ⟩ = refl
⊤-identityˡ ._≃_.to∘from a = refl
```

```agda
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  (A × ⊤) ≃⟨ ×-comm ⟩
  (⊤ × A) ≃⟨ ⊤-identityˡ ⟩
  A ≃-∎
  -- (A × ⊤) ≃⟨ ×-comm ⟩
  -- (⊤ × A) ≃⟨ ⊤-identityˡ ⟩
  -- A       ≃-∎
```

## Disjunction is sum

```agda
data _⊎_ (A B : Set) : Set where

  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
```
evidence

Eliminator
```agda
case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ x) = g x
```

```agda
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl
```
More generally, we can also throw in an arbitrary function from a disjunction:
```agda
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

infixr 1 _⊎_
```

More counting
```agda
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5
```


## False is empty

```agda
data ⊥ : Set where
  -- no clauses!
```
There is no possible evidence that `⊥` holds.

Dual to `⊤`, for `⊥` there is no introduction rule but an elimination rule.
```agda
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
```

```agda
⊥-count : ⊥ → ℕ
⊥-count ()
```
## Implication is function {#implication}

```agda
→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M
```
Used to be known as _modus ponens_.

λ is introduction, application is elimination.

Elimination followed by introduction is the identity:
```agda
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
```

```agda
→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9
```

Corresponding to the law

    (p ^ n) ^ m  ≡  p ^ (n * m)

we have the isomorphism

    A → (B → C)  ≃  (A × B) → C

```agda
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying ._≃_.to f a×b = f (proj₁ a×b) (proj₂ a×b)
currying ._≃_.from f a b = f ⟨ a , b ⟩
currying ._≃_.from∘to f = refl
currying ._≃_.to∘from f = extensionality λ a×b → cong f (η-× a×b)
-- extensionality λ { ⟨ x , x₁ ⟩ → refl }
```

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have the isomorphism:

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

```agda
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = {!!}
```

Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have the isomorphism:

    A → B × C  ≃  (A → B) × (A → C)

```agda
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = {!!}
```

## Distribution

```agda
×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = {!!}
```

Sums do not distribute over products up to isomorphism, but it is an embedding:
```agda
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = {!!}
```

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```agda
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Bundles using (_⇔_)
```
## Unicode

This chapter uses the following unicode:

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
