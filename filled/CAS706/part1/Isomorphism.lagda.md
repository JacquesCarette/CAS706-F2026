```agda
module CAS706.part1.Isomorphism where
```

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

open import Level
```

## "variables"
JC: not in PLFA, but some of this is tedious, so now's a good time

```agda
private
  variable
    ℓ : Level
    A B C : Set ℓ
```

## Function composition

```agda
_∘_ : (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

_∘′_ : (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)
```

## Extensionality {#extensionality}

```agda
postulate
  extensionality : {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

Split on n instead:
```agda
_+′_ : ℕ → ℕ → ℕ
m +′ ℕ.zero = m
m +′ ℕ.suc n = ℕ.suc (m +′ n)
```

```agda
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n =
  m +′ n ≡⟨ helper m n ⟩
  n + m  ≡⟨ +-comm n m ⟩
  m + n  ∎
  where
    helper : ∀ m n → m +′ n ≡ n + m
    helper m ℕ.zero = refl
    helper m (ℕ.suc n) = cong ℕ.suc (helper m n)
```
But what about:
```agda
same : _+′_ ≡ _+_
same = extensionality λ m → extensionality λ n → same-app m n
```

```agda
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
```

## Isomorphism

```agda
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  constructor mk-≃ -- not in PLFA
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
```

Almost the same as, but records are *way* more convenient:
```agda
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g
```

## Isomorphism is an equivalence

```agda
≃-refl : A ≃ A
≃-refl = mk-≃ (λ x → x) (λ x → x) (λ _ → refl) (λ _ → refl)

≃-refl' : A ≃ A
≃-refl' = record
  { to = λ x → x
  ; from = λ x → x
  ; to∘from = λ _ → refl
  ; from∘to = λ _ → refl
  }

≃-refl'' : A ≃ A
≃-refl'' .to x = x
≃-refl'' .from x = x
≃-refl'' .from∘to _ = refl
≃-refl'' .to∘from _ = refl
```
(show as record and with constructor and with copatterns)

```agda
≃-sym : A ≃ B → B ≃ A
≃-sym A≃B .to = A≃B .from
≃-sym A≃B .from = A≃B .to
≃-sym A≃B .from∘to x = A≃B .to∘from x
≃-sym A≃B .to∘from x = A≃B .from∘to x
```

To show isomorphism is transitive, we compose the `to` and `from`
functions, and use equational reasoning to combine the inverses:
```agda
≃-trans : A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C .to a = B≃C .to (A≃B .to a)
≃-trans A≃B B≃C .from c = A≃B .from (B≃C .from c)
≃-trans A≃B B≃C .from∘to a =
  A≃B .from (B≃C .from (B≃C .to (A≃B .to a))) ≡⟨ cong (A≃B .from) (B≃C .from∘to (A≃B .to a)) ⟩
  A≃B .from (A≃B .to a)                       ≡⟨ A≃B .from∘to a ⟩
  a ∎
≃-trans A≃B B≃C .to∘from c =
  B≃C .to (A≃B .to (A≃B .from (B≃C .from c))) ≡⟨ cong (B≃C .to) (A≃B .to∘from (B≃C .from c)) ⟩
  B≃C .to (B≃C .from c)                       ≡⟨ B≃C .to∘from c ⟩
  c                                           ∎
```

## Equational reasoning for isomorphism

```agda
module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : (A : Set) → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  _ ≃-∎ = ≃-refl

open ≃-Reasoning
```

## Embedding

```agda
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl = {!!} -- copatterns

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C = {!!}
```

It is also easy to see that if two types embed in each other, and the
embedding functions correspond, then they are isomorphic.  This is a
weak form of anti-symmetry:
```agda
≲-antisym :(A≲B : A ≲ B) → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A) → (from A≲B ≡ to B≲A)
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to .to = A≲B .to
≲-antisym A≲B B≲A to≡from from≡to .from = A≲B .from
≲-antisym A≲B B≲A to≡from from≡to .from∘to = A≲B .from∘to
≲-antisym {A = A} {B = B} A≲B B≲A to≡from from≡to .to∘from b =
  A≲B .to (A≲B .from b)     ≡⟨ cong (λ f → f (A≲B .from b)) to≡from ⟩
  B≲A .from ((A≲B .from) b) ≡⟨ cong (λ f → B≲A .from (f b)) from≡to ⟩
  B≲A .from ((B≲A .to) b)   ≡⟨ B≲A .from∘to b ⟩
  b ∎
```

## Equational reasoning for embedding

```agda
module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : A ≲ B  → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set) → A ≲ A
  _ ≲-∎ = ≲-refl

open ≲-Reasoning
```

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```agda
import Function.Base using (_∘_)
import Function.Bundles using (_↔_; _↩_)
```
The standard library `_↔_` and `_↩_` correspond to our `_≃_` and
`_≲_`, respectively, but those in the standard library are less
more general (i.e. less convenient).

## Unicode

    ∘  U+2218  RING OPERATOR (\o, \circ, \comp)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\lambda, \Gl)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~-)
    ≲  U+2272  LESS-THAN OR EQUIVALENT TO (\<~)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)
