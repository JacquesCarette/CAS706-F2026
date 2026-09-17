```agda
{-# OPTIONS --no-keep-pattern-variables #-}
module CAS706.part1.Relations where
```
## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
```
## Defining relations

```agda
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n


_ : 2 ≤ 4
_ = s≤s (s≤s z≤n) -- the obvious proof

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {m = 0} {2} (z≤n {n = 2})) -- with implicits, nameless and by name
```

```agda
+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _
```

```agda
infix 4 _≤_ -- lower than + , no assoc
```

## Inversion

```agda
inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

inv-z≤n′ : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n′ {.zero} z≤n = refl
```

## Properties of ordering relations

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.


## Reflexivity

```agda
≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
```

## Transitivity

```agda
≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
```
-- proof on _evidence_

## Anti-symmetry

```agda
≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)
```

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

## Total

```agda
data Total (m n : ℕ) : Set where
  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n
```

```agda
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n

-- new ingredient needed (with)
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)
```









```agda
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)
```

## Monotonicity

```agda
+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

{-
-- can do directly, or via above
-- chose to do it 'directly', and first pattern-match on
-- m ≤ n, as it gives us most information (and causes + to reduce).
+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
-- for this case, we need to know what 'n' is to know what
-- proof to use, so split on it.
+-monoˡ-≤ .zero zero p z≤n = ≤-refl
-- and now we need to know more about 'p'
+-monoˡ-≤ .zero (suc n) zero z≤n = z≤n
-- and here we get completely, utterly stuck! So...
+-monoˡ-≤ .zero (suc n) (suc p) z≤n = s≤s {!!}
+-monoˡ-≤ .(suc _) .(suc _) p (s≤s m≤n) = s≤s (+-monoˡ-≤ _ _ p m≤n)
-}
-- choose to use commutativity and the above instead
+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n
```

JC doesn't like `rewrite`. So let's set things up to be able to do that.
```agda
≤-refl′ : {m n : ℕ} → m ≡ n → m ≤ n
≤-refl′ refl = ≤-refl

≤-cong₂ : {m n o p : ℕ} → m ≡ o → n ≡ p → m ≤ n → o ≤ p
≤-cong₂ refl refl m≤n = m≤n

+-monoˡ-≤′ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤′ m n p m≤n = ≤-cong₂ (+-comm p m) (+-comm p n) (+-monoʳ-≤ _ _ _ m≤n)
```

```agda
+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = 
  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ _ _ _ p≤q)
```

#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
```agda
infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n
```
#### Exercise `<-trans` (recommended) {#less-trans}
#### Exercise `trichotomy` (practice) {#trichotomy}
#### Exercise `+-mono-<` (practice) {#plus-mono-less}
#### Exercise `≤→<, <→≤` (recommended) {#leq-iff-less}
#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

## Even and odd

Unary relations, predicates.
```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```
Note the overloading of `suc` !

```agda
e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)
```

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}
#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bitstring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:


## Standard library


```agda
import Data.Nat using (_≤_; z≤n; s≤s)
import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                  +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
```
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives](/Connectives/)),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.

## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
