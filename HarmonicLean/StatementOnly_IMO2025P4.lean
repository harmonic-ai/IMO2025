/-
A proper divisor of a positive integer $N$ is a positive divisor of $N$ other than $N$ itself.
The infinite sequence $a_1,a_2,\dots$ consists of positive integers, each of which has at least three proper divisors.
For each $n\geqslant 1$, the integer $a_{n+1}$ is the sum of the three largest proper divisors of $a_n$.
Determine all possible values of $a_1$.
Answer: All integers of the form $6 \cdot 12^a \cdot m$, for $a \geq 0$ and $m$ is coprime to 10.
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option linter.all false

theorem main_theorem :
    { a₁ | ∃ a : ℕ → ℕ,
      (∀ n, 0 < a n) ∧
      (∀ n, 3 ≤ (a n).properDivisors.card) ∧
      (∀ n, a (n+1) =
        ((a n).properDivisors.sort (· ≥ ·))[0]! +
        ((a n).properDivisors.sort (· ≥ ·))[1]! +
        ((a n).properDivisors.sort (· ≥ ·))[2]!) ∧
      a₁ = a 0
    } = { n | ∃ a m, m.Coprime 10 ∧ n = 6 * 12 ^ a * m } := by
      sorry
