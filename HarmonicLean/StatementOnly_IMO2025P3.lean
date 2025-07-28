/-
Let $\mathbb{N}$ denote the set of positive integers.
A function $f\colon\mathbb{N} \to \mathbb{N}$ is said to be \emph{bonza} if
$$ f(a) \ \ \text{divides} \ \ b^a - f(b)^{f(a)} $$
for all positive integers $a$ and $b$.
Determine the smallest real constant $c$ such that
$f(n)\leqslant cn$ for all bonza functions $f$ and all positive integers $n$.
Answer: 4
-/

import HarmonicLean

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

theorem main_theorem (IsBonza : (ℕ+ → ℕ+) → Prop)
  (hisBonza : ∀ f, IsBonza f ↔ ∀ a b : ℕ+, (b : ℕ) ^ (a : ℕ) ≡ (f b : ℕ) ^ (f a : ℕ) [MOD f a]) :
  IsLeast {c : ℝ | ∀ f, IsBonza f → ∀ n : ℕ+, (f n : ℝ) ≤ c * (n : ℝ)} 4 := by
  sorry
