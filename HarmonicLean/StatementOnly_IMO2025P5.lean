/-
Alice and Bazza are playing the \emph{inekoalaty game}, a two-player game whose rules depend on a positive real number $\lambda$ which is known to both players. On the $n^\text{th}$ turn of the game (starting with $n=1$) the following happens:
\begin{itemize}
        \item If $n$ is odd, Alice chooses a nonnegative real number $x_n$ such that
        \[ x_1 + x_2 + \dots + x_n \leqslant \lambda n.\]
        \item If $n$ is even, Bazza chooses a nonnegative real number $x_n$ such that
        \[ x_1^2 + x_2^2 + \dots + x_n^2 \leqslant n.\]
\end{itemize}
If a player cannot choose a suitable number $x_n$, the game ends and the other player wins. If the game goes on forever, neither player wins. All chosen numbers are known to both players.

Determine all values of $\lambda$ for which Alice has a winning strategy and all those for which Bazza has a winning strategy.

Answer: Alice wins if $\lambda > 1 / \sqrt{2}$. Bazza wins if $0 < \lambda < 1 / \sqrt{2}$.
-/

import HarmonicLean.Imports

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

noncomputable section

namespace IMO2025P5Statement

/- Alice's strategy: given a tuple of nonnegative reals of even length,
yields the next number. -/
abbrev AliceStrategy : Type := ∀ n, (Fin (2 * n) → NNReal) → NNReal
/- Bazza's strategy: given a tuple of nonnegative reals of odd length,
yields the next number. -/
abbrev BazzaStrategy : Type := ∀ n, (Fin (2 * n + 1) → NNReal) → NNReal

/- The sequence of numbers produced by a couple of strategies. -/
def play (alice : AliceStrategy) (bazza : BazzaStrategy) : ℕ → NNReal
  | n =>
    if n % 2 = 0 then alice (n / 2) fun k ↦ play alice bazza k
    else bazza (n / 2) fun k ↦ play alice bazza k

/-
The predicate saying that `n` move in the sequence `xs 0, xs 1, ...` is valid.
For even values of `n`, it checks that `∑ k ≤ n, xs k ≤ lam * (n + 1)`.
For odd values of `n`, it checks that `∑ k ≤ n, (xs k) ^ 2 ≤ n + 1`.
-/
def ValidMove (lam : ℝ) (xs : ℕ → NNReal) (n : ℕ) : Prop :=
  if Even n then ∑ k ≤ n, xs k ≤ lam * (n + 1)
  else ∑ k ≤ n, (xs k) ^ 2 ≤ n + 1

/-- The predicate saying that a given Alice's strategy is a winning one. -/
def AliceStrategy.Wins (lam : ℝ) (alice : AliceStrategy) : Prop :=
  ∀ bazza, ∃ n, IsLeast {m | ¬ValidMove lam (play alice bazza) m} n ∧ Odd n

/-- The predicate saying that a given Bazza's strategy is a winning one. -/
def BazzaStrategy.Wins (lam : ℝ) (bazza : BazzaStrategy) : Prop :=
  ∀ alice, ∃ n, IsLeast {m | ¬ValidMove lam (play alice bazza) m} n ∧ Even n

theorem main_theorem :
  {lam : ℝ | 0 < lam ∧ ∃ alice : AliceStrategy, alice.Wins lam} = {lam : ℝ | 1 / Real.sqrt 2 < lam} ∧
  {lam : ℝ | 0 < lam ∧ ∃ bazza : BazzaStrategy, bazza.Wins lam} = {lam : ℝ | 0 < lam ∧ lam < 1 / Real.sqrt 2} := by
  sorry
