/-
Consider a 2025×2025 grid of unit squares. Matilda wishes to place on the grid some rectangular
tiles, possibly of different sizes, such that each side of every tile lies on a grid line and
every unit square is covered by at most one tile.

Determine the minimum number of tiles Matilda needs to place so that each row and each column
of the grid has exactly one unit square that is not covered by any tile.
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

namespace IMO2025P6Statement

noncomputable def _ANSWER_ : ℕ := sorry

theorem problem_IMO_2025_P6
    (GoodCover : Set (Finset (NonemptyInterval (Fin 2025 × Fin 2025))))
    (hGoodCover : ∀ S, S ∈ GoodCover ↔
      Set.PairwiseDisjoint S.toSet SetLike.coe ∧
        (∀ i, ∃! j, (i, j) ∉ ⋃ t ∈ S, (t : Set (Fin 2025 × Fin 2025))) ∧
        (∀ j, ∃! i, (i, j) ∉ ⋃ t ∈ S, (t : Set (Fin 2025 × Fin 2025)))) :
    IsLeast (Finset.card '' GoodCover) _ANSWER_ := by
  sorry
