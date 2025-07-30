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

namespace IMO2025P5

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

/-
For a sequence of moves $x_1, x_2, \dots$ in the inekoalaty game, we define the partial sum of values $S_n = \sum_{i=1}^n x_i$ and the partial sum of squares $Q_n = \sum_{i=1}^n x_i^2$. We adopt the convention that $S_0=0$ and $Q_0=0$.
-/
def s (xs : ℕ → NNReal) (n : ℕ) : ℝ := ∑ i in Finset.range n, (xs i : ℝ)
def q (xs : ℕ → NNReal) (n : ℕ) : ℝ := ∑ i in Finset.range n, (xs i : ℝ) ^ 2

/-
Bazza's reference strategy is as follows: on his turn $2k$, if he has not already lost (i.e., if $Q_{2k-1} \le 2k$), he chooses $x_{2k} = \sqrt{2k - Q_{2k-1}}$.
-/
def bazzaReferenceStrategy : BazzaStrategy := fun n hist ↦
  let Q_2n_plus_1 := ∑ i, (hist i : ℝ) ^ 2
  let val_sq := (2 * (n + 1) : ℝ) - Q_2n_plus_1
  if h : 0 ≤ val_sq then
    NNReal.sqrt ⟨val_sq, h⟩
  else
    0

/-
Let $f(k) = \frac{k\sqrt{2}}{2k-1}$ for $k \ge 1$.
-/
def f (k : ℕ) : ℝ := (k : ℝ) * Real.sqrt 2 / (2 * (k : ℝ) - 1)

/-
For a given $\lambda > 1/\sqrt{2}$, Alice's reference strategy is as follows: first, choose an integer $K$ according to Lemma~\ref{lem:existence_of_K_for_alice} such that $\lambda > \frac{K\sqrt{2}}{2K-1}$.
Then, for all turns $2k-1$ with $k < K$, Alice chooses $x_{2k-1}=0$. At turn $2K-1$, Alice chooses $x_{2K-1} = \lambda(2K-1) - S_{2K-2}$.
-/
def aliceReferenceStrategy (lam : ℝ) (K : ℕ) : AliceStrategy := fun n hist ↦
  if n + 1 < K then
    0
  else if n + 1 = K then
    let S_2n := ∑ i, (hist i : ℝ)
    let move := lam * (2 * (n + 1) - 1) - S_2n
    if h_nonneg : 0 ≤ move then
      ⟨move, h_nonneg⟩
    else
      0
  else
    0

/-
If Bazza uses his reference strategy (Definition~\ref{def:bazza_strategy}) and can make a move at turn $2k$, then $Q_{2k}=2k$.
-/
lemma lemBazzaStrategyQValue (n : ℕ) (h : Fin (2 * n + 1) → NNReal)
  (h_can_move : (∑ i, (h i : ℝ) ^ 2) ≤ (2 * (n + 1) : ℝ)) :
  let x_2np1 := bazzaReferenceStrategy n h
  (∑ i, (h i : ℝ) ^ 2) + (x_2np1 : ℝ) ^ 2 = (2 * (n + 1) : ℝ) := by
  unfold bazzaReferenceStrategy;
  aesop

/-
If Bazza uses his reference strategy and neither player has won by turn $2k-1$, then $Q_{2k-2} = 2(k-1)$ for $k \ge 2$. For $k=1$, $Q_0=0$ by Definition~\ref{def:sums}.
-/
lemma lemQ_2k_minus_2_under_bazza_ref (lam : ℝ) (alice : AliceStrategy) (k : ℕ) (hk : 1 ≤ k)
  (h_not_won : ∀ m < 2 * k - 2, ValidMove lam (play alice bazzaReferenceStrategy) m) :
  q (play alice bazzaReferenceStrategy) (2 * (k - 1)) = (2 * (k - 1) : ℝ) := by
  -- For the case when $k = 1$, we have $2 * (k - 1) = 0$, and the sum of squares up to 0 is 0, which matches $2 * (1 - 1) = 0$.
  by_cases hk1 : k = 1;
  · aesop;
  · rcases k with ( _ | _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
    have h_q_2k : (∑ i in Finset.range (2 * k + 1), (play alice bazzaReferenceStrategy i : ℝ) ^ 2) ≤ (2 * (k + 1) : ℝ) := by
      specialize h_not_won ( 2 * k + 1 ) ; unfold ValidMove at h_not_won ; aesop;
      norm_cast;
      refine le_trans ?_ ( h_not_won.trans ?_ );
      · exact Finset.sum_le_sum_of_subset ( fun x hx => Finset.mem_Iic.mpr ( Finset.mem_range_le hx |> le_trans <| Nat.le_refl _ ) );
      · norm_cast;
    -- By definition of $q$, we can write
    have h_q_def : q (play alice bazzaReferenceStrategy) (2 * k + 2) = (∑ i in Finset.range (2 * k + 1), (play alice bazzaReferenceStrategy i : ℝ) ^ 2) + (bazzaReferenceStrategy k (fun i => play alice bazzaReferenceStrategy i) : ℝ) ^ 2 := by
      unfold q;
      rw [Finset.sum_range_succ];
      unfold play;
      norm_num +zetaDelta at *;
      rw [ show ( 2 * k + 1 ) / 2 = k by omega ];
      congr! 2;
      exact?;
    convert lemBazzaStrategyQValue k _ _ using 1;
    convert h_q_def;
    · rw [ Finset.sum_range ];
    · simpa only [ Finset.sum_range ] using h_q_2k

/-
If Alice does not win at turn $2j-1$ against Bazza's reference strategy, then the sum of that turn's moves is $x_{2j-1}+x_{2j} \ge \sqrt{2}$.
-/
lemma lemPairSumLowerBound (xs : ℕ → NNReal) (j : ℕ) (hj : 1 ≤ j)
  (h_q_prev : q xs (2 * (j - 1)) = (2 * (j - 1) : ℝ))
  (h_bazza_move : xs (2 * j - 1) = bazzaReferenceStrategy (j - 1) fun i ↦ xs i.val)
  (h_not_win : ¬ (q xs (2 * j - 1) > (2 * j : ℝ))) :
  (xs (2 * j - 2) : ℝ) + (xs (2 * j - 1) : ℝ) ≥ Real.sqrt 2 := by
  -- By definition of $bazzaReferenceStrategy$, we know that $x_{2j} = \sqrt{2 - x_{2j-1}^2}$.
  have h_bazza_move_value : (xs (2 * j - 1) : ℝ) = Real.sqrt (2 - (xs (2 * j - 2) : ℝ) ^ 2) := by
    rcases j with ⟨ _ | j ⟩ <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, Finset.sum_range_succ ];
    unfold bazzaReferenceStrategy;
    simp_all ( config := { decide := Bool.true } ) [ Fin.sum_univ_castSucc, q ];
    split_ifs <;> simp_all ( config := { decide := Bool.true } ) [ Finset.sum_range ];
    · ring;
    · rw [ Real.sqrt_eq_zero_of_nonpos ] ; linarith;
  by_cases h_case : (xs (2 * j - 2) : ℝ) ≤ Real.sqrt 2;
  · field_simp;
    rw [ h_bazza_move_value, Real.sqrt_le_left ];
    · nlinarith only [ Real.sqrt_nonneg ( 2 - ( xs ( 2 * j - 2 ) : ℝ ) ^ 2 ), Real.mul_self_sqrt ( show 0 ≤ 2 - ( xs ( 2 * j - 2 ) : ℝ ) ^ 2 by nlinarith only [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), h_case, show ( xs ( 2 * j - 2 ) : ℝ ) ≥ 0 by positivity ] ), show ( xs ( 2 * j - 2 ) : ℝ ) ≥ 0 by positivity ];
    · positivity;
  · exact le_add_of_le_of_nonneg ( le_of_not_le h_case ) ( NNReal.coe_nonneg _ )

/-
If Bazza uses his reference strategy and Alice has not won by turn $2k-1$, then $S_{2k-2} \ge (k-1)\sqrt{2}$ for $k \ge 1$.
-/
lemma lemSLowerBound (lam : ℝ) (alice : AliceStrategy) (k : ℕ) (hk : 1 ≤ k)
  (h_not_won : ∀ m < 2 * k - 2, ValidMove lam (play alice bazzaReferenceStrategy) m) :
  s (play alice bazzaReferenceStrategy) (2 * (k - 1)) ≥ ((k - 1) : ℝ) * Real.sqrt 2 := by
  -- By Lemma~\ref{lem:pair_sum_lower_bound}, for each $j$ from $1$ to $k-1$, we have $x_{2j-1} + x_{2j} \ge \sqrt{2}$.
  have h_pair_sum_lower_bound : ∀ j ∈ Finset.Ico 1 k, (play alice bazzaReferenceStrategy (2 * j - 2) : ℝ) + (play alice bazzaReferenceStrategy (2 * j - 1) : ℝ) ≥ Real.sqrt 2 := by
    intro j hj;
    apply_rules [ lemPairSumLowerBound ];
    · -- Since $j$ is in the Finset.Ico 1 k, we have $1 \leq j$.
      aesop;
    · -- Apply the lemma that states if Bazza uses his reference strategy and neither player has won by turn $2k-1$, then $Q_{2k-2} = 2(k-1)$.
      apply lemQ_2k_minus_2_under_bazza_ref;
      exacts [ Finset.mem_Ico.mp hj |>.1, fun m hm => h_not_won m ( by linarith [ Finset.mem_Ico.mp hj |>.2, Nat.sub_add_cancel ( by linarith [ Finset.mem_Ico.mp hj |>.1, Finset.mem_Ico.mp hj |>.2 ] : 2 ≤ 2 * k ), Nat.sub_add_cancel ( by linarith [ Finset.mem_Ico.mp hj |>.1, Finset.mem_Ico.mp hj |>.2 ] : 2 ≤ 2 * j ) ] ) ];
    · unfold play;
      -- Since $2j-1$ is odd, $(2j-1) \% 2 = 1$, so the if condition is false.
      have h_odd : (2 * j - 1) % 2 = 1 := by
        cases j <;> norm_num [ Nat.add_mod, Nat.mul_succ ] at *;
      rw [ if_neg ];
      · rw [ show ( 2 * j - 1 ) / 2 = j - 1 by omega ];
        congr!;
        exact?;
      · -- Since $h_odd$ states that $(2 * j - 1) \% 2 = 1$, we can directly conclude that $(2 * j - 1) \% 2 \neq 0$.
        aesop;
    · rcases j with ( _ | j ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
      have := h_not_won ( 2 * j + 1 ) ( by omega );
      unfold ValidMove at this; aesop;
      exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( fun i hi => Finset.mem_Iic.mpr ( by linarith [ Finset.mem_range.mp hi ] ) ) fun _ _ _ => sq_nonneg _ ) ( mod_cast this );
  -- By summing the inequalities from h_pair_sum_lower_bound over all j from 1 to k-1, we get the desired result.
  have h_sum_pairs : ∑ j in Finset.Ico 1 k, ((play alice bazzaReferenceStrategy (2 * j - 2) : ℝ) + (play alice bazzaReferenceStrategy (2 * j - 1) : ℝ)) ≥ (k - 1) * Real.sqrt 2 := by
    exact le_trans ( by norm_num [ hk ] ) ( Finset.sum_le_sum h_pair_sum_lower_bound );
  convert h_sum_pairs using 1;
  unfold s;
  exact Nat.recOn k ( by norm_num ) fun n ih => by cases n <;> norm_num [ Nat.mul_succ, Finset.sum_range_succ, Finset.sum_Ico_succ_top ] at * ; linarith;

/-
The limit of $f(k)$ from Definition~\ref{def:f_function} as $k \to \infty$ is $1/\sqrt{2}$.
-/
lemma lemFLimit : Filter.Tendsto f Filter.atTop (nhds (1 / Real.sqrt 2)) := by
  unfold f;
  -- We can divide the numerator and the denominator by $k$ and then take the limit as $k$ approaches infinity.
  have h_div : Filter.Tendsto (fun k : ℕ => (Real.sqrt 2) / (2 - 1 / (k : ℝ))) Filter.atTop (nhds (Real.sqrt 2 / 2)) := by
    exact le_trans ( tendsto_const_nhds.div ( tendsto_const_nhds.sub <| tendsto_one_div_atTop_nhds_zero_nat ) <| by norm_num ) <| by norm_num;
  refine Filter.Tendsto.congr' ?_ ( h_div.trans ?_ );
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk using by simpa [ -one_div, field_simps, hk.ne' ] using by ring;
  · norm_num [ Real.sqrt_div_self ]

/-
If $0 < \lambda < 1/\sqrt{2}$, Bazza has a winning strategy.
-/
lemma lemBazzaWinsSmallLambda (lam : ℝ) (hlam : 0 < lam ∧ lam < 1 / Real.sqrt 2) :
  ∃ bazza, BazzaStrategy.Wins lam bazza := by
  -- By Lemma~\ref{lem:alice_cannot_win_small_lambda}, if $\lambda \le 1/\sqrt{2}$, Alice cannot have a winning strategy. Therefore, Bazza's reference strategy must be a winning strategy.
  have h_bazza_wins : ∀ alice : AliceStrategy, ∃ n, IsLeast {m | ¬ValidMove lam (play alice bazzaReferenceStrategy) m} n ∧ Even n := by
    bound;
    by_contra h_contra;
    -- If Alice cannot win, then for all $n$, the game continues.
    have h_game_continues : ∀ n, ValidMove lam (play alice bazzaReferenceStrategy) n := by
      intro n;
      induction' n using Nat.strong_induction_on with n ih;
      rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
      · unfold ValidMove;
        contrapose! h_contra;
        use 2 * k;
        unfold ValidMove;
        unfold IsLeast;
        aesop;
        intro m hm;
        contrapose! hm;
        unfold ValidMove at ih; aesop;
      · have h_q_prev : q (play alice bazzaReferenceStrategy) (2 * k) = (2 * k : ℝ) := by
          convert lemQ_2k_minus_2_under_bazza_ref lam alice ( k + 1 ) ( by linarith ) _ using 1;
          · norm_num;
          · grind;
        unfold ValidMove;
        have h_not_win : ¬ (q (play alice bazzaReferenceStrategy) (2 * k + 1) > (2 * (k + 1) : ℝ)) := by
          have h_not_win : (play alice bazzaReferenceStrategy) (2 * k) ≤ Real.sqrt 2 := by
            have h_not_win : (play alice bazzaReferenceStrategy) (2 * k) ≤ lam * (2 * k + 1) - s (play alice bazzaReferenceStrategy) (2 * k) := by
              have := ih ( 2 * k ) ( by linarith ) ; unfold ValidMove at this ; aesop;
              unfold s;
              erw [ Finset.sum_Ico_eq_sub _ _ ] at this <;> norm_num at *;
              rw [ Finset.sum_range_succ ] at this ; linarith;
            have h_s_lower_bound : s (play alice bazzaReferenceStrategy) (2 * k) ≥ (k : ℝ) * Real.sqrt 2 := by
              convert lemSLowerBound lam alice ( k + 1 ) ( by linarith ) _ using 1;
              · norm_num;
              · exact fun m hm => ih m ( by omega );
            rw [ lt_div_iff₀ ] at * <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
          unfold q at *;
          norm_num [ Finset.sum_range_succ ];
          nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), show ( play alice bazzaReferenceStrategy ( 2 * k ) : ℝ ) ≥ 0 by positivity ];
        aesop;
        unfold q at *;
        erw [ Finset.sum_Ico_succ_top ] <;> norm_num;
        rw [ show play alice bazzaReferenceStrategy ( 2 * k + 1 ) = bazzaReferenceStrategy k fun i => play alice bazzaReferenceStrategy i from ?_ ];
        · rw [ ← NNReal.coe_le_coe ] ; aesop;
          unfold bazzaReferenceStrategy;
          norm_num [ Finset.sum_range ] at *;
          split_ifs;
          · norm_num [ ← NNReal.coe_le_coe ];
            rw [ Real.sq_sqrt ] <;> linarith;
          · convert h_not_win using 1;
            · unfold bazzaReferenceStrategy;
              norm_num;
            · ring;
        · unfold play;
          norm_num [ Nat.add_mod ];
          rw [ show ( 2 * k + 1 ) / 2 = k by omega ];
          congr!;
          exact?;
    -- By Lemma~\ref{lem:s_lower_bound}, $S_{2k-2} \ge (k-1)\sqrt{2}$ for all $k \ge 1$.
    have h_s_lower_bound : ∀ k : ℕ, 1 ≤ k → s (play alice bazzaReferenceStrategy) (2 * (k - 1)) ≥ ((k - 1) : ℝ) * Real.sqrt 2 := by
      intro k hk;
      convert lemSLowerBound lam alice k hk _;
      exact fun m hm => h_game_continues m;
    -- Choose $k$ such that $(k-1)\sqrt{2} > \lambda(2k-1)$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 ≤ k ∧ ((k - 1) : ℝ) * Real.sqrt 2 > lam * ((2 * k - 1) : ℝ) := by
      rw [ lt_div_iff₀ ] at * <;> norm_num;
      exact ⟨ ⌊ ( 1 - lam * Real.sqrt 2 ) ⁻¹ * 2⌋₊ + 2, by linarith, by push_cast; nlinarith [ Nat.lt_floor_add_one ( ( 1 - lam * Real.sqrt 2 ) ⁻¹ * 2 ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_inv_cancel₀ ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] : ( 1 - lam * Real.sqrt 2 ) ≠ 0 ) ] ⟩;
    specialize h_s_lower_bound k hk.1;
    specialize h_game_continues ( 2 * ( k - 1 ) ) ; unfold ValidMove at h_game_continues ; aesop;
    erw [ Finset.sum_Ico_eq_sub _ _ ] at h_game_continues <;> norm_num at *;
    unfold s at h_s_lower_bound;
    rw [ Finset.sum_range_succ ] at h_game_continues;
    linarith [ show ( play alice bazzaReferenceStrategy ( 2 * ( k - 1 ) ) : ℝ ) ≥ 0 by positivity ];
  exact ⟨ bazzaReferenceStrategy, h_bazza_wins ⟩

/-
If $\lambda > 1/\sqrt{2}$, there exists a positive integer $K$ such that $\lambda > \frac{K\sqrt{2}}{2K-1}$.
-/
lemma lemExistenceOfKForAlice (lam : ℝ) (hlam : lam > 1 / Real.sqrt 2) :
  ∃ K : ℕ, 1 ≤ K ∧ lam > f K := by
  have := @lemFLimit;
  exact Filter.eventually_atTop.mp ( this.eventually ( gt_mem_nhds hlam ) ) |> fun ⟨ K, hK ⟩ ↦ ⟨ K + 1, by linarith, hK _ <| by linarith ⟩

/-
For Alice's strategy from Definition~\ref{def:alice_strategy}, the sum $S_{2K-2}$ is bounded by $(S_{2K-2})^2 \le (K-1)Q_{2K-2}$.
-/
lemma lemSBoundByQ (lam : ℝ) (K : ℕ) (hK : 1 ≤ K) (bazza : BazzaStrategy) :
  let xs := play (aliceReferenceStrategy lam K) bazza
  (s xs (2 * (K - 1))) ^ 2 ≤ ((K - 1) : ℝ) * q xs (2 * (K - 1)) := by
  -- By definition of $s$ and $q$, we can split the sum into two parts: one over even indices and one over odd indices.
  have h_split_sum : s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ∧ q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ^ 2 := by
    -- By definition of $s$ and $q$, we can split the sum into two parts: one over even indices and one over odd indices. Since Alice's strategy for the first $K-1$ turns is to choose $0$, the sum of the play values at even indices up to $2*(K-1)$ is zero. Therefore, the total sum is just the sum of the play values at the odd indices.
    have h_split_sum : ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ∧ ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) ^ 2 = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ^ 2 := by
      -- By definition of $play$, we know that for even indices, the value is zero, and for odd indices, it's determined by Bazza's strategy.
      have h_play_even_zero : ∀ i < K - 1, play (aliceReferenceStrategy lam K) bazza (2 * i) = 0 := by
        -- By definition of play, for even indices, the value is determined by Alice's strategy. Since Alice's strategy returns zero for indices less than K-1, we have:
        intros i hi
        have h_alice_move : aliceReferenceStrategy lam K i (fun j => play (aliceReferenceStrategy lam K) bazza j) = 0 := by
          unfold aliceReferenceStrategy;
          grind;
        unfold play;
        -- Since $2i$ is even, the play value is determined by Alice's strategy, which returns zero for indices less than $K-1$.
        simp [h_alice_move];
        rwa [ Nat.mul_div_cancel_left _ ( by decide ) ];
      -- By definition of $play$, we know that for even indices, the value is zero, and for odd indices, it's determined by Bazza's strategy. Therefore, we can split the sum into two parts: one over even indices and one over odd indices.
      have h_split_sum : ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i) : ℝ) + ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ∧ ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) ^ 2 = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i) : ℝ) ^ 2 + ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ^ 2 := by
        induction' K - 1 with k hk;
        · norm_num;
        · simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, Finset.sum_range_succ ];
          constructor <;> ring;
      exact ⟨ by rw [ h_split_sum.1, Finset.sum_eq_zero fun i hi => by rw [ h_play_even_zero i ( Finset.mem_range.mp hi ) ] ; norm_num ] ; ring, by rw [ h_split_sum.2, Finset.sum_eq_zero fun i hi => by rw [ h_play_even_zero i ( Finset.mem_range.mp hi ) ] ; norm_num ] ; ring ⟩;
    exact h_split_sum;
  -- Applying the Cauchy-Schwarz inequality to the sums, we get:
  have h_cauchy_schwarz : (∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ))^2 ≤ (Finset.card (Finset.range (K - 1))) * (∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ)^2) := by
    exact?;
  cases K <;> aesop

/-
If Alice follows her reference strategy, any sequence of valid moves by Bazza up to turn $2K-2$ must satisfy $S_{2K-2} \le \sqrt{2}(K-1)$.
-/
lemma lemBazzaDefenseSBound (lam : ℝ) (K : ℕ) (hK : 1 ≤ K) (bazza : BazzaStrategy)
  (h_valid : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m) :
  s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) ≤ Real.sqrt 2 * ((K - 1) : ℝ) := by
  -- By the properties of the play sequence and the ValidMove condition, we can derive that the sum of the first 2*(K-1) terms is bounded by sqrt(2)*(K-1).
  have h_sum_bound : (s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) ^ 2 ≤ (K - 1) * q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) := by
    exact?;
  -- Substitute the bound on $q$ into the inequality for $s$.
  have h_subst : (s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) ^ 2 ≤ (K - 1) * (2 * (K - 1)) := by
    specialize h_valid ( 2 * K - 3 ) ; rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
    refine le_trans h_sum_bound ?_;
    unfold q at *;
    rw [ Finset.sum_range_succ ];
    unfold ValidMove at h_valid ; aesop;
    erw [ Finset.sum_Ico_succ_top ] at h_valid <;> norm_num at *;
    exact mul_le_mul_of_nonneg_left ( mod_cast h_valid ) ( by positivity );
  nlinarith only [ show 0 ≤ Real.sqrt 2 * ( K - 1 ) by exact mul_nonneg ( Real.sqrt_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hK ) ), h_subst, Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ]

/-
Alice's move $x_{2K-1}$ in her reference strategy is a valid move.
-/
lemma lemAliceMoveValid (lam : ℝ) (hlam : lam > 1 / Real.sqrt 2) (K : ℕ) (hK : 1 ≤ K ∧ lam > f K)
  (bazza : BazzaStrategy)
  (h_valid_hist : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m) :
  ValidMove lam (play (aliceReferenceStrategy lam K) bazza) (2 * K - 2) := by
  unfold ValidMove; aesop;
  · -- By definition of $S$, we can write
    have hS : ∑ i in Finset.Iic (2 * K - 2), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = s (play (aliceReferenceStrategy lam K) bazza) (2 * K - 1) := by
      erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num;
      rcases K with ( _ | _ | K ) <;> trivial;
    rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
    · unfold s;
      unfold play; norm_num;
      unfold aliceReferenceStrategy;
      norm_num;
      split_ifs <;> norm_num ; linarith [ inv_nonneg.2 ( Real.sqrt_nonneg 2 ) ];
    · unfold f at right;
      rw [ div_lt_iff₀ ] at right <;> norm_num at *;
      · have := lemBazzaDefenseSBound lam ( K + 1 + 1 ) ( by linarith ) bazza;
        unfold s at *;
        rw [ Finset.sum_range_succ ];
        rw [ show play ( aliceReferenceStrategy lam ( K + 1 + 1 ) ) bazza ( 2 * K + 2 ) = aliceReferenceStrategy lam ( K + 1 + 1 ) ( K + 1 ) ( fun i => play ( aliceReferenceStrategy lam ( K + 1 + 1 ) ) bazza i ) from ?_ ];
        · unfold aliceReferenceStrategy at *;
          norm_num [ Finset.sum_range, Nat.mul_succ ] at *;
          split_ifs <;> norm_num;
          · linarith!;
          · exact le_trans ( this fun m mn => h_valid_hist m mn ) ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] );
        · unfold play;
          norm_num [ Nat.add_mod ];
          rw [ show ( 2 * K + 2 ) / 2 = K + 1 by norm_num [ Nat.add_div ] ];
          congr!;
          exact?;
      · linarith;
  · exact absurd h ( by rw [ Nat.odd_iff ] ; omega )

/-
Following her reference strategy, Alice wins at turn $2K$ if and only if $\lambda(2K-1) > S_{2K-2} + \sqrt{2K - Q_{2K-2}}$.
-/
lemma lemAliceWinConditionFinalForm (lam : ℝ) (hlam : lam > 1 / Real.sqrt 2) (K : ℕ) (hK : 1 ≤ K ∧ lam > f K) (bazza : BazzaStrategy)
  (h_valid : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m) :
  let xs := play (aliceReferenceStrategy lam K) bazza
  (q xs (2 * K - 1) > (2 * K : ℝ)) ↔
  lam * ((2 * K - 1) : ℝ) > s xs (2 * (K - 1)) + Real.sqrt ((2 * K : ℝ) - q xs (2 * (K - 1))) := by
  bound;
  · -- Since $a > 2K$, we have $q xs (2K-1) > 2K$, which implies $q xs (2(K-1)) + (xs (2K-2))^2 > 2K$.
    have h_q_split : q xs (2 * (K - 1)) + (xs (2 * K - 2) : ℝ) ^ 2 > 2 * K := by
      convert a using 1;
      unfold q;
      rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, Finset.sum_range_succ ];
    -- Substitute $x_{2K-1} = \lambda(2K-1) - S_{2K-2}$ into the inequality.
    have h_subst : (xs (2 * K - 2) : ℝ) = lam * (2 * K - 1) - s xs (2 * (K - 1)) := by
      have h_subst : xs (2 * K - 2) = aliceReferenceStrategy lam K (K - 1) (fun i => xs i) := by
        have h_subst : ∀ n, xs n = if n % 2 = 0 then aliceReferenceStrategy lam K (n / 2) (fun i => xs i) else bazza (n / 2) (fun i => xs i) := by
          exact?;
        rw [ h_subst ];
        rw [ if_pos ( by omega ), show ( 2 * K - 2 ) / 2 = K - 1 by omega ];
      unfold aliceReferenceStrategy at h_subst;
      rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
      · unfold s; norm_num;
        split_ifs <;> norm_num ; linarith [ inv_nonneg.2 ( Real.sqrt_nonneg 2 ) ];
      · unfold s;
        split_ifs <;> simp_all ( config := { decide := Bool.true } ) [ Finset.sum_range ];
        have := h_valid ( 2 * K + 1 ) ( by linarith ) ; unfold ValidMove at this ; aesop;
        contrapose! h_q_split;
        unfold q;
        norm_cast;
        exact le_trans ( by rw [ Finset.range_eq_Ico ] ; rfl ) ( this.trans ( by ring_nf; norm_num ) );
    aesop;
    -- Taking the square root of both sides of the inequality from h_q_split, we get Real.sqrt (2 * K - q xs (2 * (K - 1))) < lam * (2 * K - 1) - s xs (2 * (K - 1)).
    have h_sqrt : Real.sqrt (2 * K - q xs (2 * (K - 1))) < lam * (2 * K - 1) - s xs (2 * (K - 1)) := by
      rw [ Real.sqrt_lt ];
      · linarith;
      · rcases K with ( _ | _ | K ) <;> norm_num [ Nat.mul_succ ] at *;
        · exact show ( ∑ i in Finset.range 0, ( xs i : ℝ ) ^ 2 ) ≤ 2 by norm_num;
        · specialize h_valid ( 2 * K + 1 ) ; unfold ValidMove at h_valid ; aesop;
          unfold q;
          norm_cast;
          exact le_trans ( by rw [ Finset.range_eq_Ico ] ; rfl ) ( h_valid.trans ( by ring_nf; norm_num ) );
      · exact h_subst ▸ NNReal.coe_nonneg _;
    linarith;
  · -- Substitute the expression for $xs (2K - 2)$ from Alice's reference strategy.
    have h_subst : xs (2 * K - 2) = lam * (2 * K - 1) - s xs (2 * K - 2) := by
      rcases K with ( _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
      -- By definition of `aliceReferenceStrategy`, when `n + 1 = K`, Alice sets `xs (2 * K)` to `lam * (2 * (K + 1) - 1) - s xs (2 * K)`.
      have h_alice_move : xs (2 * K) = aliceReferenceStrategy lam (K + 1) K (fun i => xs i) := by
        have h_alice_move : ∀ n, xs n = if n % 2 = 0 then aliceReferenceStrategy lam (K + 1) (n / 2) (fun i => xs i) else bazza (n / 2) (fun i => xs i) := by
          exact?;
        rw [ h_alice_move ] ; norm_num;
        rw [ Nat.mul_div_cancel_left _ ( by decide ) ];
      unfold aliceReferenceStrategy at *;
      unfold s at *;
      simp +zetaDelta at *;
      rw [ h_alice_move, Finset.sum_range ];
      split_ifs <;> norm_num;
      exact False.elim <| ‹¬_› <| by simpa [ Finset.sum_range ] using a.le.trans' <| add_le_add_left ( Real.sqrt_nonneg _ ) _;
    -- Substitute the expression for $q xs (2 * K - 1)$ using the definition of $q$.
    have h_q : q xs (2 * K - 1) = q xs (2 * K - 2) + (xs (2 * K - 2) : ℝ) ^ 2 := by
      unfold q;
      cases K <;> norm_num [ Nat.mul_succ, Finset.sum_range_succ ] at *;
    rcases K with ( _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
    contrapose! a;
    nlinarith [ Real.sqrt_nonneg ( 2 * ( K + 1 ) - q xs ( 2 * K ) ), Real.mul_self_sqrt ( show 0 ≤ 2 * ( K + 1 ) - q xs ( 2 * K ) by nlinarith ) ]

/-
For any sequence of valid moves by Bazza against Alice's reference strategy, $S_{2K-2} + \sqrt{2K - Q_{2K-2}} \le K\sqrt{2}$.
-/
lemma lemBazzaObjectiveUpperBound (lam : ℝ) (K : ℕ) (hK : 2 ≤ K) (bazza : BazzaStrategy)
  (h_valid : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m) :
  let xs := play (aliceReferenceStrategy lam K) bazza
  s xs (2 * (K - 1)) + Real.sqrt ((2 * K : ℝ) - q xs (2 * (K-1))) ≤ (K : ℝ) * Real.sqrt 2 := by
  -- By Lemma~\ref{lem:q_bound}, we know that $Q_{2K-2} \leq 2(K-1)$.
  have h_q_bound : q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) ≤ 2 * (K - 1) := by
    -- Apply the hypothesis `h_valid` with `m = 2 * (K - 1) - 1`.
    specialize h_valid (2 * (K - 1) - 1);
    rcases K with ( _ | _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ ];
    unfold ValidMove at h_valid ; aesop;
    convert h_valid using 1;
    unfold q; norm_cast;
    erw [ Finset.range_eq_Ico ] ; rfl;
  -- By Lemma~\ref{lem:s_lower_bound}, we know that $S_{2K-2} \leq \sqrt{(K-1)Q_{2K-2}}$.
  have h_s_lower_bound : s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) ≤ Real.sqrt ((K - 1) * q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) := by
    refine Real.le_sqrt_of_sq_le ?_;
    unfold s q;
    -- By definition of play, we know that play (aliceReferenceStrategy lam K) bazza (2 * i) = 0 for all i < K - 1.
    have h_play_zero : ∀ i < K - 1, play (aliceReferenceStrategy lam K) bazza (2 * i) = 0 := by
      unfold play;
      unfold aliceReferenceStrategy;
      grind;
    -- Since $play (aliceReferenceStrategy lam K) bazza (2 * i) = 0$ for all $i < K - 1$, we can split the sum into two parts: one over even indices and one over odd indices.
    have h_split_sum : ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) := by
      have h_split_sum : Finset.range (2 * (K - 1)) = Finset.image (fun i => 2 * i) (Finset.range (K - 1)) ∪ Finset.image (fun i => 2 * i + 1) (Finset.range (K - 1)) := by
        ext ; aesop;
        · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
        · linarith;
      rw [ h_split_sum, Finset.sum_union ];
      · norm_num;
        exact Finset.sum_eq_zero fun i hi => by rw [ h_play_zero i ( Finset.mem_range.mp hi ) ] ; norm_num;
      · norm_num [ Finset.disjoint_right ];
        grind;
    -- Applying the Cauchy-Schwarz inequality to the sum of the terms over odd indices.
    have h_cauchy_schwarz_odd : (∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ))^2 ≤ (K - 1) * (∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ)^2) := by
      have h_cauchy_schwarz_odd : ∀ (u v : Fin (K - 1) → ℝ), (∑ i, u i * v i)^2 ≤ (∑ i, u i^2) * (∑ i, v i^2) := by
        exact?;
      simpa [ Finset.sum_range, Nat.cast_sub ( show 1 ≤ K by linarith ) ] using h_cauchy_schwarz_odd ( fun _ => 1 ) ( fun i => ( play ( aliceReferenceStrategy lam K ) bazza ( 2 * i + 1 ) : ℝ ) );
    -- Since the play values at even indices are zero, the sum of the squares up to 2*(K-1) is just the sum of the squares of the odd terms up to K-1.
    have h_split_sum_sq : ∑ i in Finset.range (2 * (K - 1)), (play (aliceReferenceStrategy lam K) bazza i : ℝ)^2 = ∑ i in Finset.range (K - 1), (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ)^2 := by
      have h_split_sum_sq : Finset.range (2 * (K - 1)) = Finset.image (fun i => 2 * i) (Finset.range (K - 1)) ∪ Finset.image (fun i => 2 * i + 1) (Finset.range (K - 1)) := by
        ext ; aesop;
        · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
        · grind;
      rw [ h_split_sum_sq, Finset.sum_union ];
      · norm_num;
        exact Finset.sum_eq_zero fun i hi => by rw [ h_play_zero i ( Finset.mem_range.mp hi ) ] ; norm_num;
      · norm_num [ Finset.disjoint_right ];
        intros; omega;
    aesop;
  refine le_trans ( add_le_add h_s_lower_bound le_rfl ) ?_;
  -- Applying the Cauchy-Schwarz inequality, we get:
  have h_cauchy_schwarz : (Real.sqrt ((K - 1) * q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) + Real.sqrt (2 * K - q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)))) ^ 2 ≤ (K - 1 + 1) * ((q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) + (2 * K - q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)))) := by
    rw [ Real.sqrt_mul ( by norm_num; linarith ) ];
    nlinarith only [ sq_nonneg ( Real.sqrt ( K - 1 ) * Real.sqrt ( 2 * K - q ( play ( aliceReferenceStrategy lam K ) bazza ) ( 2 * ( K - 1 ) ) ) - Real.sqrt ( q ( play ( aliceReferenceStrategy lam K ) bazza ) ( 2 * ( K - 1 ) ) ) ), Real.mul_self_sqrt ( show ( K : ℝ ) - 1 ≥ 0 by norm_num; linarith ), Real.mul_self_sqrt ( show ( q ( play ( aliceReferenceStrategy lam K ) bazza ) ( 2 * ( K - 1 ) ) : ℝ ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => sq_nonneg _ ), Real.mul_self_sqrt ( show ( 2 * K - q ( play ( aliceReferenceStrategy lam K ) bazza ) ( 2 * ( K - 1 ) ) : ℝ ) ≥ 0 by linarith ) ];
  exact le_trans ( Real.le_sqrt_of_sq_le h_cauchy_schwarz ) ( Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ] ⟩ )

/-
If $\lambda > 1/\sqrt{2}$, Alice has a winning strategy.
-/
lemma lemAliceWinsLargeLambda (lam : ℝ) (hlam : lam > 1 / Real.sqrt 2) :
  ∃ alice, AliceStrategy.Wins lam alice := by
  -- obtain such a K using lemExistenceOfKForAlice
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 ≤ K ∧ lam > f K := by
    exact?;
  use aliceReferenceStrategy lam K;
  intro bazza;
  by_contra h_contra;
  -- If Alice never wins, then Bazza must win by turn $2K-1$.
  have h_bazza_wins : ∀ m < 2 * K - 2, ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m := by
    intro m hm;
    induction' m using Nat.strong_induction_on with m ih;
    by_cases h_even : Even m;
    · unfold ValidMove;
      -- Since $m$ is even, we can write $m = 2k$ for some $k$.
      obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := even_iff_two_dvd.mp h_even;
      -- By definition of play, we can write out the sum.
      have h_sum : ∑ i in Finset.Iic (2 * k), (play (aliceReferenceStrategy lam K) bazza i : ℝ) = ∑ i in Finset.range k, (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) := by
        erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, Nat.mul_succ ];
        rw [ show ( Finset.range ( 2 * k ) : Finset ℕ ) = Finset.image ( fun i => 2 * i ) ( Finset.range k ) ∪ Finset.image ( fun i => 2 * i + 1 ) ( Finset.range k ) from ?_, Finset.sum_union ] <;> norm_num;
        · unfold play;
          unfold aliceReferenceStrategy;
          norm_num;
          rw [ Finset.sum_congr rfl fun i hi => by rw [ if_pos ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( show 2 ≤ 2 * K from by linarith ) ] ) ] ] ; norm_num;
          intros; omega;
        · norm_num [ Finset.disjoint_right ];
          intros; omega;
        · ext ; aesop;
          · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
          · linarith;
      -- By definition of play, we can write out the sum of squares.
      have h_sum_squares : ∑ i in Finset.range k, (play (aliceReferenceStrategy lam K) bazza (2 * i + 1) : ℝ) ^ 2 ≤ 2 * k := by
        have := ih ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
        have := ih ( 2 * k + 1 ) ( by linarith ) ( by omega ) ; unfold ValidMove at this; aesop;
        norm_cast;
        refine le_trans ?_ ( this.trans ?_ );
        · have h_sum_squares : Finset.image (fun i => 2 * i + 1) (Finset.range (k + 1)) ⊆ Finset.Iic (2 * k + 1) := by
            exact Finset.image_subset_iff.mpr fun i hi => Finset.mem_Iic.mpr ( by linarith [ Finset.mem_range.mp hi ] );
          exact le_trans ( by rw [ Finset.sum_image ( by norm_num ) ] ) ( Finset.sum_le_sum_of_subset h_sum_squares );
        · norm_cast;
      have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range k ) => pow_two_nonneg ( ( play ( aliceReferenceStrategy lam K ) bazza ( 2 * i + 1 ) : ℝ ) - Real.sqrt 2 );
      norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] at this;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
      rw [ inv_eq_one_div, div_lt_iff₀ ] at hlam <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
    · contrapose! h_contra;
      use m;
      exact ⟨ ⟨ h_contra, fun n hn => not_lt.1 fun contra => hn <| ih n contra <| by omega ⟩, Nat.odd_iff.mpr <| Nat.not_even_iff.mp h_even ⟩;
  have h_alice_wins : q (play (aliceReferenceStrategy lam K) bazza) (2 * K - 1) > (2 * K : ℝ) := by
    have h_alice_wins : lam * ((2 * K - 1) : ℝ) > s (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1)) + Real.sqrt ((2 * K : ℝ) - q (play (aliceReferenceStrategy lam K) bazza) (2 * (K - 1))) := by
      have := lemBazzaObjectiveUpperBound lam K;
      rcases K with ( _ | _ | K ) <;> aesop;
      · unfold s q; norm_num;
        unfold f at hK ; aesop;
        norm_num at hK ; linarith;
      · refine' lt_of_le_of_lt ( this bazza h_bazza_wins ) _;
        unfold f at hK;
        rw [ div_lt_iff₀ ] at hK <;> norm_num at * <;> nlinarith;
    exact?;
  refine' h_contra ⟨ 2 * K - 1, _, _ ⟩;
  · -- Since $ValidMove$ holds for all $m < 2K-2$, the next $m$ where $ValidMove$ fails must be $2K-1$.
    have h_least : ∀ m, m < 2 * K - 1 → ValidMove lam (play (aliceReferenceStrategy lam K) bazza) m := by
      -- Since $m < 2K-1$, we have either $m < 2K-2$ or $m = 2K-2$. In both cases, $ValidMove$ holds by $h_bazza_wins$.
      intros m hm
      by_cases hm' : m < 2 * K - 2;
      · exact h_bazza_wins m hm';
      · convert lemAliceMoveValid lam hlam K hK bazza _;
        · omega;
        · exact h_bazza_wins;
    refine' ⟨ _, fun m hm => _ ⟩ <;> aesop;
    · unfold ValidMove at a;
      rcases K with ( _ | K ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
      unfold q at h_alice_wins;
      erw [ Finset.sum_Ico_succ_top ] at a <;> norm_num at *;
      exact h_alice_wins.not_le ( by norm_num [ ← NNReal.coe_le_coe ] at *; nlinarith );
    · exact not_lt.1 fun contra => hm <| h_least m <| by omega;
  · exact ⟨ K - 1, by omega ⟩

/-
Alice wins if $\lambda > 1 / \sqrt{2}$. Bazza wins if $0 < \lambda < 1 / \sqrt{2}$.
-/
theorem main_theorem :
  {lam : ℝ | 0 < lam ∧ ∃ alice : AliceStrategy, alice.Wins lam} = {lam : ℝ | 1 / Real.sqrt 2 < lam} ∧
  {lam : ℝ | 0 < lam ∧ ∃ bazza : BazzaStrategy, bazza.Wins lam} = {lam : ℝ | 0 < lam ∧ lam < 1 / Real.sqrt 2} := by
  constructor;
  · apply Set.ext;
    bound;
    · cases a ; aesop;
      -- By definition of Alice's winning strategy, if Alice has a winning strategy, then x must be greater than 1/sqrt(2).
      have h_x_gt : x > 1 / Real.sqrt 2 := by
        have := h bazzaReferenceStrategy;
        -- By definition of Alice's winning strategy, if Alice has a winning strategy, then there exists some $n$ where the move is invalid and $n$ is odd.
        obtain ⟨n, hn₁, hn₂⟩ := this;
        -- By definition of ValidMove, if the move is invalid, then for odd n, the sum of squares exceeds n+1.
        have h_sum_squares : ∑ i in Finset.range n, (play w bazzaReferenceStrategy i : ℝ) ^ 2 > n + 1 := by
          have := hn₁.1;
          unfold ValidMove at this;
          aesop;
          · exact absurd h_1 ( by simpa using hn₂ );
          · contrapose! this;
            erw [ Finset.sum_Ico_succ_top ] <;> norm_num;
            rw [ ← NNReal.coe_le_coe ] ; aesop;
            rw [ show play w bazzaReferenceStrategy n = bazzaReferenceStrategy ( n / 2 ) ( fun i => play w bazzaReferenceStrategy i ) from ?_ ];
            · unfold bazzaReferenceStrategy;
              norm_num [ ← NNReal.coe_le_coe ];
              split_ifs;
              · norm_num [ ← NNReal.coe_le_coe, Finset.sum_range ];
                rw [ Real.sq_sqrt ];
                · rw [ show n = 2 * ( n / 2 ) + 1 by linarith [ Nat.odd_iff.mp hn₂, Nat.div_add_mod n 2 ] ];
                  norm_num [ Nat.add_div ];
                  rw [ show ( 2 * ( n / 2 ) + 1 ) / 2 = n / 2 by omega ] ; linarith;
                · linarith;
              · convert this using 1;
                unfold bazzaReferenceStrategy;
                norm_num;
            · unfold play;
              norm_num [ Nat.odd_iff.mp hn₂ ];
              congr!;
              exact?;
        -- Since $n$ is odd, we can write $n = 2k + 1$ for some $k$.
        obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := hn₂;
        -- By definition of play, we can write out the sum of squares for the first 2k+1 turns.
        have h_play_sum_squares : ∑ i in Finset.range (2 * k + 1), (play w bazzaReferenceStrategy i : ℝ) ^ 2 ≤ 2 * k + (play w bazzaReferenceStrategy (2 * k) : ℝ) ^ 2 := by
          -- By definition of ValidMove, the sum of squares up to 2k is ≤ 2k.
          have h_sum_squares_2k : ∑ i in Finset.range (2 * k), (play w bazzaReferenceStrategy i : ℝ) ^ 2 ≤ 2 * k := by
            have := hn₁.2;
            have := @this ( 2 * k ) ; unfold ValidMove at this ; aesop;
            have := @this_1 ( 2 * k ) ; unfold ValidMove at this ; aesop;
            have := @this_1 ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
            unfold ValidMove at this ; aesop;
            convert NNReal.coe_le_coe.mpr this using 1;
            · erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num;
            · norm_cast;
          rw [ Finset.sum_range_succ ] ; linarith;
        have h_play_sum_squares : play w bazzaReferenceStrategy (2 * k) ≤ x * (2 * k + 1) - ∑ i in Finset.range (2 * k), (play w bazzaReferenceStrategy i : ℝ) := by
          have := hn₁.2;
          have := @this ( 2 * k ) ; unfold ValidMove at this ; aesop;
          erw [ Finset.sum_Ico_succ_top ] at this <;> norm_num at *;
          linarith;
        have h_play_sum_squares : ∑ i in Finset.range (2 * k), (play w bazzaReferenceStrategy i : ℝ) ≥ k * Real.sqrt 2 := by
          have := @lemSLowerBound x w ( k + 1 ) ( by linarith ) ?_;
          · aesop;
          · intro m hm;
            have := hn₁.2;
            exact Classical.not_not.1 fun hnm => not_lt_of_ge ( this hnm ) ( by omega );
        simp +zetaDelta at *;
        -- By combining the terms, we can factor out $\sqrt{2}$ and simplify the expression.
        have h_simplified : Real.sqrt 2 < x * (2 * k + 1) - k * Real.sqrt 2 := by
          nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( play w bazzaReferenceStrategy ( 2 * k ) : ℝ ) ≥ 0 by positivity ];
        rw [ inv_eq_one_div, div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
      simpa using h_x_gt;
    · exact ⟨ lt_trans ( by positivity ) a, lemAliceWinsLargeLambda x a ⟩;
  · -- To prove the equality, we show mutual inclusion.
    apply Set.ext
    intro lam;
    constructor;
    · -- If there exists a bazza strategy that wins, then by the problem's statement, lam must be less than 1/sqrt(2).
      intro h
      obtain ⟨bazza, hbazza⟩ := h.right
      have hlam : 0 < lam ∧ lam < 1 / Real.sqrt 2 := by
        specialize hbazza ( fun n x => 0 );
        aesop;
        unfold ValidMove at *;
        have := left_1.1 ; aesop;
        contrapose! this;
        -- Since $w$ is even, we can write $w = 2k$ for some $k$.
        obtain ⟨k, rfl⟩ : ∃ k, w = 2 * k := even_iff_two_dvd.mp right;
        -- By definition of play, we can write out the sum.
        have h_sum : ∑ i in Finset.Iic (2 * k), (play (fun n x => 0) bazza i : ℝ) = ∑ i in Finset.range k, (play (fun n x => 0) bazza (2 * i + 1) : ℝ) := by
          erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, Nat.mul_succ ];
          rw [ show ( Finset.range ( 2 * k ) : Finset ℕ ) = Finset.image ( fun i => 2 * i ) ( Finset.range k ) ∪ Finset.image ( fun i => 2 * i + 1 ) ( Finset.range k ) from ?_, Finset.sum_union ] <;> norm_num;
          · unfold play;
            norm_num;
          · norm_num [ Finset.disjoint_right ];
            intros; omega;
          · ext ; aesop;
            · rcases Nat.even_or_odd' a with ⟨ b, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ b, by linarith, rfl ⟩;
            · linarith;
        -- By definition of play, we can write out the sum of squares.
        have h_sum_squares : ∑ i in Finset.range k, (play (fun n x => 0) bazza (2 * i + 1) : ℝ) ^ 2 ≤ 2 * k := by
          have := left_1.2;
          have := @this ( 2 * k - 1 ) ; rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ Nat.mul_succ, parity_simps ];
          convert NNReal.coe_le_coe.mpr this using 1;
          · erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ Finset.sum_range_succ, Nat.mul_succ ];
            unfold play;
            exact Nat.recOn k ( by norm_num ) fun n ihn => by norm_num [ Nat.mul_succ, Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod ] at * ; linarith;
          · norm_cast;
        have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range k ) => pow_two_nonneg ( ( play ( fun n x => 0 ) bazza ( 2 * i + 1 ) : ℝ ) - Real.sqrt 2 );
        norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] at this;
        norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
        rw [ inv_eq_one_div, div_le_iff₀ ] at * <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]
      exact hlam;
    · exact fun h => ⟨ h.1, lemBazzaWinsSmallLambda lam h ⟩

#print axioms main_theorem
