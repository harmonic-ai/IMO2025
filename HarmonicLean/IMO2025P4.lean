/-
A proper divisor of a positive integer $N$ is a positive divisor of $N$ other than $N$ itself.
The infinite sequence $a_1,a_2,\dots$ consists of positive integers, each of which has at least three proper divisors.
For each $n\geqslant 1$, the integer $a_{n+1}$ is the sum of the three largest proper divisors of $a_n$.
Determine all possible values of $a_1$.
Answer: All integers of the form $6 \cdot 12^a \cdot m$, for $a \geq 0$ and $m$ is coprime to 10.
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

namespace IMO2025P4

/-
Let $N$ be a positive integer with at least three proper divisors. Let its positive divisors in ascending order be $1=c_1 < c_2 < c_3 < c_4 < \dots$. The three largest proper divisors of $N$ are $N/c_2, N/c_3, N/c_4$. We define the function $S(N)$ as the sum of these three divisors: $S(N) = \frac{N}{c_2} + \frac{N}{c_3} + \frac{N}{c_4}$. The sequence in the problem is defined by $a_{n+1} = S(a_n)$.
-/
def S (N : ℕ) : ℕ :=
  let largestProperDivisors := (Nat.properDivisors N).sort (· ≥ ·)
  largestProperDivisors[0]! + largestProperDivisors[1]! + largestProperDivisors[2]!

/-
For a positive integer $N$ satisfying the conditions in Definition~\ref{def:sequence_function}, we define the ratio $R(N) = \frac{S(N)}{N} = \frac{1}{c_2} + \frac{1}{c_3} + \frac{1}{c_4}$. The sequence recurrence can be written as $a_{n+1} = a_n R(a_n)$.
-/
def R (N : ℕ) : ℚ :=
  (S N : ℚ) / (N : ℚ)

/-
For a positive integer $N$, let $c_k(N)$ denote its $k$-th smallest positive divisor. So $c_1(N)=1 < c_2(N) < c_3(N) < \dots$. We will write $c_k$ when $N$ is clear from the context. The condition that $N$ has at least three proper divisors means its total number of divisors, $\tau(N)$, is at least 4. This guarantees the existence of $c_4$.
-/
def c_k (k N : ℕ) : ℕ :=
  ((Nat.divisors N).sort (· ≤ ·))[k-1]!

-- A helper definition for the properties of the sequence `a`
def IsSequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧
  (∀ n, 3 ≤ (Nat.properDivisors (a n)).card) ∧
  (∀ n, a (n+1) = S (a n))

/-
If $a_n$ is an odd integer, then $a_{n+1}$ is also an odd integer.
-/
lemma lem_odd_successor_is_odd (a_n : ℕ) : Odd a_n → 3 ≤ (Nat.properDivisors a_n).card → Odd (S a_n) := by
  aesop;
  -- Since $a_n$ is odd, all its proper divisors are also odd.
  have h_proper_divisors_odd : ∀ d ∈ ((Nat.properDivisors a_n).sort (· ≥ ·)), Odd d := by
    aesop;
    -- Since $a_n$ is odd, any divisor $d$ of $a_n$ must also be odd. This is because if $d$ were even, then $a_n$ would be even, contradicting the assumption that $a_n$ is odd.
    exact a.of_dvd_nat left;
  -- Since $a_n$ is odd, the sum of its three largest proper divisors is also odd.
  have h_sum_odd : Odd ((Finset.sort (· ≥ ·) (Nat.properDivisors a_n))[0]! + (Finset.sort (· ≥ ·) (Nat.properDivisors a_n))[1]! + (Finset.sort (· ≥ ·) (Nat.properDivisors a_n))[2]!) := by
    rcases n : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) a_n.properDivisors with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | hz ⟩ ⟩ ⟩ ; simp_all +arith +decide;
    · replace n := congr_arg List.length n; aesop;
      interval_cases a_n <;> contradiction;
    · -- Since the cardinality of the proper divisors is at least 3, the sorted list cannot be [x].
      have h_card : (Finset.sort (fun x1 x2 => x1 ≥ x2) a_n.properDivisors).length ≥ 3 := by
        simpa using a_1;
      grind;
    · replace n := congr_arg List.length n; aesop;
    · -- Since $x$, $y$, and $z$ are all odd, their sum $x + y + z$ is also odd.
      have h_odd_sum : Odd x ∧ Odd y ∧ Odd z := by
        aesop;
      simp_all ( config := { decide := Bool.true } ) [ parity_simps ];
      exact iff_of_false ( by simpa using h_odd_sum.2.1 ) ( by simpa using h_odd_sum.2.2 );
    · simp_all ( config := { decide := Bool.true } ) [ parity_simps ];
      exact iff_of_false ( by simpa using h_proper_divisors_odd.2.1 ) ( by simpa using h_proper_divisors_odd.2.2.1 );
  exact h_sum_odd

/-
If a term $a_k$ in the sequence is odd, then all subsequent terms $a_n$ for $n \ge k$ are odd.
-/
lemma lem_odd_implies_all_odd (a : ℕ → ℕ) (k : ℕ) : IsSequence a → Odd (a k) → ∀ n, k ≤ n → Odd (a n) := by
  -- We proceed by induction on $n$.
  intro h_seq h_odd_k n hn
  induction' hn with n ih;
  · assumption;
  · cases h_seq ; aesop;
    exact?

/-
For an odd integer $N$ with at least three proper divisors, $R(N) < 1$.
-/
lemma lem_ratio_for_odd (N : ℕ) : Odd N → 3 ≤ (Nat.properDivisors N).card → R N < 1 := by
  -- By Lemma~\ref{lem:odd_successor_divisors}, all divisors of $N$ are odd.
  intros h_odd h_card
  have h_divisors_odd : ∀ d, d ∈ Nat.properDivisors N → Odd d := by
    exact fun d hd => h_odd.of_dvd_nat <| Nat.mem_properDivisors.mp hd |>.1;
  unfold R;
  rw [ div_lt_iff₀ ] <;> norm_cast;
  · -- Let $d_1$, $d_2$, and $d_3$ be the three largest proper divisors of $N$. Then $d_1 \leq N/3$, $d_2 \leq N/3$, and $d_3 \leq N/3$.
    obtain ⟨d1, d2, d3, hd1, hd2, hd3, hd_sum⟩ : ∃ d1 d2 d3, d1 ∈ Nat.properDivisors N ∧ d2 ∈ Nat.properDivisors N ∧ d3 ∈ Nat.properDivisors N ∧ d1 > d2 ∧ d2 > d3 ∧ d1 + d2 + d3 = S N := by
      unfold S;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors with _ | ⟨ d1, _ | ⟨ d2, _ | ⟨ d3, _ | k ⟩ ⟩ ⟩ ; aesop;
      · replace x := congr_arg List.length x; aesop;
        interval_cases N <;> contradiction;
      · replace x := congr_arg List.length x; aesop;
      · replace x := congr_arg List.length x; aesop;
      · -- Since the list is sorted in descending order, we have $d1 > d2$ and $d2 > d3$.
        have h_sorted : d1 > d2 ∧ d2 > d3 := by
          have := Finset.sort_sorted_gt N.properDivisors; aesop;
        exact ⟨ d1, d2, d3, by replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x d1; aesop, by replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x d2; aesop, by replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x d3; aesop, h_sorted.1, h_sorted.2, rfl ⟩;
      · have := Finset.sort_sorted ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors; aesop;
        -- Since $d1$, $d2$, and $d3$ are the three largest proper divisors of $N$, we have $d1 > d2 > d3$.
        have h_distinct : d1 > d2 ∧ d2 > d3 := by
          have h_distinct : d1 ≠ d2 ∧ d2 ≠ d3 := by
            have h_distinct : List.Nodup (d1 :: d2 :: d3 :: k :: tail) := by
              exact x ▸ Finset.sort_nodup _ _;
            aesop;
          exact ⟨ lt_of_le_of_ne left h_distinct.1.symm, lt_of_le_of_ne left_1 h_distinct.2.symm ⟩;
        exact ⟨ d1, ⟨ Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.1, Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.2 ⟩, d2, ⟨ Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.1, Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.2 ⟩, d3, ⟨ Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.1, Nat.mem_properDivisors.mp ( Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( by rw [ x ] ; simp ( config := { decide := Bool.true } ) ) ) |>.2 ⟩, by linarith, by linarith, rfl ⟩;
    -- Since $d_1$, $d_2$, and $d_3$ are the three largest proper divisors of $N$, each must be less than or equal to $N/3$.
    have hd1_le : d1 ≤ N / 3 := by
      -- Since $d1$ is a proper divisor of $N$, there exists some integer $k$ such that $N = d1 * k$ and $k > 1$.
      obtain ⟨k, hk⟩ : ∃ k, N = d1 * k ∧ 1 < k := by
        norm_num +zetaDelta at *;
        exact hd1.1.imp fun x hx => ⟨ by linarith, by nlinarith only [ hx, hd1.2 ] ⟩;
      rw [ Nat.le_div_iff_mul_le three_pos ] ; rcases k with ( _ | _ | _ | k ) <;> simp_all +arith +decide;
      · exact absurd h_odd ( by simp ( config := { decide := Bool.true } ) [ parity_simps ] );
      · nlinarith only [ hd1 ]
    have hd2_le : d2 ≤ N / 3 := by
      grind
    have hd3_le : d3 ≤ N / 3 := by
      grind;
    rw [ Nat.le_div_iff_mul_le three_pos ] at *;
    bound;
  · exact?

/-
If a term $a_k$ in the sequence is odd, the subsequence $(a_n)_{n \ge k}$ is strictly decreasing.
-/
lemma lem_odd_implies_decreasing (a : ℕ → ℕ) (k : ℕ) : IsSequence a → Odd (a k) → ∀ n ≥ k, a (n+1) < a n := by
  -- By definition of IsSequence, we know that R(a_n) < 1 for all n ≥ k.
  intros ha h_odd n hn
  have h_ratio : R (a n) < 1 := by
    -- Since $a_n$ is odd for all $n \geq k$, we can apply the lemma that states $R(N) < 1$ for any odd $N$ with at least three proper divisors.
    have h_odd_all : ∀ n ≥ k, Odd (a n) := by
      exact?;
    -- Apply the lemma that states $R(N) < 1$ for any odd $N$ with at least three proper divisors.
    apply lem_ratio_for_odd; exact h_odd_all n hn; exact ha.2.1 n;
  -- By definition of $R$, we know that $R(a_n) = \frac{S(a_n)}{a_n}$. Since $R(a_n) < 1$, multiplying both sides by $a_n$ (which is positive) gives $S(a_n) < a_n$.
  have h_S_lt_an : S (a n) < a n := by
    unfold R at h_ratio;
    rw [ div_lt_one ] at h_ratio <;> norm_cast at * ; linarith [ ha.1 n ];
  rw [ ha.2.2 ] ; aesop

/-
An infinite sequence as defined in the problem cannot contain any odd terms.
-/
lemma lem_no_odd_terms (a : ℕ → ℕ) : IsSequence a → ∀ k, Even (a k) := by
  -- Assume that there exists some k where a_k is odd.
  by_contra h_odd;
  -- Then there exists some k such that a_k is odd and the sequence a is an IsSequence.
  obtain ⟨k, hk_odd, ha_seq⟩ : ∃ k, Odd (a k) ∧ IsSequence a := by
    aesop;
  -- By Lemma~\ref{lem:odd_implies_decreasing}, the sequence of positive integers $(a_n)_{n \ge k}$ is strictly decreasing.
  have h_decreasing : ∀ n ≥ k, a (n + 1) < a n := by
    exact?;
  -- Apply the fact that a strictly decreasing sequence of positive integers must be finite.
  have h_finite : Set.Finite (Set.range (fun n => a (k + n))) := by
    -- Since the sequence $a$ is strictly decreasing starting from $k$, the values $a (k + n)$ are all distinct and decreasing. Therefore, the range of the function $n \mapsto a (k + n)$ is finite.
    have h_finite : ∀ n, a (k + n) ≥ a (k + (n + 1)) := by
      exact fun n => Nat.le_of_lt ( h_decreasing _ ( Nat.le_add_right _ _ ) );
    exact Set.finite_iff_bddAbove.mpr ⟨ a ( k + 0 ), by rintro x ⟨ n, rfl ⟩ ; exact Nat.recOn n ( by norm_num ) fun n ihn => by linarith! [ h_finite n ] ⟩;
  exact h_finite.not_infinite <| Set.infinite_range_of_injective ( StrictAnti.injective <| strictAnti_nat_of_succ_lt fun n => h_decreasing _ <| Nat.le_add_right _ _ )

/-
Every term $a_n$ in the sequence must be an even integer.
-/
lemma lem_all_terms_even (a : ℕ → ℕ) : IsSequence a → ∀ n, Even (a n) := by
  exact?

/-
For any term $a_n$ in the sequence, its second smallest divisor is $c_2(a_n)=2$.
-/
lemma lem_c2_is_2 (a : ℕ → ℕ) : IsSequence a → ∀ n, c_k 2 (a n) = 2 := by
  -- By Lemma~\ref{lem:all_terms_even}, each term $a_n$ is even. Therefore, $2$ is a divisor of $a_n$.
  have h_two_divisor (a : ℕ → ℕ) (n : ℕ) (ha : IsSequence a) : 2 ∈ Nat.divisors (a n) := by
    norm_num +zetaDelta at *;
    exact ⟨ even_iff_two_dvd.mp ( by exact? ), ne_of_gt ( ha.1 n ) ⟩;
  -- Since $a_n$ is even, its smallest divisor is $1$ and the next smallest divisor is $2$.
  have h_smallest_divisors (a : ℕ → ℕ) (n : ℕ) (ha : IsSequence a) : (Nat.divisors (a n)).sort (· ≤ ·) = 1 :: 2 :: (Nat.divisors (a n) \ {1, 2}).sort (· ≤ ·) := by
    -- Since the divisors are sorted in ascending order, the first element is 1, the second is 2, and the rest are the divisors greater than 2.
    have h_sorted : (Nat.divisors (a n)).sort (· ≤ ·) = (insert 1 (insert 2 ((Nat.divisors (a n)) \ {1, 2}))).sort (· ≤ ·) := by
      congr;
      ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> aesop;
    rw [ h_sorted, Finset.sort_insert, Finset.sort_insert ];
    · exact fun x hx => Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩;
    · aesop;
    · aesop;
      exact Nat.pos_of_dvd_of_pos left ( Nat.pos_of_ne_zero ( h_two_divisor a n ha |>.2 ) );
    · aesop;
  unfold c_k; aesop;

/-
A term $a_n$ is a fixed point, i.e., $a_{n+1}=a_n$, if and only if $R(a_n)=1$.
-/
lemma lem_fixed_point_condition (N : ℕ) : 0 < N → (S N = N ↔ R N = 1) := by
  unfold R;
  intro N; rw [ div_eq_iff ] ; norm_cast ; aesop;
  positivity

/-
An integer $N$ has smallest divisors $c_2=2, c_3=3, c_4=6$ if and only if it is divisible by 6, not divisible by 4, and not divisible by 5.
-/
lemma lem_structure_of_fixed_points (N : ℕ) : 0 < N → (Nat.divisors N).card ≥ 4 → ((c_k 2 N = 2 ∧ c_k 3 N = 3 ∧ c_k 4 N = 6) ↔ (6 ∣ N ∧ ¬ (4 ∣ N) ∧ ¬ (5 ∣ N))) := by
  bound;
  -- Since $N$ is divisible by 6, it must be divisible by both 2 and 3. Therefore, the smallest divisors after 1 are 2 and 3.
  have h_div_2_3 : 2 ∣ N ∧ 3 ∣ N := by
    unfold c_k at *;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ ) <;> aesop;
    · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 2; aesop;
    · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 3; aesop;
  exact Nat.lcm_dvd h_div_2_3.left h_div_2_3.right;
  · unfold c_k at *;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
    · have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
      have := this 1; have := this.symm; aesop;
      cases this_1 6 ; aesop;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
      have := n ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.2 ⟨ a_2, by linarith ⟩ ) ; aesop;
      linarith [ left_7 4 h_2 ];
  · unfold c_k at *;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
    · have := Finset.sort_sorted ( fun x1 x2 => x1 ≤ x2 ) N.divisors; aesop;
      interval_cases x <;> have := congr_arg List.toFinset n <;> norm_num [ Finset.ext_iff ] at this;
      · specialize this 0 ; aesop;
      · exact absurd ( this 5 ) ( by norm_num [ a_2, a.ne' ] );
      · have := this 1; aesop;
    · -- Since 5 is a divisor of N and the list is sorted, 5 must appear between 3 and 6 in the list.
      have h_five_in_list : 5 ∈ Finset.sort (fun x1 x2 => x1 ≤ x2) N.divisors := by
        exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.mpr ⟨ a_2, by linarith ⟩ );
      have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
      linarith [ left_7 5 h_2 ];
  · -- Since $N$ is divisible by 6, it is even, so 2 is a divisor. The smallest divisor is 1, so the next one must be 2.
    have h_divisors : 1 ∈ Nat.divisors N ∧ 2 ∈ Nat.divisors N ∧ ∀ d ∈ Nat.divisors N, 1 < d → d ≥ 2 := by
      exact ⟨ Nat.mem_divisors.mpr ⟨ one_dvd _, by linarith ⟩, Nat.mem_divisors.mpr ⟨ dvd_trans ( by decide ) left, by linarith ⟩, fun d hd hd' => hd' ⟩;
    -- Since the divisors are sorted in ascending order and 2 is the smallest divisor greater than 1, the second element in the sorted list of divisors must be 2.
    have h_sorted : (Nat.divisors N).sort (· ≤ ·) = 1 :: 2 :: (Nat.divisors N \ {1, 2}).sort (· ≤ ·) := by
      rw [ ← Finset.sort_insert ];
      · rw [ ← Finset.sort_insert ];
        · congr;
          ext d; by_cases hd1 : d = 1 <;> by_cases hd2 : d = 2 <;> aesop;
        · aesop;
          exact Nat.pos_of_dvd_of_pos left_2 a;
        · norm_num +zetaDelta at *;
      · exact fun d hd => h_divisors.2.2 d ( by aesop ) ( lt_of_le_of_ne ( Nat.pos_of_mem_divisors ( by aesop ) ) ( Ne.symm ( by aesop ) ) );
      · aesop;
    -- Since the list is sorted in ascending order, the second element is indeed 2.
    have h_second : ((Nat.divisors N).sort (· ≤ ·))[1]! = 2 := by
      aesop;
    exact h_second;
  · -- Since $N$ is divisible by 6, its divisors include 1, 2, 3, and 6. The next smallest divisor after 3 is 6, so the third smallest divisor is 3.
    have h_divisors : (Nat.divisors N).sort (· ≤ ·) = [1, 2, 3] ++ (Nat.divisors N \ {1, 2, 3}).sort (· ≤ ·) := by
      -- Since $N$ is divisible by 6, its divisors include 1, 2, 3, and 6. The next smallest divisor after 3 is 6, so the third smallest divisor is 3. Therefore, the sorted list of divisors of $N$ is [1, 2, 3] followed by the sorted list of divisors of $N$ excluding 1, 2, and 3.
      have h_divisors : (Nat.divisors N).sort (· ≤ ·) = (insert 1 (insert 2 (insert 3 ((Nat.divisors N) \ {1, 2, 3})))).sort (· ≤ ·) := by
        congr;
        ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> by_cases hx3 : x = 3 <;> aesop;
        · exact dvd_trans ( by norm_num ) left;
        · exact dvd_trans ( by norm_num ) left;
      rw [ h_divisors, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
      all_goals aesop;
      · contrapose! left_3; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
      · exact Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos left_2 a ) ( Ne.symm left_3 );
      · exact Nat.pos_of_dvd_of_pos left_2 a;
    -- Since the list of divisors is sorted in ascending order, the third element is the third smallest divisor.
    unfold c_k; aesop;
  · -- Since $N$ is divisible by 6, the divisors of $N$ include 1, 2, 3, and 6. We need to show that these are the four smallest divisors.
    have h_divisors : (Nat.divisors N).sort (· ≤ ·) = [1] ++ [2] ++ [3] ++ [6] ++ (Nat.divisors N \ {1, 2, 3, 6} : Finset ℕ).sort (· ≤ ·) := by
      have h_divisors : (Nat.divisors N).sort (· ≤ ·) = (insert 1 (insert 2 (insert 3 (insert 6 ((Nat.divisors N) \ {1, 2, 3, 6}))))).sort (· ≤ ·) := by
        congr;
        ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> by_cases hx3 : x = 3 <;> by_cases hx6 : x = 6 <;> aesop;
        · exact dvd_trans ( by norm_num ) left;
        · exact dvd_trans ( by norm_num ) left;
      rw [ h_divisors, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
      all_goals simp_all ( config := { decide := Bool.true } ) [ Finset.mem_insert, Finset.mem_singleton ];
      · intro b hb _ hb1 hb2 hb3 hb6; contrapose! hb1; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
      · intro a ha _ ha1 ha2 ha3 ha6; contrapose! ha1; interval_cases a <;> simp_all ( config := { decide := Bool.true } ) ;
      · exact fun a ha _ ha1 ha2 ha3 ha6 => Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos ha ‹_› ) ( Ne.symm ha1 );
      · bound;
        exact Nat.pos_of_dvd_of_pos a_3 a;
    unfold c_k;
    aesop

/-
For any term $a_n$ in the sequence, the ratio is $R(a_n) = \frac{1}{2} + \frac{1}{c_3(a_n)} + \frac{1}{c_4(a_n)}$.
-/
lemma lem_ratio_for_even (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → R N = (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) := by
  unfold R c_k;
  unfold S;
  rcases N <;> aesop;
  -- Let's simplify the expression for the ratio $R$.
  have h_divisors : (Nat.divisors (Nat.succ n)).sort (· ≤ ·) = 1 :: 2 :: ((Nat.divisors (Nat.succ n)).erase 1 |>.erase 2).sort (· ≤ ·) := by
    have h_divisors : (Nat.divisors (Nat.succ n)).sort (· ≤ ·) = (insert 1 (insert 2 ((Nat.divisors (Nat.succ n)).erase 1 |>.erase 2))).sort (· ≤ ·) := by
      congr;
      ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> aesop;
      exact even_iff_two_dvd.mp a;
    rw [ h_divisors, Finset.sort_insert, Finset.sort_insert ];
    · exact fun x hx => Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩;
    · aesop;
    · field_simp;
      exact fun a ha₁ ha₂ ha₃ => Nat.pos_of_dvd_of_pos ha₃ ( Nat.succ_pos _ );
    · aesop;
  have h_divisors_rev : (Nat.divisors (Nat.succ n)).sort (· ≥ ·) = (List.map (fun d => Nat.succ n / d) ((Nat.divisors (Nat.succ n)).sort (· ≤ ·))) := by
    have h_divisors_rev : (Nat.divisors (Nat.succ n)).sort (· ≥ ·) = (List.map (fun d => Nat.succ n / d) ((Nat.divisors (Nat.succ n)).sort (· ≤ ·))) := by
      have h_divisors_rev_aux : ∀ {l : List ℕ}, (∀ d ∈ l, d ∣ Nat.succ n) → List.Sorted (· ≤ ·) l → List.Sorted (· ≥ ·) (List.map (fun d => Nat.succ n / d) l) := by
        intros l hl_div hl_sorted; induction hl_sorted <;> aesop;
        exact Nat.div_le_div_left ( a_3 _ a_6 ) ( Nat.pos_of_dvd_of_pos left ( Nat.succ_pos _ ) )
      have h_divisors_rev_aux : List.Perm (List.map (fun d => Nat.succ n / d) ((Nat.divisors (Nat.succ n)).sort (· ≤ ·))) ((Nat.divisors (Nat.succ n)).sort (· ≥ ·)) := by
        rw [ List.perm_iff_count ];
        intro x; rw [ List.count_eq_of_nodup, List.count_eq_of_nodup ];
        · simp +zetaDelta at *;
          bound;
          · exact False.elim <| h <| Nat.div_dvd_of_dvd left;
          · exact False.elim <| h ⟨ ( n + 1 ) / x, Nat.div_dvd_of_dvd h_1, by rw [ Nat.div_div_self h_1 <| by aesop ] ⟩;
        · exact Finset.sort_nodup _ _;
        · rw [ List.nodup_map_iff_inj_on ];
          · norm_num +zetaDelta at *;
            intro x hx y hy hxy; have := Nat.div_mul_cancel hx; have := Nat.div_mul_cancel hy; aesop;
            nlinarith;
          · exact Finset.sort_nodup _ _;
      aesop;
      have h_sorted : List.Sorted (· ≥ ·) ((n + 1) :: (n + 1) / 2 :: List.map (fun d => Nat.succ n / d) (Finset.sort (fun x1 x2 => x1 ≤ x2) (((n + 1).divisors.erase 1).erase 2))) := by
        simp +zetaDelta at *;
        exact ⟨ ⟨ Nat.div_le_self _ _, fun a x hx₁ hx₂ hx₃ hx₄ => hx₄ ▸ Nat.div_le_self _ _ ⟩, fun b x hx₁ hx₂ hx₃ hx₄ => hx₄ ▸ Nat.div_le_div_left ( show x ≥ 2 from Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos hx₃ ( Nat.succ_pos _ ) ) ( Ne.symm hx₂ ) ) ( by decide ), h_divisors_rev_aux_1 ( fun x hx => Nat.dvd_of_mem_divisors <| Finset.mem_of_mem_erase <| Finset.mem_of_mem_erase <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 hx ) <| Finset.sort_sorted ( · ≤ · ) _ ⟩;
      exact List.eq_of_perm_of_sorted h_divisors_rev_aux.symm ( Finset.sort_sorted ( fun x1 x2 => x2 ≤ x1 ) _ ) h_sorted;
    exact h_divisors_rev;
  -- Let's substitute the sorted list of divisors into the expression for $R$.
  have h_divisors_erase : (Nat.properDivisors (Nat.succ n)).sort (· ≥ ·) = (List.map (fun d => Nat.succ n / d) ((Nat.divisors (Nat.succ n)).sort (· ≤ ·))).tail := by
    rw [ ← h_divisors_rev ];
    rw [ ← Nat.cons_self_properDivisors ] <;> aesop;
    rw [ Finset.sort_insert ] ; aesop;
    · exact fun x hx => Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.mem_properDivisors.mp hx |>.1 );
    · aesop;
  aesop;
  rcases k : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( ( Nat.divisors ( n + 1 ) ).erase 1 |> Finset.erase <| 2 ) with _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ; aesop;
  · rw [ inv_eq_one_div, div_eq_div_iff ] <;> norm_cast <;> linarith [ Nat.div_mul_cancel ( even_iff_two_dvd.mp a ) ];
  · replace h_divisors := congr_arg List.length h_divisors ; aesop;
    rw [ ← Nat.cons_self_properDivisors ] at h_divisors <;> aesop;
  · -- Let's simplify the expression for the ratio $R$ in the case where there are at least three proper divisors.
    field_simp;
    rw [ Nat.cast_div, Nat.cast_div, Nat.cast_div ] <;> norm_num <;> ring;
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k b; aesop;
      rwa [ add_comm ];
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k a; aesop;
      rwa [ add_comm ];
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
    · simpa [ ← even_iff_two_dvd, parity_simps ] using ‹Even ( n + 1 ) ›

/-
If $R(N)>1$ for an even number $N$ with $c_3(N)=3$, then $c_4(N)$ must be 4 or 5.
-/
lemma lem_growth_condition (N : ℕ) : Even N → c_k 3 N = 3 → R N > 1 → c_k 4 N = 4 ∨ c_k 4 N = 5 := by
  -- Since $c_k 3 N = 3$, we have $R N = \frac{1}{2} + \frac{1}{3} + \frac{1}{c_k 4 N}$.
  intro h_even h_c3 h_r
  have h_r_eq : R N = (1 : ℚ) / 2 + 1 / 3 + 1 / (c_k 4 N) := by
    rw [ lem_ratio_for_even ] <;> aesop;
    -- Since $N$ is even, it has at least the proper divisors $1$, $2$, and $N/2$.
    have h_divisors : Nat.properDivisors N ⊇ {1, 2, N / 2} := by
      simp ( config := { decide := Bool.true } ) [ Finset.insert_subset_iff ];
      rcases N with ( _ | _ | _ | N ) <;> simp_all +arith +decide;
      · exact absurd h_c3 ( by native_decide );
      · exact absurd h_r ( by native_decide );
      · exact ⟨ by obtain ⟨ k, hk ⟩ := h_even; omega, Nat.div_dvd_of_dvd <| even_iff_two_dvd.mp h_even, by obtain ⟨ k, hk ⟩ := h_even; omega ⟩;
    -- Since {1, 2, N/2} is a subset of the proper divisors of N and these three elements are distinct, the cardinality of the proper divisors must be at least 3.
    have h_card : ({1, 2, N / 2} : Finset ℕ).card ≤ (Nat.properDivisors N).card := by
      exact Finset.card_le_card h_divisors;
    rcases N with ( _ | _ | _ | _ | _ | _ | N ) <;> simp_all +arith +decide;
    · exact absurd h_r ( by native_decide );
    · exact le_trans ( by rw [ Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem ] <;> norm_num <;> omega ) h_card;
  rcases n : c_k 4 N with ( _ | _ | _ | _ | _ | _ | c_k4N ) <;> simp_all ( config := { decide := Bool.true } );
  · norm_num at *;
  · unfold c_k at *;
    rcases x : Finset.sort ( fun x x_1 => x ≤ x_1 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | k ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
    · have := x ▸ Finset.sort_sorted ( · ≤ · ) N.divisors; simp_all ( config := { decide := Bool.true } ) ;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
  · unfold c_k at *;
    rcases k : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ ) <;> aesop;
    · have := k ▸ Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
  · unfold c_k at * ; aesop;
    rcases k : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
    · have := k ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
    · have := k ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
  · -- By simplifying the inequality $1 < 2⁻¹ + 3⁻¹ + (c_k4N + 6)⁻¹$, we can derive a contradiction.
    field_simp at h_r;
    rw [ lt_div_iff₀ ] at h_r <;> linarith

/-
If $c_3(a_n) \ge 4$, then $R(a_n) < 1$.
-/
lemma lem_decreasing_condition (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → c_k 3 N ≥ 4 → R N < 1 := by
  -- By Lemma~\ref{lem:ratio_for_even}, $R(N) = \frac{1}{2} + \frac{1}{c_3} + \frac{1}{c_4}$.
  intro h_even h_card h_c3
  have h_ratio : R N = (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) := by
    exact?;
  -- Since $c_k 4 N > c_k 3 N$, we have $c_k 4 N \geq c_k 3 N + 1$.
  have h_c4 : c_k 4 N ≥ c_k 3 N + 1 := by
    -- Since the list of divisors is sorted in ascending order and there are at least four divisors, the fourth element must be strictly greater than the third.
    have h_sorted : ∀ {l : List ℕ}, List.Sorted (· ≤ ·) l → List.Nodup l → 4 ≤ l.length → l[3]! > l[2]! := by
      aesop;
      rcases l with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | l ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
      · omega;
      · grind;
    have h_sorted : List.Sorted (· ≤ ·) ((Nat.divisors N).sort (· ≤ ·)) ∧ List.Nodup ((Nat.divisors N).sort (· ≤ ·)) ∧ 4 ≤ ((Nat.divisors N).sort (· ≤ ·)).length := by
      rw [ ← Nat.cons_self_properDivisors ] <;> aesop;
    unfold c_k; aesop;
  rw [ h_ratio, div_add_div, div_add_div, div_lt_iff₀ ] <;> norm_cast <;> nlinarith only [ h_c3, h_c4 ]

/-
If an even integer $N$ has $v_3(N)=0$ and $v_3(S(N))>0$, then $c_3(N) \equiv 2 \pmod 3$ and $c_4(N) \equiv 2 \pmod 3$.
-/
lemma lem_v3_transition_condition (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → padicValNat 3 N = 0 → 0 < padicValNat 3 (S N) → c_k 3 N % 3 = 2 ∧ c_k 4 N % 3 = 2 := by
  -- Since $N$ is even and $v_3(N) = 0$, $N$ is not divisible by 3. However, $S(N)$ is divisible by 3 because $v_3(S(N)) > 0$.
  intro h_even h_card h_v3N h_v3SN
  have h_not_div3 : ¬(3 ∣ N) := by
    -- Since the p-adic valuation of 3 for N is zero, 3 does not divide N.
    simp [padicValNat] at h_v3N;
    exact h_v3N ( Nat.pos_of_ne_zero ( by aesop_cat ) );
  -- Since $S(N)$ is divisible by 3, we have $S(N) = N * R(N)$ and $R(N) = \frac{1}{2} + \frac{1}{c_3} + \frac{1}{c_4}$.
  have h_RN_div3 : 3 ∣ (c_k 3 N) * (c_k 4 N) + 2 * (c_k 4 N) + 2 * (c_k 3 N) := by
    have h_RN_div3 : 3 ∣ (N * (c_k 3 N * c_k 4 N + 2 * c_k 4 N + 2 * c_k 3 N)) := by
      have h_RN_div3 : S N = N * (1 / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) : ℚ) := by
        have h_ratio : R N = (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) := by
          exact?;
        rw [ ← h_ratio ];
        unfold R;
        rw [ mul_div_cancel₀ _ ( by aesop ) ];
      have h_RN_div3 : (S N : ℚ) * 2 * (c_k 3 N) * (c_k 4 N) = N * ((c_k 3 N) * (c_k 4 N) + 2 * (c_k 4 N) + 2 * (c_k 3 N)) := by
        by_cases h : c_k 3 N = 0 <;> by_cases h' : c_k 4 N = 0 <;> simp_all ( config := { decide := Bool.true } ) [ -one_div, field_simps ] ; ring;
        · unfold c_k at h;
          rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> aesop;
          · replace n := congr_arg List.length n; aesop;
          · replace n := congr_arg List.length n; aesop;
            exact absurd n ( Nat.ne_of_gt ( Finset.one_lt_card.mpr ⟨ 1, by aesop_cat, by aesop_cat ⟩ ) );
          · have := congr_arg List.length n; norm_num at this;
            exact absurd this ( by linarith [ show Finset.card ( Nat.properDivisors N ) + 1 = Finset.card ( Nat.divisors N ) by rw [ ← Nat.insert_self_properDivisors ] <;> aesop ] );
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
        · unfold c_k at *;
          rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
          · have y := congr_arg List.length x; norm_num at y;
            rw [ ← Nat.cons_self_properDivisors ] at y <;> aesop;
          · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
          · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
        · linear_combination h_RN_div3;
      norm_cast at *;
      exact h_RN_div3 ▸ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by contrapose! h_v3SN; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ) _ ) _ ) _;
    exact Or.resolve_left ( Nat.prime_three.dvd_mul.mp h_RN_div3 ) h_not_div3;
  -- Since $c_3$ and $c_4$ are not divisible by 3, their residues modulo 3 must be 1 or 2.
  have h_c3_mod3 : (c_k 3 N) % 3 ≠ 0 := by
    have h_c3_div3 : c_k 3 N ∣ N := by
      unfold c_k;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | h ⟩ ⟩ ⟩ ) <;> aesop;
      · replace x := congr_arg List.length x; aesop;
      · replace x := congr_arg List.length x; aesop;
        exact absurd x ( Nat.ne_of_gt ( Finset.one_lt_card_iff.mpr ⟨ 1, by aesop_cat, by aesop_cat ⟩ ) );
      · replace x := congr_arg List.length x; aesop;
        rw [ ← Nat.cons_self_properDivisors ] at x <;> aesop;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x c; aesop;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x c; aesop;
    exact fun h => h_not_div3 <| dvd_trans ( Nat.dvd_of_mod_eq_zero h ) h_c3_div3
  have h_c4_mod3 : (c_k 4 N) % 3 ≠ 0 := by
    intro h; simp_all ( config := { decide := Bool.true } ) [ Nat.dvd_iff_mod_eq_zero ] ;
    simp_all ( config := { decide := Bool.true } ) [ Nat.add_mod, Nat.mul_mod ];
    have := Nat.mod_lt ( c_k 3 N ) three_pos; interval_cases c_k 3 N % 3 <;> contradiction;
  have := Nat.mod_lt ( c_k 3 N ) zero_lt_three; ( have := Nat.mod_lt ( c_k 4 N ) zero_lt_three; interval_cases _ : c_k 3 N % 3 <;> interval_cases _ : c_k 4 N % 3 <;> simp_all ( config := { decide := Bool.true } ) [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod ] ; )

/-
If $a_n$ is a term in an infinite sequence with $c_2=2, c_3=3, c_4=5$, then $a_{n+1}$ is odd.
-/
lemma lem_growth_c4_is_5_impossible (a_n : ℕ) : IsSequence (fun n => if n=0 then a_n else S^[n] a_n) → c_k 2 a_n = 2 → c_k 3 a_n = 3 → c_k 4 a_n = 5 → Odd (S a_n) := by
  aesop;
  -- The conditions $c_2=2, c_3=3, c_4=5$ imply $v_2(a_n)=1, v_3(a_n)\ge 1, v_5(a_n)\ge 1$.
  have h_v2 : a_n % 2 = 0 ∧ a_n % 4 ≠ 0 := by
    -- Since $c_k 2 a_n = 2$, we know that $2$ is the second smallest divisor of $a_n$, implying $a_n$ is even.
    have h_even : a_n % 2 = 0 := by
      have := lem_all_terms_even ( fun n => if n = 0 then a_n else S^[n] a_n ) a 0 ; aesop;
      -- Since $a_n$ is even, we have $a_n \equiv 0 \pmod{2}$.
      exact Nat.even_iff.mp this;
    unfold c_k at * ; aesop;
    rcases k : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) a_n.divisors ) with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ ) <;> aesop;
    · replace k := congr_arg List.toFinset k ; rw [ Finset.ext_iff ] at k ; have := k 4 ; simp_all ( config := { decide := Bool.true } );
      have := k 1; have := k 2; have := k 3; have := k 4; have := k 5; have := k a; have := k a_n; have := k ( a_n / 4 ) ; have := k ( a_n / 2 ) ; have := k ( a_n / 3 ) ; have := k ( a_n / 5 ) ; norm_num at * ; aesop;
    · have := k ▸ Finset.sort_sorted ( · ≤ · ) a_n.divisors; aesop;
      have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.2 ⟨ Nat.dvd_of_mod_eq_zero a_4, by aesop ⟩ ) ; aesop;
      linarith [ left_7 4 h_2 ];
  -- Using Definition~\ref{def:sequence_function}, $a_{n+1} = a_n R(a_n)$. The exponent of 2 in this result is $v_2(a_{n+1}) = v_2(a_n) + v_2(R(a_n))$.
  have h_exp : S a_n = a_n * (31 / 30 : ℚ) := by
    -- By Lemma~\ref{lem:ratio_for_even}, $R(a_n) = \frac{1}{2} + \frac{1}{3} + \frac{1}{5} = \frac{31}{30}$.
    have h_ratio : R a_n = (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 5 := by
      rw [ lem_ratio_for_even ];
      · aesop;
      · exact Nat.even_iff.mpr h_v2.1;
      · have := a.2.1 0; aesop;
    unfold R at h_ratio;
    rw [ div_eq_iff ] at h_ratio <;> first |linarith|aesop;
  -- Since $a_n$ is divisible by 2 but not by 4, we have $v_2(a_n) = 1$. Therefore, $v_2(a_{n+1}) = v_2(a_n) + v_2(31/30) = 1 + 0 - 1 = 0$.
  have h_v2_a_n_plus_1 : (S a_n) % 2 = 1 := by
    rw [ mul_div, eq_div_iff ] at h_exp <;> norm_cast at *;
    grind;
  exact Nat.odd_iff.mpr h_v2_a_n_plus_1

/-
If an even integer $N$ has $v_3(N)=0$ and $v_3(S(N))>0$, then $v_2(N)=1$.
-/
lemma lem_v3_transition_v2_is_1 (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → padicValNat 3 N = 0 → 0 < padicValNat 3 (S N) → padicValNat 2 N = 1 := by
  aesop;
  -- If $v_2(N) \geq 2$, then $4$ is a divisor of $N$. Since $v_3(N) = 0$, $3$ is not a divisor of $N$. Therefore, the smallest divisor of $N$ greater than $2$ is $4$, so $c_3(N) = 4$.
  by_cases h_v2 : padicValNat 2 N ≥ 2;
  · -- Since $v_2(N) \geq 2$, $4$ is a divisor of $N$. Since $v_3(N) = 0$, $3$ is not a divisor of $N$. Therefore, the smallest divisor of $N$ greater than $2$ is $4$, so $c_3(N) = 4$.
    have h_c3 : c_k 3 N = 4 := by
      -- Since $v_2(N) \geq 2$, $4$ is a divisor of $N$. Since $v_3(N) = 0$, $3$ is not a divisor of $N$. Therefore, the smallest divisor of $N$ greater than $2$ is $4$, so $c_3(N) = 4$ and $c_4(N) = 5$.
      have h_divisors : (Nat.divisors N).sort (· ≤ ·) = [1, 2, 4] ++ (Nat.divisors N \ {1, 2, 4}).sort (· ≤ ·) := by
        have h_divisors : (Nat.divisors N).sort (· ≤ ·) = (insert 1 (insert 2 (insert 4 (Nat.divisors N \ {1, 2, 4})))).sort (· ≤ ·) := by
          congr;
          -- Since $N$ is even and has at least three proper divisors, $1$, $2$, and $4$ are all divisors of $N$.
          have h_divisors : 1 ∈ Nat.divisors N ∧ 2 ∈ Nat.divisors N ∧ 4 ∈ Nat.divisors N := by
            aesop;
            · exact even_iff_two_dvd.mp a;
            · exact dvd_trans ( pow_dvd_pow 2 h_v2 ) ( Nat.ordProj_dvd _ _ );
          ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> by_cases hx4 : x = 4 <;> aesop;
        rw [ h_divisors, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
        all_goals simp_all ( config := { decide := Bool.true } );
        · intro b hb _ hb1 hb2 hb4; contrapose! hb1; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
        · exact fun a ha _ ha1 ha2 ha4 => Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos ha ( Nat.pos_of_ne_zero ‹_› ) ) ( Ne.symm ha1 );
        · exact fun a ha _ _ _ _ => Nat.pos_of_dvd_of_pos ha ( Nat.pos_of_ne_zero ‹_› );
      unfold c_k;
      aesop;
    -- By Lemma~\ref{lem:v3_transition_condition}, this implies $c_3(N) \equiv 2 \pmod 3$.
    have h_c3_mod : c_k 3 N % 3 = 2 := by
      -- Since $c_k 3 N = 4$, we have $4 \mod 3 = 1$, which contradicts the lemma that $c_k 3 N \equiv 2 \pmod{3}$. Therefore, our assumption that $c_k 3 N = 4$ must be incorrect.
      have h_contra : c_k 3 N % 3 = 2 := by
        have h_lemma : padicValNat 3 N = 0 → 0 < padicValNat 3 (S N) → c_k 3 N % 3 = 2 := by
          intros; exact lem_v3_transition_condition N a a_1 ‹_› ‹_› |>.1;
        exact h_lemma (by
        exact padicValNat.eq_zero_of_not_dvd h_1) (by
        assumption);
      exact h_contra;
    norm_num [ h_c3 ] at h_c3_mod;
  · interval_cases _ : padicValNat 2 N <;> simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_iff ];
    -- Since $N$ is even, we have $2 \mid N$, which contradicts $h_1$.
    have h_contra : 2 ∣ N := by
      -- Since $N$ is even, we have $2 \mid N$ by definition.
      exact even_iff_two_dvd.mp a;
    grind

/-
If $N$ is a fixed point (i.e., $R(N)=1$), then its smallest divisors are $c_2(N)=2, c_3(N)=3, c_4(N)=6$.
-/
lemma lem_fixed_point_divisors (N : ℕ) : S N = N → 3 ≤ (Nat.properDivisors N).card → c_k 2 N = 2 ∧ c_k 3 N = 3 ∧ c_k 4 N = 6 := by
  -- By Lemma~\ref{lem:ratio_for_even}, this becomes $\frac{1}{2} + \frac{1}{c_3} + \frac{1}{c_4} = 1$, which simplifies to $\frac{1}{c_3} + \frac{1}{c_4} = \frac{1}{2}$.
  intro h_fixed_point h_card
  have h_ratio : (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) = 1 := by
    have h_ratio : R N = (1 : ℚ) / 2 + 1 / (c_k 3 N) + 1 / (c_k 4 N) := by
      apply lem_ratio_for_even;
      · contrapose! h_fixed_point;
        -- Since $N$ is odd, by Lemma~\ref{lem:ratio_for_odd}, we have $R(N) < 1$.
        have h_ratio_lt_one : R N < 1 := by
          exact lem_ratio_for_odd N ( by simpa using h_fixed_point ) h_card;
        unfold R at h_ratio_lt_one;
        rw [ div_lt_one ] at h_ratio_lt_one <;> norm_cast at * ; aesop;
        exact Nat.pos_of_ne_zero ( by rintro rfl; contradiction );
      · assumption;
    rw [ ← h_ratio, show R N = 1 from by rw [ show R N = ( S N : ℚ ) / N by exact rfl ] ; rw [ h_fixed_point, div_self ] ; aesop ];
  have h_c3 : c_k 3 N = 3 := by
    -- Since $c_3 < c_4$, we have $\frac{1}{c_3} > \frac{1}{c_4}$, so $\frac{2}{c_3} > \frac{1}{c_3} + \frac{1}{c_4} = \frac{1}{2}$, which implies $c_3 < 4$.
    have h_c3_lt_4 : c_k 3 N < 4 := by
      contrapose h_ratio;
      -- Since $c_k 3 N \geq 4$, we have $c_k 4 N \geq c_k 3 N + 1$.
      have h_c4_ge_c3_plus_1 : c_k 4 N ≥ c_k 3 N + 1 := by
        -- Since the divisors are sorted in ascending order and distinct, the fourth divisor must be greater than the third.
        have h_sorted : ∀ {l : List ℕ}, List.Sorted (· ≤ ·) l → List.Nodup l → ∀ i j : ℕ, i < j → i < List.length l → j < List.length l → l.get! i < l.get! j := by
          intros l hl_sorted hl_nodup i j hij hi hj;
          field_simp;
          have := List.pairwise_iff_get.mp hl_sorted;
          exact lt_of_le_of_ne ( this ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij ) fun h => by have := List.nodup_iff_injective_get.mp hl_nodup; have := @this ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; aesop;
        have h_sorted_divisors : List.Sorted (· ≤ ·) ((Nat.divisors N).sort (· ≤ ·)) ∧ List.Nodup ((Nat.divisors N).sort (· ≤ ·)) := by
          exact ⟨ Finset.sort_sorted _ _, Finset.sort_nodup _ _ ⟩;
        have := @h_sorted _ h_sorted_divisors.left h_sorted_divisors.right 2 3 ( by decide ) ?_ ?_ <;> aesop;
        · unfold c_k; aesop;
        · rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
          linarith;
        · rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
          linarith;
      rw [ div_add_div, div_add_div, div_eq_iff ] <;> norm_cast <;> nlinarith only [ h_ratio, h_c4_ge_c3_plus_1 ];
    interval_cases _ : c_k 3 N <;> simp_all ( config := { decide := Bool.true } );
    · unfold c_k at *;
      rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> aesop;
      replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
    · linarith [ inv_pos.mpr ( show 0 < ( c_k 4 N : ℚ ) by norm_cast; contrapose! h_ratio; aesop ) ];
    · norm_num at h_ratio;
      unfold c_k at *;
      rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | ⟨ g, _ | h ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ <;> aesop;
      all_goals replace := Finset.sort_sorted ( fun x1 x2 => x1 ≤ x2 ) N.divisors; simp_all ( config := { decide := Bool.true } );
      have := congr_arg List.length n; norm_num at this;
      rw [ ← Nat.cons_self_properDivisors ] at this <;> aesop;
  aesop;
  · unfold c_k at *;
    rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ ; aesop;
    · aesop;
    · have := congr_arg List.length n; norm_num at this;
      rw [ ← Nat.cons_self_properDivisors ] at this <;> aesop;
    · aesop;
      norm_num at h_ratio;
    · have := Finset.sort_sorted ( fun x1 x2 => x1 ≤ x2 ) N.divisors; aesop;
      -- Since $a \leq b \leq 3$ and $a \leq d$, and the list is sorted, we deduce that $a = 1$ and $b = 2$.
      have ha : a = 1 := by
        interval_cases a <;> simp_all ( config := { decide := Bool.true } );
        · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
        · have := Nat.mem_divisors_self N ( by aesop_cat ) ; replace n := congr_arg List.toFinset n ; rw [ Finset.ext_iff ] at n ; specialize n 1 ; aesop;
        · interval_cases b ; norm_num at *;
          have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
          have := this 1; aesop;
          linarith [ this.mp ( by rintro rfl; contradiction ) ];
      interval_cases b <;> simp_all ( config := { decide := Bool.true } );
      · have := n ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
      · have := n ▸ Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) N.divisors; aesop;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
      interval_cases b <;> interval_cases a <;> norm_num at *;
      all_goals have := n ▸ Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) N.divisors; simp_all ( config := { decide := Bool.true } ) ;
      replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
  · exact_mod_cast ( by nlinarith [ inv_mul_cancel₀ ( show ( c_k 4 N : ℚ ) ≠ 0 from fun h => by norm_num [ h ] at h_ratio ) ] : ( c_k 4 N : ℚ ) = 6 )

/-
An integer $N$ is a fixed point if and only if $N$ is of the form $6m$ for some positive integer $m$ with $\gcd(m,10)=1$.
-/
lemma lem_fixed_point_form (N : ℕ) : (S N = N ∧ 3 ≤ (Nat.properDivisors N).card) ↔ ∃ m, 0 < m ∧ Nat.Coprime m 10 ∧ N = 6 * m := by
  constructor;
  · intro h;
    -- By Lemma~\ref{lem:fixed_point_divisors}, its smallest divisors are $c_2(N)=2$, $c_3(N)=3$, and $c_4(N)=6$.
    have h_divisors : c_k 2 N = 2 ∧ c_k 3 N = 3 ∧ c_k 4 N = 6 := by
      -- By Lemma~\ref{lem:fixed_point_divisors}, if $S(N) = N$ and $N$ has at least three proper divisors, then the smallest divisors of $N$ are $2$, $3$, and $6$.
      apply lem_fixed_point_divisors; exact h.left; exact h.right;
    -- This requires that $N$ be divisible by 6, not divisible by 4, and not divisible by 5.
    have h_div_conditions : 6 ∣ N ∧ ¬(4 ∣ N) ∧ ¬(5 ∣ N) := by
      have := lem_structure_of_fixed_points N;
      rcases N with ( _ | _ | N ) <;> simp_all +arith +decide;
      exact this ( by rw [ ← Nat.cons_self_properDivisors ] <;> aesop );
    rcases h_div_conditions.1 with ⟨ m, rfl ⟩;
    exact ⟨ m, Nat.pos_of_ne_zero ( by aesop_cat ), Nat.Coprime.symm <| Nat.Coprime.gcd_eq_one <| Nat.Coprime.mul ( show Nat.Coprime 2 m from Nat.prime_two.coprime_iff_not_dvd.2 fun contra => h_div_conditions.2.1 <| dvd_trans ( by decide ) ( mul_dvd_mul_left _ contra ) ) ( show Nat.Coprime 5 m from Nat.Prime.coprime_iff_not_dvd ( by decide ) |>.2 fun contra => h_div_conditions.2.2 <| dvd_trans ( by decide ) ( mul_dvd_mul_left _ contra ) ), rfl ⟩;
  · bound;
    · -- The three largest proper divisors of $6w$ are $3w$, $2w$, and $w$. Their sum is $3w + 2w + w = 6w$.
      have h_divisors : (Nat.properDivisors (6 * w)).sort (· ≥ ·) = [3 * w, 2 * w, w] ++ (Nat.properDivisors (6 * w) \ {3 * w, 2 * w, w}).sort (· ≥ ·) := by
        norm_num +zetaDelta at *;
        rw [ ← Finset.sort_insert ];
        · rw [ ← Finset.sort_insert ];
          · rw [ ← Finset.sort_insert ];
            · congr with x ; aesop;
              · grind;
              · exact ⟨ 2, by ring ⟩;
              · exact ⟨ 3, by ring ⟩;
            · aesop;
              obtain ⟨ k, hk ⟩ := left_2;
              rcases k with ( _ | _ | _ | _ | _ | k ) <;> nlinarith;
            · aesop;
              linarith;
          · aesop;
            obtain ⟨ k, hk ⟩ := left_2;
            rcases k with ( _ | _ | _ | _ | _ | k ) <;> simp_all! +arith +decide;
            · omega;
            · omega;
            · omega;
            · nlinarith;
          · aesop;
            linarith;
        · aesop;
          obtain ⟨ k, hk ⟩ := left_2;
          rcases k with ( _ | _ | _ | _ | _ | k ) <;> simp_all! +arith +decide;
          · omega;
          · omega;
          · exact absurd ( Nat.dvd_gcd ( show 2 ∣ w by omega ) ( show 2 ∣ 10 by decide ) ) ( by norm_num [ left_1 ] );
          · rcases k with ( _ | _ | k ) <;> try nlinarith;
            exact absurd ( Nat.dvd_gcd ( show 5 ∣ w by omega ) ( show 5 ∣ 10 by norm_num ) ) ( by aesop );
        · aesop;
      unfold S;
      simp +arith +decide [ h_divisors ];
    · -- Since $w$ is coprime to 10, the proper divisors of $6w$ include at least $1$, $2$, and $3$.
      have h_divisors : Nat.properDivisors (6 * w) ⊇ {1, 2, 3} := by
        simp ( config := { decide := Bool.true } ) [ Finset.insert_subset_iff ];
        -- Since $w$ is a positive integer, $6w$ is clearly greater than $1$, $2$, and $3$.
        have h_ineq : 1 < 6 * w ∧ 2 < 6 * w ∧ 3 < 6 * w := by
          exact ⟨ by linarith, by linarith, by linarith ⟩;
        exact ⟨ h_ineq.1, ⟨ ⟨ 3 * w, by ring ⟩, h_ineq.2.1 ⟩, ⟨ ⟨ 2 * w, by ring ⟩, h_ineq.2.2 ⟩ ⟩;
      exact Finset.card_mono h_divisors

/-
Any integer $N$ of the form $6 \cdot 12^a \cdot m$ with $a \ge 0$ and $\gcd(m,10)=1$ is a valid starting term $a_1$.
-/
lemma lem_verification_of_form :
  { n | ∃ a m, m > 0 ∧ Nat.Coprime m 10 ∧ n = 6 * 12 ^ a * m } ⊆ { a₁ | ∃ a : ℕ → ℕ, IsSequence a ∧ a₁ = a 0 } := by
    -- From Lemma 2, we know that if $a_1 = 6 \cdot 12^a \cdot m$, then $a_{n+1} = \frac{13}{12} a_n$ for $n \leq a$.
    have h_step : ∀ a m : ℕ, 0 < m → Nat.Coprime m 10 → IsSequence (fun n => if n ≤ a then 6 * 12 ^ (a - n) * m * 13 ^ n else 6 * m * 13 ^ a) := by
      intros a m hm h_coprime;
      constructor;
      · aesop;
      · constructor;
        · intro n;
          norm_num +zetaDelta at *;
          split_ifs;
          · refine' Finset.two_lt_card.mpr _;
            simp;
            exact ⟨ 1, ⟨ one_dvd _, by nlinarith [ show 12 ^ ( a - n ) * m * 13 ^ n > 0 by positivity ] ⟩, 2, ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by norm_num ) _ ) _ ) _, by nlinarith [ show 12 ^ ( a - n ) * m * 13 ^ n > 0 by positivity ] ⟩, 3, ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by norm_num ) _ ) _ ) _, by nlinarith [ show 12 ^ ( a - n ) * m * 13 ^ n > 0 by positivity ] ⟩, by norm_num, by norm_num, by norm_num ⟩;
          · refine' le_trans _ ( Finset.card_mono <| show Nat.properDivisors ( 6 * m * 13 ^ a ) ≥ { 1, 2, 3 } from _ );
            · native_decide +revert;
            · norm_num [ Finset.insert_subset_iff ];
              exact ⟨ by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ], ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ] ⟩, dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ] ⟩;
        · aesop;
          · rw [ show a - n = ( a - ( n + 1 ) ) + 1 by omega ] ; ring;
            unfold S;
            -- The largest proper divisors of $m \cdot 12^{a-(1+n)} \cdot 13^n \cdot 72$ are $m \cdot 12^{a-(1+n)} \cdot 13^n \cdot 36$, $m \cdot 12^{a-(1+n)} \cdot 13^n \cdot 24$, and $m \cdot 12^{a-(1+n)} \cdot 13^n \cdot 18$.
            have h_divisors : (Nat.properDivisors (m * 12 ^ (a - (1 + n)) * 13 ^ n * 72)).sort (· ≥ ·) = [m * 12 ^ (a - (1 + n)) * 13 ^ n * 36, m * 12 ^ (a - (1 + n)) * 13 ^ n * 24, m * 12 ^ (a - (1 + n)) * 13 ^ n * 18] ++ (Finset.sort (· ≥ ·) (Finset.filter (fun d => d < m * 12 ^ (a - (1 + n)) * 13 ^ n * 18) (Nat.properDivisors (m * 12 ^ (a - (1 + n)) * 13 ^ n * 72)))) := by
              have h_divisors : (Nat.properDivisors (m * 12 ^ (a - (1 + n)) * 13 ^ n * 72)).sort (· ≥ ·) = (insert (m * 12 ^ (a - (1 + n)) * 13 ^ n * 36) (insert (m * 12 ^ (a - (1 + n)) * 13 ^ n * 24) (insert (m * 12 ^ (a - (1 + n)) * 13 ^ n * 18) (Finset.filter (fun d => d < m * 12 ^ (a - (1 + n)) * 13 ^ n * 18) (Nat.properDivisors (m * 12 ^ (a - (1 + n)) * 13 ^ n * 72)))))).sort (· ≥ ·) := by
                congr;
                ext; aesop;
                · rcases left with ⟨ k, hk ⟩;
                  rcases k with ( _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> norm_num at * <;> first | exact Or.inl <| by nlinarith | exact Or.inr <| Or.inl <| by nlinarith | exact Or.inr <| Or.inr <| Or.inl <| by nlinarith | exact Or.inr <| Or.inr <| Or.inr <| by nlinarith;
                · exact ⟨ 2, by ring ⟩;
                · exact mul_dvd_mul_left _ ( by decide );
                · exact mul_dvd_mul_left _ ( by decide );
              rw [ h_divisors, Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
              all_goals simp +arith +decide;
              · intros; linarith;
              · intros; linarith;
              · linarith;
              · intros; linarith;
              · linarith;
            aesop;
            ring;
          · linarith;
          · cases h_1.eq_or_lt <;> first | linarith | aesop;
            -- By definition of $S$, we know that $S(6 \cdot m \cdot 13^n) = 6 \cdot m \cdot 13^n$ since $6 \cdot m \cdot 13^n$ is a fixed point.
            have h_fixed_point : S (6 * m * 13 ^ n) = 6 * m * 13 ^ n := by
              have h_fixed_point : ∀ m : ℕ, 0 < m → Nat.Coprime m 10 → S (6 * m) = 6 * m := by
                exact fun m hm h_coprime => lem_fixed_point_form ( 6 * m ) |>.2 ⟨ m, hm, h_coprime, rfl ⟩ |>.1;
              simpa only [ mul_assoc ] using h_fixed_point ( m * 13 ^ n ) ( by positivity ) ( by exact Nat.Coprime.mul h_coprime ( by cases n <;> norm_num ) );
            exact h_fixed_point.symm;
          · -- By definition of $S$, we know that $S(6 * m * 13^a) = 6 * m * 13^a$ since $6 * m * 13^a$ is a fixed point.
            have h_fixed_point : S (6 * m * 13 ^ a) = 6 * m * 13 ^ a := by
              have h_form : ∃ m', 0 < m' ∧ Nat.Coprime m' 10 ∧ 6 * m * 13 ^ a = 6 * m' := by
                exact ⟨ m * 13 ^ a, by positivity, by exact Nat.Coprime.mul h_coprime ( by exact Nat.Coprime.pow_left _ ( by decide ) ), by ring ⟩
              aesop;
              exact lem_fixed_point_form _ |>.2 ⟨ w, left, left_1, rfl ⟩ |>.1;
            exact h_fixed_point.symm;
    rintro _ ⟨ a, m, hm, hm', rfl ⟩;
    exact ⟨ _, h_step a m hm hm', by simp ( config := { decide := Bool.true } ) ⟩

/-
If an even integer $N$ has $v_2(N)=1$, $v_3(N)=0$, and $v_3(S(N))>0$, then its divisors $c_3(N)$ and $c_4(N)$ are both odd.
-/
lemma lem_v3_transition_c3_c4_are_odd (N : ℕ) : padicValNat 2 N = 1 → padicValNat 3 N = 0 → 0 < padicValNat 3 (S N) → 3 ≤ (Nat.properDivisors N).card → Odd (c_k 3 N) ∧ Odd (c_k 4 N) := by
  intro h2 h3 h4 h5;
  -- Since $c_k 3 N$ and $c_k 4 N$ are both $\equiv 2 \pmod 3$, they must be odd.
  have h_odd_c3 : Odd (c_k 3 N) := by
    -- Since $v_2(N)=1$, $N$ is divisible by 2 but not by 4. Thus, the smallest divisor greater than 2 must be odd.
    have h_c3_odd : c_k 3 N ∉ ({1, 2} : Finset ℕ) := by
      unfold c_k; aesop;
      · rcases n : Finset.sort ( · ≤ · ) N.divisors with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
        · replace n := congr_arg List.length n ; simp_all +arith +decide;
          rw [ ← Nat.cons_self_properDivisors ] at n <;> aesop;
        · have := Finset.sort_sorted ( · ≤ · ) N.divisors; simp_all ( config := { decide := Bool.true } ) ;
          rcases x with ( _ | _ | x ) <;> rcases y with ( _ | _ | y ) <;> simp_all +arith +decide;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
          · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
          · have := n ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
      · rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | h ⟩ ⟩ ⟩ ) <;> aesop;
        · have := congr_arg List.length n; norm_num at this;
          rw [ ← Nat.cons_self_properDivisors ] at this <;> aesop;
        · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
          interval_cases x <;> interval_cases y <;> simp_all ( config := { decide := Bool.true } );
          all_goals have := n ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; simp_all ( config := { decide := Bool.true } );
          replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
    rcases k : ( Nat.divisors N |> Finset.sort ( · ≤ · ) ) with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ ) <;> aesop;
    · replace k := congr_arg List.length k; aesop;
    · replace k := congr_arg List.length k; aesop;
      exact absurd k ( by exact Nat.ne_of_gt ( Finset.one_lt_card_iff.mpr ⟨ 1, by aesop_cat, by aesop_cat ⟩ ) );
    · replace k := congr_arg List.length k; aesop;
      rw [ ← Nat.cons_self_properDivisors ] at k <;> aesop;
    · have := congr_arg List.length k; norm_num at this;
      rw [ ← Nat.cons_self_properDivisors ] at this <;> aesop;
    · have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors N ) ; aesop;
      unfold c_k at *;
      have := k ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors N ) ; simp_all +arith +decide;
      have ha : a = 1 := by
        have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.one_mem_divisors.2 <| by aesop_cat ) ; aesop;
        · interval_cases a <;> aesop;
          replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
        · interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all ( config := { decide := Bool.true } ) only;
        · grind;
      have hb : b = 2 := by
        have hb : b ≤ 2 := by
          have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.2 ⟨ show 2 ∣ N from ?_, by aesop ⟩ ) ; aesop;
          · exact ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] );
          · aesop;
        interval_cases b <;> simp_all ( config := { decide := Bool.true } );
      have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( Nat.mem_divisors.2 ⟨ Nat.dvd_of_mem_divisors ( show c ∈ Nat.divisors N from by { replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k c; aesop } ), by { aesop } ⟩ ) ; aesop;
      contrapose! right_8;
      have h_even_divisor : c / 2 ∈ Nat.divisors N := by
        have h_even_divisor : c / 2 ∣ N := by
          exact Nat.dvd_trans ( Nat.div_dvd_of_dvd <| even_iff_two_dvd.mp <| by simpa using right_8 ) <| Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| k.symm ▸ by simp ( config := { decide := Bool.true } ) ;
        aesop;
      have := k ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 h_even_divisor; aesop;
      · have := Nat.div_mul_cancel ( even_iff_two_dvd.mp right_8 ) ; aesop;
      · have := Nat.div_mul_cancel ( even_iff_two_dvd.mp right_8 ) ; aesop;
        replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 4; aesop;
        rw [ padicValNat ] at h2 ; aesop;
        simp_all ( config := { decide := Bool.true } ) [ Nat.find_eq_iff ];
      · linarith [ Nat.div_mul_cancel ( even_iff_two_dvd.mp right_8 ) ];
      · omega;
      · grind
  have h_odd_c4 : Odd (c_k 4 N) := by
    -- By Lemma~\ref{lem:v3_transition_condition}, $c_3 \equiv 2 \pmod 3$ and $c_4 \equiv 2 \pmod 3$.
    have h_c3_c4_mod3 : c_k 3 N % 3 = 2 ∧ c_k 4 N % 3 = 2 := by
      apply_rules [ lem_v3_transition_condition ];
      exact even_iff_two_dvd.mpr ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] );
    unfold c_k at *;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    · have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
      -- Since $N$ is even, $2$ is a divisor of $N$. The divisors of $N$ in ascending order are $1, 2, c, d$. Since $c$ is the smallest odd divisor greater than $2$, $d$ must be greater than $c$ and cannot be $4$ (as $4$ would imply $v_2(N) \geq 2$, contradicting $v_2(N) = 1$). Therefore, $d$ must be odd.
      have h_d_odd : d > c ∧ ¬(4 ∣ N) := by
        have h_d_odd : d > c := by
          have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
          cases lt_or_eq_of_le right_1 <;> aesop;
          have := Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) N.divisors; aesop;
        rw [ padicValNat ] at h2 ; aesop;
        simp_all ( config := { decide := Bool.true } ) [ Nat.find_eq_iff ];
      cases this 1 ; cases this 2 ; cases this c ; cases this d ; aesop;
      · have := this 2; norm_num at this;
        cases this.mp ( dvd_trans ( by norm_num ) ( Nat.dvd_of_mod_eq_zero ( show N % 2 = 0 from Nat.mod_eq_zero_of_dvd <| by exact ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ) ) ) ) <;> aesop;
        · have := this_1 d; specialize this_1 ( d / 2 ) ; rcases Nat.even_or_odd' d with ⟨ k, rfl | rfl ⟩ <;> simp_all +arith +decide;
          rcases k with ( _ | _ | _ | k ) <;> simp_all +arith +decide;
          · interval_cases c <;> trivial;
          · exact absurd ( this_1.mp ( dvd_of_mul_left_dvd this ) ) ( by omega );
        · contradiction;
        · interval_cases c <;> trivial;
      · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
        interval_cases a <;> simp_all ( config := { decide := Bool.true } );
        · specialize this_1 0 ; aesop;
        · have := this_1 2; norm_num at this;
          cases this.mp ( dvd_trans ( by decide ) ( Nat.dvd_of_mod_eq_zero ( show N % 2 = 0 from Nat.mod_eq_zero_of_dvd <| by exact ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ) ) ) ) <;> aesop;
          · contradiction;
          · interval_cases c ; trivial;
    · have := Finset.sort_sorted ( · ≤ · ) N.divisors; aesop;
      -- Since $d$ is a divisor of $N$ and $N$ is even, but $c_k 3 N = 2$ (the smallest even divisor), $d$ must be odd.
      have h_d_odd : ¬(2 ∣ d) := by
        contrapose! left_4;
        cases left_4 ; aesop;
        have := n ▸ Finset.sort_nodup ( · ≤ · ) N.divisors; aesop;
        -- Since $c$ is the third smallest divisor and $N$ is even, $c$ must be greater than 2.
        have hc_gt_2 : 2 < c := by
          -- Since $c$ is a divisor of $N$ and $N$ is even, $c$ must be greater than 2.
          have hc_gt_2 : c ≠ 2 := by
            simp +zetaDelta at *;
            exact fun h => by simp_all ( config := { decide := Bool.true } ) [ Nat.even_iff ] ;
          exact lt_of_le_of_ne ( Nat.le_of_not_lt fun h => by interval_cases c <;> simp_all ( config := { decide := Bool.true } ) ) ( Ne.symm hc_gt_2 );
        -- Since $a \leq b \leq c$ and $a \neq b$, we have $b \geq a + 1$. Similarly, since $b \leq c$ and $b \neq c$, we have $c \geq b + 1$. Therefore, $c \geq a + 2$.
        have hc_ge_a2 : c ≥ a + 2 := by
          omega;
        have := congr_arg List.toFinset n; norm_num [ Finset.ext_iff ] at this;
        have := this 2; norm_num at this;
        cases this.mp ⟨ by exact Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.dvd_iff_mod_eq_zero ] ; exact ( by contrapose! h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ) ), by aesop ⟩ <;> aesop;
        · cases this_1 ( 1 : ℕ ) ; aesop;
          grind;
        · interval_cases a <;> simp_all ( config := { decide := Bool.true } );
          · specialize this_1 0 ; aesop;
          · have := this_1 ( 2 * w ) ; specialize this_1 w ; aesop;
            rcases w with ( _ | _ | w ) <;> simp_all +arith +decide;
            -- Since $w + 2$ divides $N$ and $w + 2 \notin \text{tail}$, we must have $w = 0$ or $w + 2 = c$ or $w + 2 = k$.
            have h_w_cases : w = 0 ∨ w + 2 = c ∨ w + 2 = k := by
              -- Since $w + 2$ divides $N$ and $w + 2 \notin \text{tail}$, we must have $w = 0$ or $w + 2 = c$ or $w + 2 = k$ by the hypothesis `this_1`.
              have h_w_cases : w = 0 ∨ w + 2 = c ∨ w + 2 = k ∨ w + 2 ∈ tail := by
                exact this_1.mp ( dvd_of_mul_left_dvd left_1 );
              grind;
            rcases h_w_cases with ( rfl | h_w_cases | h_w_cases ) <;> simp_all +arith +decide;
            · omega;
            · bound;
        · linarith;
        · grind;
      norm_num +zetaDelta at *;
      exact Nat.odd_iff.mpr h_d_odd
  exact ⟨h_odd_c3, h_odd_c4⟩

/-
If $N$ is an even integer with $v_3(N)=0$ such that $S(N)$ is divisible by 3, then $S(N)$ is odd.
-/
lemma lem_transition_to_v3_positive_is_odd (N : ℕ) : Even N → 3 ≤ (Nat.properDivisors N).card → padicValNat 3 N = 0 → 3 ∣ S N → Odd (S N) := by
  -- By Lemma~\ref{lem:v3_transition_v2_is_1}, the hypotheses imply $v_2(N)=1$.
  intro h_even h_card h_v3 h_div3
  have h_v2 : padicValNat 2 N = 1 := by
    apply_rules [ lem_v3_transition_v2_is_1 ];
    contrapose! h_v3; aesop;
    unfold S at h_v3;
    rcases x : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> aesop;
    · replace x := congr_arg List.length x; aesop;
      interval_cases N <;> trivial;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
  -- Since $c_3(N)$ and $c_4(N)$ are divisible by 3, we have $c_3(N) = 4$ or $c_3(N) = 5$.
  have h_c3 : Odd (c_k 3 N) ∧ Odd (c_k 4 N) := by
    apply_rules [ lem_v3_transition_c3_c4_are_odd ];
    unfold padicValNat; aesop;
    unfold S at h;
    rcases x : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    · replace x := congr_arg List.length x; aesop;
      interval_cases N <;> trivial;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
  -- By definition of $S$, we know that $S(N) = \frac{N}{c_2} + \frac{N}{c_3} + \frac{N}{c_4}$.
  have h_S_def : S N = N / c_k 2 N + N / c_k 3 N + N / c_k 4 N := by
    unfold S;
    -- The three largest proper divisors of $N$ are $N/2$, $N/3$, and $N/4$.
    have h_largest_divisors : (Nat.properDivisors N).sort (· ≥ ·) = (List.map (fun d => N / d) ((Nat.divisors N).sort (· ≤ ·))).drop 1 := by
      have h_largest_divisors : List.map (fun d => N / d) ((Nat.divisors N).sort (· ≤ ·)) = N.divisors.sort (· ≥ ·) := by
        have h_largest_divisors : List.Perm (List.map (fun d => N / d) ((Nat.divisors N).sort (· ≤ ·))) (Finset.sort (· ≥ ·) (Nat.divisors N)) := by
          rw [ List.perm_iff_count ];
          intro a; rw [ List.count_eq_of_nodup, List.count_eq_of_nodup ];
          · simp;
            bound;
            · exact False.elim <| h ⟨ Nat.div_dvd_of_dvd left_1, right_2 ⟩;
            · exact False.elim <| h ⟨ N / a, ⟨ Nat.div_dvd_of_dvd left_1, right_1 ⟩, by rw [ Nat.div_div_self ] <;> aesop ⟩;
          · exact Finset.sort_nodup _ _;
          · rw [ List.nodup_map_iff_inj_on ];
            · aesop;
              exact?;
            · exact Finset.sort_nodup _ _;
        have h_sorted : List.Sorted (· ≥ ·) (List.map (fun d => N / d) ((Nat.divisors N).sort (· ≤ ·))) := by
          have h_sorted : ∀ {l : List ℕ}, List.Sorted (· ≤ ·) l → (∀ d ∈ l, d ∣ N) → List.Sorted (· ≥ ·) (List.map (fun d => N / d) l) := by
            intros l hl_sorted hl_div; induction hl_sorted <;> aesop;
            exact Nat.div_le_div_left ( a_1 _ a_4 ) ( Nat.pos_of_dvd_of_pos left_1 ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
          exact h_sorted ( Finset.sort_sorted ( · ≤ · ) _ ) fun x hx => Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 hx;
        exact List.eq_of_perm_of_sorted h_largest_divisors h_sorted ( Finset.sort_sorted ( fun x1 x2 => x1 ≥ x2 ) _ );
      have h_largest_divisors : N.divisors.sort (· ≥ ·) = N :: N.properDivisors.sort (· ≥ ·) := by
        rw [ ← Nat.cons_self_properDivisors ];
        · rw [ Finset.sort_cons ];
          exact fun x hx => Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.mem_properDivisors.mp hx |>.1 );
        · aesop;
      aesop;
    unfold c_k; aesop;
    rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
  -- Since $c_k 2 N = 2$, we have $N / c_k 2 N = N / 2$, which is odd because $N$ is even and $v2(N) = 1$.
  have h_N_div_2_odd : Odd (N / c_k 2 N) := by
    have h_c2 : c_k 2 N = 2 := by
      -- Since $N$ is even, its smallest divisor greater than 1 is 2.
      have h_divisors_order : (Nat.divisors N).sort (· ≤ ·) = 1 :: 2 :: (Nat.divisors N \ {1, 2}).sort (· ≤ ·) := by
        rw [ ← Finset.sort_insert ];
        · rw [ ← Finset.sort_insert ];
          · congr;
            ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> aesop;
            exact even_iff_two_dvd.mp h_even;
          · aesop;
            exact Nat.pos_of_dvd_of_pos left_1 ( Nat.pos_of_ne_zero right_2 );
          · aesop;
        · exact fun x hx => Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by aesop_cat, by aesop_cat ⟩;
        · aesop;
      unfold c_k; aesop;
    rw [ padicValNat ] at h_v2;
    split_ifs at h_v2 ; simp_all ( config := { decide := Bool.true } ) [ Nat.find_eq_iff ];
    exact Nat.odd_iff.mpr ( by omega );
  have := Nat.div_mul_cancel ( show c_k 3 N ∣ N from Nat.dvd_of_mem_divisors <| by
    unfold c_k at *;
    rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x c; aesop; ) ; have := Nat.div_mul_cancel ( show c_k 4 N ∣ N from Nat.dvd_of_mem_divisors <| by
    -- Since $c_k 4 N$ is the fourth smallest divisor of $N$, it must be a divisor of $N$.
    have h_c4_div : c_k 4 N ∈ (Nat.divisors N).sort (· ≤ ·) := by
      unfold c_k;
      -- Since the list is sorted in ascending order, the fourth element is indeed a divisor of N.
      have h_div : (Finset.sort (· ≤ ·) (Nat.divisors N)).length ≥ 4 := by
        rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
      rcases n : Finset.sort ( · ≤ · ) N.divisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | k ⟩ ⟩ ⟩ ⟩ <;> aesop;
    exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 h_c4_div ) ; replace := congr_arg Even this; simp_all ( config := { decide := Bool.true } ) [ parity_simps ] ;
  aesop;
  · replace this_1 := congr_arg Even this_1; simp_all ( config := { decide := Bool.true } ) [ parity_simps ] ;
    exact this_1.resolve_right ( by simpa using left );
  · exact absurd h_2 ( by simpa using right );
  · exact absurd h_2 ( by simpa using right )

/-
An infinite sequence cannot have a term $a_k$ with $v_3(a_k)=0$.
-/
lemma lem_no_v3_zero_terms (a : ℕ → ℕ) : IsSequence a → ∀ k, padicValNat 3 (a k) ≠ 0 := by
  intros ha k;
  by_contra h_contra;
  -- If for all $n \geq k$, $v_3(a_n) = 0$, then the subsequence $(a_n)_{n \geq k}$ would be strictly decreasing, which contradicts the sequence being infinite.
  by_cases h_all_zero : ∀ n ≥ k, padicValNat 3 (a n) = 0;
  · have h_decreasing : ∀ n ≥ k, a (n + 1) < a n := by
      intros n hn;
      have h_decreasing : ∀ n ≥ k, R (a n) < 1 := by
        intros n hn;
        apply lem_decreasing_condition;
        · exact?;
        · exact ha.2.1 n;
        · by_contra h_contra;
          interval_cases _ : c_k 3 ( a n ) <;> simp_all ( config := { decide := Bool.true } );
          · unfold c_k at *;
            rcases x : ( a n |> Nat.divisors |> Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | h ⟩ ⟩ ⟩ <;> aesop;
            · replace x := congr_arg List.length x ; aesop;
              exact absurd x ( ne_of_gt ( ha.1 n ) );
            · have := congr_arg List.length x; norm_num at this;
              have := ha.2.1 n;
              rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
              interval_cases a n <;> contradiction;
            · have := congr_arg List.length x; norm_num at this;
              -- Since $a_n$ has at least three proper divisors, the cardinality of its divisors must be at least 3. This contradicts the assumption that it's 2.
              have h_card : 3 ≤ (Nat.divisors (a n)).card := by
                have := ha.2.1 n;
                exact le_trans this ( Finset.card_mono <| fun x hx => Nat.mem_divisors.mpr ⟨ Nat.mem_properDivisors.mp hx |>.1, by specialize ha; have := ha.1 n; aesop ⟩ );
              linarith;
            · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
            · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
          · unfold c_k at *;
            rcases x : ( a n |> Nat.divisors |> Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> aesop;
            · have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              interval_cases y <;> interval_cases x_1 <;> have := ha.2.1 n <;> simp_all ( config := { decide := Bool.true } );
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x ( a n ) ; aesop;
                by_cases h : a n = 0 <;> aesop;
            · have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              interval_cases x_1 <;> interval_cases y <;> simp_all ( config := { decide := Bool.true } );
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
              · have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              · have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
          · unfold c_k at *;
            rcases x : ( a n |> Nat.divisors |> Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> aesop;
            · have := congr_arg List.length x; norm_num at this;
              -- This contradicts the assumption that the number of proper divisors is at least 3.
              have h_contra : (Nat.divisors (a n)).card ≥ 4 := by
                have := ha.2.1 n;
                rw [ ← Nat.cons_self_properDivisors ] <;> aesop;
              linarith;
            · have h_divisors : x_1 = 1 := by
                have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
                interval_cases x_1 <;> simp_all ( config := { decide := Bool.true } );
                · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
                · have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              interval_cases y <;> simp_all ( config := { decide := Bool.true } );
              · have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              · have := x ▸ Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) ; aesop;
          · -- Since $c_k 3 (a n) = 3$, it follows that $3$ divides $a n$.
            have h_div : 3 ∣ a n := by
              unfold c_k at *;
              rcases x : ( a n |> Nat.divisors |> Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ) with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | h ⟩ ⟩ ⟩ ) <;> aesop;
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 3; aesop;
              · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 3; aesop;
            cases h_all_zero n hn <;> aesop;
            exact absurd h ( ne_of_gt ( ha.1 n ) );
      have := h_decreasing n hn;
      unfold R at this;
      rw [ div_lt_one ] at this <;> norm_cast at * <;> have := ha.2.2 n <;> aesop;
      exact ha.1 n;
    -- Since the subsequence $(a_n)_{n \geq k}$ is strictly decreasing and consists of positive integers, it must be finite.
    have h_finite : Set.Finite (Set.range (fun n => a (k + n))) := by
      exact Set.finite_iff_bddAbove.mpr ⟨ a k, by rintro x ⟨ n, rfl ⟩ ; exact Nat.recOn n ( by norm_num ) fun n ihn => by linarith! [ h_decreasing ( k + n ) ( by linarith ) ] ⟩;
    exact h_finite.not_infinite <| Set.infinite_range_of_injective ( StrictAnti.injective <| strictAnti_nat_of_succ_lt fun n => h_decreasing _ <| Nat.le_add_right _ _ );
  · -- Therefore, there must be a first term $a_m$ with $m > k$ such that $v_3(a_m) > 0$.
    obtain ⟨m, hm₁, hm₂⟩ : ∃ m > k, padicValNat 3 (a m) > 0 ∧ ∀ n, k < n ∧ n < m → padicValNat 3 (a n) = 0 := by
      obtain ⟨m, hm₁, hm₂⟩ : ∃ m > k, padicValNat 3 (a m) > 0 := by
        push_neg at h_all_zero;
        exact h_all_zero.imp fun n hn => ⟨ lt_of_le_of_ne hn.1 ( by aesop ), Nat.pos_of_ne_zero hn.2 ⟩;
      exact ⟨ Nat.find ( ⟨ m, hm₁, hm₂ ⟩ : ∃ m > k, padicValNat 3 ( a m ) > 0 ), Nat.find_spec ( ⟨ m, hm₁, hm₂ ⟩ : ∃ m > k, padicValNat 3 ( a m ) > 0 ) |>.1, Nat.find_spec ( ⟨ m, hm₁, hm₂ ⟩ : ∃ m > k, padicValNat 3 ( a m ) > 0 ) |>.2, by aesop ⟩;
    -- Since $a_m = S(a_{m-1})$ and $v_3(a_{m-1}) = 0$, by Lemma~\ref{lem:transition_to_v3_positive_is_odd}, $a_m$ must be odd.
    have h_odd_am : Odd (a m) := by
      have h_odd_am : padicValNat 3 (a (m - 1)) = 0 ∧ 3 ∣ a m := by
        rcases m <;> aesop;
        · cases ha ; aesop;
          linarith [ left_3 k ];
        · exact absurd h ( ne_of_gt ( ha.1 k ) );
        · cases lt_or_eq_of_le ( Nat.le_of_lt_succ hm₁ ) <;> aesop;
        · exact?;
      have h_odd_am : Odd (S (a (m - 1))) := by
        apply lem_transition_to_v3_positive_is_odd;
        · exact?;
        · exact ha.2.1 ( m - 1 );
        · exact h_odd_am.left;
        · have := ha.2.2 ( m - 1 ) ; rcases m <;> aesop;
      have := ha.2.2 ( m - 1 ) ; rcases m <;> aesop;
    -- This contradicts Lemma~\ref{lem:no_odd_terms}, which states that no term in the sequence can be odd.
    have h_contradiction : ∀ n, Even (a n) := by
      exact?;
    exact Nat.not_even_iff_odd.mpr h_odd_am ( h_contradiction m )

/-
For any term $a_n$ in an infinite sequence, it must be divisible by 3. This implies $c_3(a_n)=3$.
-/
lemma lem_all_terms_divisible_by_3 (a : ℕ → ℕ) : IsSequence a → ∀ n, 3 ∣ a n ∧ c_k 3 (a n) = 3 := by
  aesop;
  · contrapose! a_1;
    exact fun h => absurd ( lem_no_v3_zero_terms a h n ) ( by aesop );
  · -- Since $a_n$ is divisible by 3 and even, its smallest divisors are 1, 2, and 3. Therefore, the third smallest divisor is 3.
    have h_divisors : (Nat.divisors (a n)).sort (· ≤ ·) = 1 :: 2 :: 3 :: (Nat.divisors (a n) \ {1, 2, 3}).sort (· ≤ ·) := by
      rw [ ← Finset.sort_insert ];
      · rw [ ← Finset.sort_insert ];
        · rw [ ← Finset.sort_insert ];
          · -- Since $a_n$ is divisible by 3, the set $\{1, 2, 3\}$ is a subset of the divisors of $a_n$.
            have h_subset : {1, 2, 3} ⊆ Nat.divisors (a n) := by
              intro x hx
              aesop;
              · simpa [ a_2 ] using a_1.1 n;
              · exact even_iff_two_dvd.mp ( by exact? );
              · simpa [ a_2 ] using a_1.1 n;
              · contrapose! a_1;
                exact fun h => absurd ( lem_no_v3_zero_terms a h n ) ( by aesop );
              · simpa [ a_2 ] using a_1.1 n;
            congr;
            ext x; by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> by_cases hx3 : x = 3 <;> aesop;
            · exact Nat.dvd_of_mem_divisors ( h_subset ( by norm_num ) );
            · exact Nat.dvd_of_mem_divisors ( h_subset ( by norm_num ) );
          · aesop;
            exact Nat.pos_of_dvd_of_pos left ( Nat.pos_of_ne_zero right_1 );
          · aesop;
        · aesop;
          exact Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos left ( Nat.pos_of_ne_zero right_1 ) ) ( Ne.symm left_1 );
        · -- Since $2$ is not in $\{3\}$ and $2$ is not in $(Nat.divisors (a n) \ {1, 2, 3})$, it follows that $2$ is not in their union.
          simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton];
      · -- Since $b$ is a divisor of $a_n$ and $b \notin \{1, 2, 3\}$, the smallest possible value for $b$ is $3$.
        intros b hb
        have hb_pos : 1 ≤ b := by
          exact Nat.pos_of_mem_divisors ( Finset.mem_sdiff.mp hb |>.1 );
        contrapose! hb; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
      · aesop;
    unfold c_k;
    aesop

/-
An infinite sequence cannot have a term $a_n$ with $c_4(a_n) \ge 7$.
-/
lemma lem_c4_ge_7_impossible (a : ℕ → ℕ) : IsSequence a → ∀ n, ¬ (c_k 4 (a n) ≥ 7) := by
  bound;
  -- Since $a_n$ is divisible by 3, its divisors must include 1, 2, 3, and 6. Therefore, $c_4(a_n)$ cannot be greater than or equal to 7.
  have h_divisors : 3 ∣ a n ∧ c_k 3 (a n) = 3 := by
    exact?;
  have h_ratio : R (a n) < 1 := by
    -- Substitute c_k 3 (a n) = 3 into the expression for R(a n).
    have h_ratio_expr : R (a n) = (1 : ℚ) / 2 + 1 / 3 + 1 / (c_k 4 (a n)) := by
      rw [ lem_ratio_for_even ];
      · rw [ h_divisors.2 ] ; ring;
      · exact?;
      · exact a_1.2.1 n;
    rw [ h_ratio_expr, div_add_div, div_add_div, div_lt_iff₀ ] <;> norm_cast <;> nlinarith;
  unfold R at h_ratio;
  rw [ div_lt_iff₀ ] at h_ratio <;> norm_cast at *;
  · unfold c_k at *;
    rcases k : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ ) <;> aesop;
    have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
    interval_cases y <;> interval_cases x <;> simp_all ( config := { decide := Bool.true } );
    all_goals have := k ▸ Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) ; simp_all ( config := { decide := Bool.true } );
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 0; aesop;
    · replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k 6; simp_all ( config := { decide := Bool.true } ) ;
      contrapose! k;
      exact Or.inl ⟨ ⟨ Nat.lcm_dvd left ( show 2 ∣ a n from even_iff_two_dvd.mp ( by simpa using lem_all_terms_even a a_1 n ) ), by aesop_cat ⟩, by linarith, fun h => by have := left_7 _ h; linarith ⟩;
  · exact a_1.1 n

/-
For any term $a_n$ in a non-constant infinite sequence, if $a_n$ is not a fixed point, then $R(a_n)>1$.
-/
lemma lem_non_fixed_must_grow (a : ℕ → ℕ) : IsSequence a → ∀ n, S (a n) ≠ a n → R (a n) > 1 := by
  -- By Lemma~\ref{lem:all_terms_divisible_by_3}, we have $c_3(a_n)=3$. By Lemma~\ref{lem:c4_ge_7_impossible}, we must have $c_4(a_n) < 7$.
  intros ha n hn
  have h_c3 : c_k 3 (a n) = 3 := by
    -- By Lemma~\ref{lem:all_terms_divisible_by_3}, we have $3 \mid a_n$ and $c_3(a_n) = 3$.
    apply (lem_all_terms_divisible_by_3 a ha n).right
  have h_c4 : c_k 4 (a n) < 7 := by
    by_contra h_contra;
    have := lem_c4_ge_7_impossible a ha n;
    exact this ( not_lt.mp h_contra );
  -- Since $c_4(a_n)$ must be 4 or 5, we can calculate $R(a_n)$ for these cases.
  have h_cases : c_k 4 (a n) = 4 ∨ c_k 4 (a n) = 5 := by
    interval_cases _ : c_k 4 ( a n ) <;> simp_all ( config := { decide := Bool.true } );
    · unfold c_k at *;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
      · replace x := congr_arg List.length x ; simp_all ( config := { decide := Bool.true } );
        have := ha.2.1 n; rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 0; aesop;
    · unfold c_k at *;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors ( a n ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
      have := x ▸ Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; simp_all ( config := { decide := Bool.true } );
    · unfold c_k at *;
      rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( a n |> Nat.divisors ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | k ⟩ ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
      · have := x ▸ Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; simp_all ( config := { decide := Bool.true } );
      · have := x ▸ Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; simp_all ( config := { decide := Bool.true } );
    · unfold c_k at *;
      -- Since the divisors are sorted in ascending order, having two consecutive divisors both equal to 3 isn't possible. This means our assumption must be wrong, leading to a contradiction.
      have h_unique_divisors : List.Nodup (Finset.sort (· ≤ ·) (Nat.divisors (a n))) := by
        exact Finset.sort_nodup _ _;
      rcases x : Finset.sort ( · ≤ · ) ( Nat.divisors ( a n ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | k ⟩ ⟩ ⟩ ⟩ <;> simp_all ( config := { decide := Bool.true } );
    · -- If $c_4(a_n) = 6$, then $R(a_n) = \frac{1}{2} + \frac{1}{3} + \frac{1}{6} = 1$, so $a_n$ is a fixed point by Lemma~\ref{lem:fixed_point_condition}.
      have h_fixed_point : R (a n) = 1 := by
        rw [ lem_ratio_for_even ];
        · norm_num [ h_c3, ‹c_k 4 ( a n ) = 6› ];
        · exact?;
        · exact ha.2.1 n;
      have := lem_fixed_point_condition ( a n ) ( ha.1 n ) ; aesop;
  have h_ratio : R (a n) = (1 : ℚ) / 2 + 1 / (c_k 3 (a n)) + 1 / (c_k 4 (a n)) := by
    apply lem_ratio_for_even;
    · exact?;
    · exact ha.2.1 n;
  rcases h_cases with ( h | h ) <;> norm_num [ h_ratio, h_c3, h ]

/-
Any possible value of $a_1$ must be of the form $6 \cdot 12^a \cdot m$ for some integer $a \ge 0$ and a positive integer $m$ with $\gcd(m,10)=1$.
-/
lemma lem_a1_structure :
  { a₁ | ∃ a : ℕ → ℕ, IsSequence a ∧ a₁ = a 0 } ⊆ { n | ∃ a m, m > 0 ∧ Nat.Coprime m 10 ∧ n = 6 * 12 ^ a * m } := by
    -- Therefore, any term $a_n$ in the sequence must be of the form $6 \cdot 12^k \cdot m$ where $m$ is coprime to 10.
    intros a₁ ha₁
    obtain ⟨a, ha_seq, rfl⟩ := ha₁;
    -- Let $k$ be such that $a_k$ is the first fixed point in the sequence.
    obtain ⟨k, hk⟩ : ∃ k, S (a k) = a k ∧ ∀ j < k, S (a j) ≠ a j := by
      -- By the well-ordering principle, there exists a smallest $k$ such that $S(a_k) = a_k$.
      obtain ⟨k, hk⟩ : ∃ k, S (a k) = a k := by
        -- By contradiction, assume there is no such $k$.
        by_contra h_no_fixed_point;
        -- Since $a_n$ is not a fixed point, we have $R(a_n) > 1$ for all $n$.
        have hR_gt_1 : ∀ n, R (a n) > 1 := by
          intros n;
          apply_rules [ lem_non_fixed_must_grow ];
          exact fun h => h_no_fixed_point ⟨ n, h ⟩;
        -- Since $R(a_n) > 1$, we have $a_{n+1} = a_n \cdot R(a_n) > a_n$ for all $n$.
        have h_increasing : ∀ n, a (n + 1) > a n := by
          unfold R at hR_gt_1;
          intro n; specialize hR_gt_1 n; rw [ gt_iff_lt, lt_div_iff₀ ] at hR_gt_1 <;> norm_cast at * <;> aesop;
          · exact ha_seq.2.2 n ▸ hR_gt_1;
          · exact ha_seq.1 n;
        -- Since $a_n$ is strictly increasing, it cannot have a term $a_k$ with $c_4(a_k) \ge 7$.
        have h_c4_lt_7 : ∀ n, c_k 4 (a n) < 7 := by
          intros n
          by_contra h_contra;
          exact absurd ( lem_c4_ge_7_impossible a ha_seq n ) ( by aesop );
        -- Since $c_4(a_n) < 7$, we have $c_4(a_n) = 4$ or $c_4(a_n) = 5$ for all $n$.
        have h_c4_eq_4_or_5 : ∀ n, c_k 4 (a n) = 4 ∨ c_k 4 (a n) = 5 := by
          intros n
          have h_c4_divisors : c_k 2 (a n) = 2 ∧ c_k 3 (a n) = 3 := by
            have := lem_all_terms_divisible_by_3 a ha_seq n;
            have := lem_c2_is_2 a ha_seq n; aesop;
          have h_c4_gt_c3 : c_k 4 (a n) > c_k 3 (a n) := by
            unfold c_k at *;
            rcases x : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( a n |> Nat.divisors ) ) with _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | k ⟩ ⟩ ⟩ <;> aesop;
            · have := ha_seq.2.1 n; replace x := congr_arg List.length x; aesop;
              rw [ ← Nat.cons_self_properDivisors ] at x <;> aesop;
            · have := Finset.sort_sorted ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
              rcases k with ( _ | _ | _ | _ | k ) <;> simp_all +arith +decide;
              have := x ▸ Finset.sort_nodup ( · ≤ · ) ( Nat.divisors ( a n ) ) ; aesop;
          have := h_c4_lt_7 n; interval_cases _ : c_k 4 ( a n ) <;> simp_all ( config := { decide := Bool.true } ) ;
          have := lem_ratio_for_even ( a n ) ( by
            exact? ) ( by
            exact ha_seq.2.1 n ) ; simp_all ( config := { decide := Bool.true } );
          linarith [ hR_gt_1 n ];
        -- Since $c_4(a_n) = 4$ or $c_4(a_n) = 5$, we have $R(a_n) = \frac{13}{12}$ or $R(a_n) = \frac{31}{30}$ for all $n$.
        have hR_eq_13_12_or_31_30 : ∀ n, R (a n) = 13 / 12 ∨ R (a n) = 31 / 30 := by
          intros n
          obtain h | h := h_c4_eq_4_or_5 n;
          · have hR_eq_13_12 : R (a n) = 1 / 2 + 1 / 3 + 1 / 4 := by
              rw [ lem_ratio_for_even ];
              · have := lem_all_terms_divisible_by_3 a ha_seq n; aesop;
              · exact?;
              · exact ha_seq.2.1 n;
            exact Or.inl <| hR_eq_13_12.trans <| by norm_num;
          · have hR_eq_31_30 : R (a n) = (1 : ℚ) / 2 + 1 / (c_k 3 (a n)) + 1 / (c_k 4 (a n)) := by
              rw [ lem_ratio_for_even ];
              · exact?;
              · exact ha_seq.2.1 n;
            have h_c3_eq_3 : c_k 3 (a n) = 3 := by
              have := lem_all_terms_divisible_by_3 a ha_seq n;
              exact this.2;
            norm_num [ hR_eq_31_30, h_c3_eq_3, h ];
        -- Since $R(a_n) = \frac{13}{12}$ or $R(a_n) = \frac{31}{30}$, we have $a_{n+1} = a_n \cdot \frac{13}{12}$ or $a_{n+1} = a_n \cdot \frac{31}{30}$ for all $n$.
        have h_an1_eq_an_mul_13_12_or_31_30 : ∀ n, a (n + 1) = a n * (13 / 12 : ℚ) ∨ a (n + 1) = a n * (31 / 30 : ℚ) := by
          intro n; specialize hR_eq_13_12_or_31_30 n; unfold R at hR_eq_13_12_or_31_30; aesop;
          · exact Or.inl ( by rw [ ← h, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr ( by linarith [ ha_seq.1 n ] ) ) ] ; rw [ ha_seq.2.2 ] );
          · rw [ div_eq_iff ] at h_1 <;> norm_num [ ha_seq.2.2 ] at *;
            · exact Or.inr ( by linarith );
            · linarith [ ha_seq.1 n ];
        -- Since $a_{n+1} = a_n \cdot \frac{13}{12}$ or $a_{n+1} = a_n \cdot \frac{31}{30}$, we have $a_n = a_0 \cdot \left(\frac{13}{12}\right)^{k} \cdot \left(\frac{31}{30}\right)^{m}$ for some $k, m \geq 0$.
        have h_an_form : ∀ n, ∃ k m : ℕ, a n = a 0 * (13 / 12 : ℚ) ^ k * (31 / 30 : ℚ) ^ m := by
          intro n;
          induction' n with n ih;
          · exact ⟨ 0, 0, by norm_num ⟩;
          · rcases ih with ⟨ k, m, ih ⟩ ; rcases h_an1_eq_an_mul_13_12_or_31_30 n with h | h <;> [ exact ⟨ k + 1, m, by rw [ h, ih ] ; ring ⟩ ; exact ⟨ k, m + 1, by rw [ h, ih ] ; ring ⟩ ];
        choose k m hkm using h_an_form;
        -- Since $a_n$ is an integer, the denominator $12^{k_n} \cdot 30^{m_n}$ must divide $a_0$.
        have h_denom_divides_a0 : ∀ n, 12 ^ k n * 30 ^ m n ∣ a 0 := by
          -- Since $a_n$ is an integer, the denominator $12^{k_n} \cdot 30^{m_n}$ must divide the numerator $a_0 \cdot 13^{k_n} \cdot 31^{m_n}$.
          have h_denom_divides_num : ∀ n, 12 ^ k n * 30 ^ m n ∣ a 0 * 13 ^ k n * 31 ^ m n := by
            intro n; specialize hkm n; rw [ div_pow, div_pow ] at hkm;
            field_simp at hkm;
            norm_cast at hkm; exact hkm ▸ dvd_mul_left _ _;
          intro n; specialize h_denom_divides_num n;
          refine' Nat.Coprime.dvd_of_dvd_mul_right _ _;
          exact 13 ^ k n * 31 ^ m n;
          · apply_rules [ Nat.Coprime.mul, Nat.Coprime.pow ];
            · apply_rules [ Nat.Coprime.mul_right, Nat.Coprime.pow ];
            · apply_rules [ Nat.Coprime.mul_right, Nat.Coprime.pow ];
          · simpa only [ mul_assoc ] using h_denom_divides_num;
        -- Since $12^{k_n} \cdot 30^{m_n}$ divides $a_0$, and $a_0$ is fixed, the sequence $12^{k_n} \cdot 30^{m_n}$ must be bounded.
        have h_denom_bounded : ∃ M, ∀ n, 12 ^ k n * 30 ^ m n ≤ M := by
          exact ⟨ a 0, fun n => Nat.le_of_dvd ( ha_seq.1 0 ) ( h_denom_divides_a0 n ) ⟩;
        -- Since $12^{k_n} \cdot 30^{m_n}$ is bounded, the sequence $k_n + m_n$ must also be bounded.
        have h_k_m_bounded : ∃ M, ∀ n, k n + m n ≤ M := by
          obtain ⟨ M, hM ⟩ := h_denom_bounded;
          use M;
          intro n; specialize hM n; contrapose! hM;
          refine' lt_of_lt_of_le hM _;
          -- Since $12^{k_n} \cdot 30^{m_n}$ grows exponentially, we have $k_n + m_n \leq 12^{k_n} \cdot 30^{m_n}$.
          have h_exp_growth : ∀ k m : ℕ, k + m ≤ 12 ^ k * 30 ^ m := by
            intro k m; induction' k with k ih generalizing m <;> induction' m with m ih' <;> norm_num [ Nat.pow_succ', mul_assoc ] at *;
            · linarith [ pow_pos ( by decide : 0 < 30 ) m ];
            · linarith [ ih 0, Nat.one_le_pow k 12 ( by decide ) ];
            · linarith [ ih m ];
          exact h_exp_growth _ _;
        -- Since $k_n + m_n$ is bounded, the sequence $a_n$ must also be bounded.
        have h_an_bounded : ∃ M, ∀ n, a n ≤ M := by
          use a 0 * 13 ^ h_k_m_bounded.choose * 31 ^ h_k_m_bounded.choose;
          intro n;
          have := hkm n;
          rw [ ← @Nat.cast_le ℚ ];
          rw [ this ] ; push_cast ; ring_nf;
          gcongr;
          · exact le_trans ( pow_le_pow_left ( by norm_num ) ( by norm_num ) _ ) ( pow_le_pow_right₀ ( by norm_num ) ( show m n ≤ h_k_m_bounded.choose from by linarith [ h_k_m_bounded.choose_spec n ] ) );
          · exact le_trans ( pow_le_pow_left ( by norm_num ) ( by norm_num ) _ ) ( pow_le_pow_right₀ ( by norm_num ) ( h_k_m_bounded.choose_spec n |> le_trans ( Nat.le_add_right _ _ ) ) );
        exact absurd ( Set.infinite_range_of_injective ( StrictMono.injective ( strictMono_nat_of_lt_succ h_increasing ) ) ) ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr ⟨ h_an_bounded.choose, Set.forall_mem_range.mpr fun n => h_an_bounded.choose_spec n ⟩ );
      exact ⟨ Nat.find ( ⟨ k, hk ⟩ : ∃ k, S ( a k ) = a k ), Nat.find_spec ( ⟨ k, hk ⟩ : ∃ k, S ( a k ) = a k ), fun j hj => Nat.find_min ( ⟨ k, hk ⟩ : ∃ k, S ( a k ) = a k ) hj ⟩;
    -- By Lemma~\ref{lem:transition_to_v3_positive_is_odd}, the term $a_{k-1}$ must have $v_2(a_{k-1}) \ge 2$.
    have h_ak_minus_1 : ∀ j < k, a (j + 1) = a j * (13 / 12 : ℚ) := by
      -- Since $a_j$ is not a fixed point, we have $R(a_j) > 1$ and $c_3(a_j) = 3$, $c_4(a_j) = 4$.
      have h_R_gt_1_and_c3_c4 : ∀ j < k, R (a j) > 1 ∧ c_k 3 (a j) = 3 ∧ c_k 4 (a j) = 4 := by
        intros j hj;
        -- Since $a_j$ is not a fixed point, by Lemma~\ref{lem:all_terms_divisible_by_3}, $a_j$ is divisible by 3, so $c_k 3 (a_j) = 3$.
        have h_c3 : c_k 3 (a j) = 3 := by
          exact lem_all_terms_divisible_by_3 a ha_seq j |>.2;
        have h_R_gt_1 : R (a j) > 1 := by
          exact lem_non_fixed_must_grow a ha_seq j ( hk.2 j hj );
        have := lem_growth_condition ( a j ) ?_ ?_ ?_ <;> aesop;
        · have := lem_growth_c4_is_5_impossible ( a j ) ?_ ?_ ?_ ?_;
          · -- Since $a_j$ is even, $S(a_j)$ must also be even. This contradicts the fact that $S(a_j)$ is odd.
            have h_even_S : Even (S (a j)) := by
              have h_even_S : Even (a (j + 1)) := by
                exact?;
              exact ha_seq.2.2 j ▸ h_even_S;
            exact Nat.not_even_iff_odd.mpr this h_even_S;
          · -- Since $a$ is a sequence, we have $a (n + 1) = S (a n)$ for all $n$.
            have h_seq : ∀ n, a (n + 1) = S (a n) := by
              exact fun n => ha_seq.2.2 n;
            constructor <;> aesop;
            · exact ha_seq.1 j;
            · have := ha_seq.1 ( j + n );
              convert this using 1;
              exact Nat.recOn n ( by norm_num ) fun n ih => by rw [ Nat.add_succ, h_seq, Function.iterate_succ_apply', ih ] ;
            · exact ha_seq.2.1 j;
            · -- Since $a$ is a sequence, each term $a n$ has at least three proper divisors. Therefore, $S^[n] (a j)$ is just another term in the sequence, and thus has at least three proper divisors.
              have h_seq_divisors : ∀ n, 3 ≤ (Nat.properDivisors (a n)).card := by
                exact fun n => ha_seq.2.1 n;
              convert h_seq_divisors ( j + n ) using 1;
              exact congr_arg ( fun x => ( Nat.properDivisors x ).card ) ( Nat.recOn n ( by norm_num ) fun n ih => by rw [ Nat.add_succ, h_seq, Function.iterate_succ_apply', ih ] );
            · exact Nat.recOn n ( by norm_num ) fun n ih => by rw [ Function.iterate_succ_apply', ih, Function.iterate_succ_apply' ] ;
          · exact lem_c2_is_2 a ha_seq j;
          · exact h_c3;
          · exact h_1;
        · exact?;
      intro j hj;
      have := h_R_gt_1_and_c3_c4 j hj;
      have h_S_a_j : S (a j) = a j * (13 / 12 : ℚ) := by
        unfold R at this;
        have := lem_ratio_for_even ( a j ) ( by
          exact? ) ( by
          exact ha_seq.2.1 j ) ; aesop;
        rw [ lt_div_iff₀ ] at this_1 <;> norm_num at *;
        · unfold R at this;
          rw [ ← this, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr <| by specialize ha_seq; have := ha_seq.1 j; aesop ) ];
        · exact Nat.pos_of_ne_zero ( by specialize ha_seq; have := ha_seq.1 j; aesop );
      rw [ ← h_S_a_j, ha_seq.2.2 ];
    -- Therefore, $a_0 = a_k \cdot \left(\frac{12}{13}\right)^k$.
    have h_a0 : a 0 = a k * (12 / 13 : ℚ) ^ k := by
      have h_a0 : ∀ j ≤ k, a j = a 0 * (13 / 12 : ℚ) ^ j := by
        intro j hj;
        induction' j with j ih;
        · norm_num;
        · rw [ h_ak_minus_1 j ( Nat.lt_of_succ_le hj ), ih ( Nat.le_of_succ_le hj ), pow_succ, mul_assoc ];
      rw [ h_a0 k le_rfl ] ; ring;
      norm_num [ mul_assoc, ← mul_pow ];
    -- Since $a_k$ is a fixed point, by Lemma~\ref{lem:fixed_point_form}, $a_k$ must be of the form $6m'$ where $m'$ is coprime to 10.
    obtain ⟨m', hm'_pos, hm'_coprime, hm'_eq⟩ : ∃ m', 0 < m' ∧ Nat.Coprime m' 10 ∧ a k = 6 * m' := by
      have := lem_fixed_point_form ( a k );
      exact this.mp ⟨ hk.1, ha_seq.2.1 k ⟩;
    -- Substitute $a_k = 6m'$ into the equation $a_0 = a_k \cdot \left(\frac{12}{13}\right)^k$ to get $a_0 = 6m' \cdot \left(\frac{12}{13}\right)^k$.
    rw [hm'_eq] at h_a0;
    -- For $a_0$ to be an integer, $m'$ must be divisible by $13^k$. Let $m' = 13^k \cdot m$ for some integer $m$.
    obtain ⟨m, hm⟩ : ∃ m, m' = 13^k * m := by
      have h_div : 13^k ∣ 6 * m' := by
        field_simp at h_a0;
        norm_cast at h_a0;
        exact ( Nat.Coprime.dvd_of_dvd_mul_right ( by cases k <;> norm_num ) <| h_a0 ▸ dvd_mul_left _ _ );
      exact ( Nat.Coprime.dvd_of_dvd_mul_left ( by cases k <;> norm_num ) h_div );
    refine' ⟨ k, m, _, _, _ ⟩ <;> simp_all ( config := { decide := Bool.true } ) [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ];
    · exact hm'_coprime.2;
    · rw [ ← @Nat.cast_inj ℚ ] ; push_cast [ h_a0 ] ; ring;
      -- By simplifying, we can see that $(12/13)^k * 13^k = 12^k$.
      field_simp

/-
A proper divisor of a positive integer $N$ is a positive divisor of $N$ other than $N$ itself.
The infinite sequence $a_1,a_2,...$ consists of positive integers, each of which has at least three proper divisors.
For each $n \ge 1$, the integer $a_{n+1}$ is the sum of the three largest proper divisors of $a_n$.
The set of all possible values of $a_1$ is the set of all integers of the form $6 \cdot 12^a \cdot m$, for any integer $a \ge 0$ and any positive integer $m$ which is coprime to $10$.
-/
theorem main_theorem :
    { a₁ | ∃ a : ℕ → ℕ,
      (∀ n, 0 < a n) ∧
      (∀ n, 3 ≤ (a n).properDivisors.card) ∧
      (∀ n, a (n+1) =
        ((a n).properDivisors.sort (· ≥ ·))[0]! +
        ((a n).properDivisors.sort (· ≥ ·))[1]! +
        ((a n).properDivisors.sort (· ≥ ·))[2]!) ∧
      a₁ = a 0
    } = { n | ∃ a m, m > 0 ∧ m.Coprime 10 ∧ n = 6 * 12 ^ a * m } := by
      ext a₁;
      constructor;
      · intro ha₁;
        -- By lemma lem_a1_structure, any possible value of $a_1$ must be of the form $6 \cdot 12^a \cdot m$ for some integer $a \ge 0$ and a positive integer $m$ with $\gcd(m,10)=1$.
        apply lem_a1_structure;
        obtain ⟨a, ha⟩ := ha₁;
        exact ⟨ a, ⟨ ha.1, ha.2.1, ha.2.2.1 ⟩, ha.2.2.2 ⟩;
      · -- By definition of $a₁$, we know that there exist $a$ and $m$ such that $a₁ = 6 * 12^a * m$ and $m$ is coprime to 10.
        intro h
        obtain ⟨a, m, hm_pos, hm_coprime, rfl⟩ := h;
        -- Apply the lemma lem_verification_of_form to obtain the required sequence a and show that a 0 equals 6 * 12^a * m.
        obtain ⟨a, ha⟩ := lem_verification_of_form ⟨a, m, hm_pos, hm_coprime, rfl⟩;
        exact ⟨ a, ha.1.1, ha.1.2.1, ha.1.2.2, ha.2 ⟩

#print axioms main_theorem
