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

namespace IMO2025P4Solve2

/-
The following definition is not explicitly present in the provided text, but is referred to as "Definition def:s_N". We formalize it here for use in the lemmas.
For a positive integer $N$ with at least three proper divisors, $s(N)$ is the sum of the three largest proper divisors of $N$.
-/
def s (N : ℕ) : ℕ :=
  if h : 3 ≤ N.properDivisors.card then
    ((N.properDivisors.sort (· ≥ ·))[0]! +
     (N.properDivisors.sort (· ≥ ·))[1]! +
     (N.properDivisors.sort (· ≥ ·))[2]!)
  else 0

/-
If an integer $N$ is not divisible by 2 or 3, then $s(N) < N$.
-/
lemma lem_s_N_bound_no_2_3 (N : ℕ) (hpos : 0 < N) (h_card : 3 ≤ N.properDivisors.card)
  (h2 : ¬ (2 ∣ N)) (h3 : ¬ (3 ∣ N)) : s N < N := by
    unfold s;
    -- Since $N$ is not divisible by 2 or 3, its smallest prime factor $p$ must be at least 5. Therefore, the three largest proper divisors are $N/p$, $N/q$, and $N/r$, where $p$, $q$, and $r$ are the smallest primes dividing $N$.
    have h_smallest_prime : ∀ {d : ℕ}, d ∈ N.properDivisors → d ≤ N / 5 := by
      aesop;
      rw [ Nat.le_div_iff_mul_le ] <;> obtain ⟨ k, hk ⟩ := left <;> aesop;
      contrapose! h3; interval_cases k <;> simp_all ( config := { decide := Bool.true } ) ;
      norm_num [ Nat.mul_mod ] at h2;
    rcases x : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.length x; aesop;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; have := x a; have := x b; have := x c; aesop;
      have := x a; have := x b; have := x c; norm_num at *;
      grind;
    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; have ha := x a; have hb := x b; have hc := x c; have hk := x k; norm_num at *;
      grind

/-
Let $N$ be an integer satisfying the condition in Definition~\ref{def:s_N}. If $1 < d_1 < d_2 < d_3 < \dots$ are the positive divisors of $N$ greater than 1 in increasing order, then the three largest proper divisors of $N$ are $N/d_1$, $N/d_2$, and $N/d_3$.
-/
lemma lem_s_N_smallest_divisors (N : ℕ) (h_card : 3 ≤ N.properDivisors.card) :
  let d₁ := ((N.divisors.erase 1).sort (· ≤ ·))[0]!
  let d₂ := ((N.divisors.erase 1).sort (· ≤ ·))[1]!
  let d₃ := ((N.divisors.erase 1).sort (· ≤ ·))[2]!
  s N = N / d₁ + N / d₂ + N / d₃ := by
    -- The three largest proper divisors of $N$ are $N/d_1$, $N/d_2$, and $N/d_3$, where $d_1$, $d_2$, and $d_3$ are the three smallest divisors of $N$ greater than 1.
    have h_largest : (N.properDivisors.sort (· ≥ ·))[0]! = N / ((N.divisors.erase 1).sort (· ≤ ·))[0]! ∧
                     (N.properDivisors.sort (· ≥ ·))[1]! = N / ((N.divisors.erase 1).sort (· ≤ ·))[1]! ∧
                     (N.properDivisors.sort (· ≥ ·))[2]! = N / ((N.divisors.erase 1).sort (· ≤ ·))[2]! := by
                       have h_largest : (N.properDivisors.sort (· ≥ ·)) = List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·)) := by
                         have h_largest : List.Sorted (· ≥ ·) (List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·))) ∧ List.Nodup (List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·))) := by
                           aesop;
                           · -- Since the original list of divisors is sorted in ascending order, applying N/d to each element will reverse the order, resulting in a list sorted in descending order.
                             have h_sorted : ∀ {l : List ℕ}, (∀ d ∈ l, d ∣ N) → List.Sorted (· ≤ ·) l → List.Sorted (· ≥ ·) (List.map (fun d => N / d) l) := by
                               intros l hl_div hl_sorted; induction hl_sorted <;> aesop;
                               exact Nat.div_le_div_left ( a_1 _ a_4 ) ( Nat.pos_of_dvd_of_pos left ( Nat.pos_of_ne_zero ( by aesop_cat ) ) );
                             exact h_sorted ( fun d hd => Nat.dvd_of_mem_divisors <| Finset.mem_of_mem_erase <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 hd ) <| Finset.sort_sorted _ _;
                           · rw [ List.nodup_map_iff_inj_on ];
                             · aesop;
                               exact?;
                             · exact Finset.sort_nodup _ _;
                         -- To prove the equality of the two lists, we can show that they are permutations of each other and that they are both sorted in the required order.
                         have h_perm : List.Perm (List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·))) (Finset.sort (· ≥ ·) N.properDivisors) := by
                           -- Since every proper divisor of $N$ can be written as $N/d$ for some divisor $d$ of $N$, the list of $N/d$ for each $d$ in the sorted list of divisors (excluding 1) is exactly the list of proper divisors.
                           have h_perm : List.toFinset (List.map (fun d => N / d) ((N.divisors.erase 1).sort (· ≤ ·))) = N.properDivisors := by
                             ext; aesop;
                             · -- Since $w \mid N$, we have $N / w \mid N$ by definition of division.
                               apply Nat.div_dvd_of_dvd left_2;
                             · exact Nat.div_lt_self ( Nat.pos_of_ne_zero right_2 ) ( lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos left_2 ( Nat.pos_of_ne_zero right_2 ) ) ( Ne.symm left_1 ) );
                             · exact ⟨ N / a, ⟨ by nlinarith [ Nat.div_mul_cancel left_1 ], Nat.div_dvd_of_dvd left_1, by linarith ⟩, by rw [ Nat.div_div_self ] <;> aesop ⟩;
                           rw [ List.perm_iff_count ];
                           intro a; replace h_perm := Finset.ext_iff.mp h_perm a; aesop;
                           by_cases ha : a ∈ List.map ( fun d => N / d ) ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) ) <;> aesop;
                           rw [ List.count_eq_zero_of_not_mem, List.count_eq_zero_of_not_mem ] <;> aesop;
                         rw [ List.eq_of_perm_of_sorted h_perm h_largest.1 ( Finset.sort_sorted _ _ ) ];
                       rcases n : Finset.sort ( · ≤ · ) ( Nat.divisors N |> Finset.erase <| 1 ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ <;> aesop;
    unfold s; aesop;

/-
If an integer $N$ is divisible by 2 but not by 3, then $s(N) < N$.
-/
lemma lem_s_N_bound_yes_2_no_3 (N : ℕ) (hpos : 0 < N) (h_card : 3 ≤ N.properDivisors.card)
  (h2 : 2 ∣ N) (h3 : ¬ (3 ∣ N)) : s N < N := by
    -- Let's denote the three largest proper divisors of $N$ as $d_1$, $d_2$, and $d_3$.
    obtain ⟨d1, d2, d3, hd1, hd2, hd3, hd_distinct⟩ : ∃ d1 d2 d3, d1 ∈ N.properDivisors ∧ d2 ∈ N.properDivisors ∧ d3 ∈ N.properDivisors ∧ d1 > d2 ∧ d2 > d3 ∧ d1 + d2 + d3 = s N := by
      -- Since $N$ has at least three proper divisors, we can select the three largest ones from the sorted list of proper divisors.
      obtain ⟨d1, d2, d3, hd1, hd2, hd3, hd_sorted⟩ : ∃ d1 d2 d3, d1 ∈ N.properDivisors ∧ d2 ∈ N.properDivisors ∧ d3 ∈ N.properDivisors ∧ d1 > d2 ∧ d2 > d3 ∧ d1 ∈ (N.properDivisors.sort (· ≥ ·)) ∧ d2 ∈ (N.properDivisors.sort (· ≥ ·)) ∧ d3 ∈ (N.properDivisors.sort (· ≥ ·)) ∧ (N.properDivisors.sort (· ≥ ·)).take 3 = [d1, d2, d3] := by
        rcases n : Finset.sort ( fun x1 x2 ↦ x1 ≥ x2 ) N.properDivisors with _ | ⟨ d1, _ | ⟨ d2, _ | ⟨ d3, _ | n ⟩ ⟩ ⟩ ; aesop;
        · have := congr_arg List.length n; norm_num at this;
          interval_cases N ; contradiction;
        · replace n := congr_arg List.length n; aesop;
        · -- Since the cardinality of the proper divisors is at least 3, the sorted list cannot have only two elements. This leads to a contradiction.
          have h_contra : (Finset.sort (fun x1 x2 => x1 ≥ x2) N.properDivisors).length ≥ 3 := by
            simpa using h_card;
          aesop;
        · -- Since the list is sorted in descending order, we have $d1 > d2 > d3$.
          have h_sorted : d1 > d2 ∧ d2 > d3 := by
            have := n ▸ Finset.sort_sorted_gt N.properDivisors; aesop;
          exact ⟨ d1, d2, d3, by replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n d1; aesop, by replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n d2; aesop, by replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n d3; aesop, h_sorted.1, h_sorted.2, by aesop ⟩;
        · have := Finset.sort_sorted_gt N.properDivisors; aesop;
          all_goals replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; have := n d1; have := n d2; have := n d3; have := n n_1; aesop;
          grind;
          · specialize n d1; aesop;
          · specialize n d2; aesop;
          · specialize n d2; aesop;
          · specialize n d3; aesop;
          · exact ( n d3 ) |>.2 ( Or.inr <| Or.inr <| Or.inl rfl ) |>.2;
      -- Since the list take 3 of the sorted proper divisors is [d1, d2, d3], these are the three largest elements. Hence, their sum is s(N).
      use d1, d2, d3;
      unfold s;
      rcases n : Finset.sort ( fun x1 x2 => x1 ≥ x2 ) N.properDivisors with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ <;> aesop;
    -- Since $2|N$, we have $d_1 = N/2$.
    have hd1_eq : d1 ≤ N / 2 := by
      -- Since $d1$ divides $N$ and $d1 < N$, we can write $N = d1 * k$ for some integer $k \geq 2$.
      obtain ⟨k, hk⟩ : ∃ k, N = d1 * k ∧ 2 ≤ k := by
        aesop;
        exact Exists.elim left fun k hk => ⟨ k, hk, by nlinarith only [ hk, right, left_3, left_4 ] ⟩;
      rw [ Nat.le_div_iff_mul_le ] <;> nlinarith only [ hk ];
    -- Since $3 \nmid N$, we have $d_2 \leq N/4$.
    have hd2_eq : d2 ≤ N / 4 := by
      rw [ Nat.le_div_iff_mul_le ] <;> aesop;
      rcases left_1 with ⟨ k, hk ⟩;
      rcases k with ( _ | _ | _ | _ | k ) <;> simp_all ( config := { decide := Bool.true } );
      grind;
    grind

/-
For an integer $N$ with smallest divisors greater than 1 being $d_1 < d_2 < d_3$, the function $s(N)$ from Definition~\ref{def:s_N} is given by $s(N) = N(\frac{1}{d_1} + \frac{1}{d_2} + \frac{1}{d_3})$.
-/
lemma lem_s_N_formula (N : ℕ) (h_card : 3 ≤ N.properDivisors.card) :
  let d₁ := ((N.divisors.erase 1).sort (· ≤ ·))[0]!
  let d₂ := ((N.divisors.erase 1).sort (· ≤ ·))[1]!
  let d₃ := ((N.divisors.erase 1).sort (· ≤ ·))[2]!
  (s N : ℚ) = (N : ℚ) * (1 / (d₁ : ℚ) + 1 / (d₂ : ℚ) + 1 / (d₃ : ℚ)) := by
    -- Apply the lemma lem_s_N_smallest_divisors to express s(N) in terms of the reciprocals of the smallest divisors.
    have h_s_N : s N = N / ((N.divisors.erase 1).sort (· ≤ ·))[0]! + N / ((N.divisors.erase 1).sort (· ≤ ·))[1]! + N / ((N.divisors.erase 1).sort (· ≤ ·))[2]! := by
      -- Apply the lemma lem_s_N_smallest_divisors to conclude the proof.
      apply lem_s_N_smallest_divisors;
      assumption;
    rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ <;> aesop;
    · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n a; aesop;
    · rw [ Nat.cast_div ( Nat.dvd_of_mem_divisors <| Finset.mem_of_mem_erase <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by rw [ n ] ; simp ( config := { decide := Bool.true } ) ), Nat.cast_div ( Nat.dvd_of_mem_divisors <| Finset.mem_of_mem_erase <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by rw [ n ] ; simp ( config := { decide := Bool.true } ) ) ];
      · ring;
      · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n b; aesop;
      · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
    · have hn : a ∣ N ∧ b ∣ N ∧ c ∣ N := by
        replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; aesop;
        · specialize n a; aesop;
        · grind;
        · specialize n c; aesop;
      rw [ Nat.cast_div ( by tauto ), Nat.cast_div ( by tauto ), Nat.cast_div ( by tauto ) ] <;> ring <;> aesop;
    · -- By definition of $d₁$, $d₂$, and $d₃$, we know that $d₁$, $d₂$, and $d₃$ are the three smallest divisors of $N$ greater than 1.
      have h_divisors : d₁ ∣ N ∧ d₂ ∣ N ∧ d₃ ∣ N := by
        replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; aesop;
        · specialize n a; aesop;
        · -- By definition of $n$, we know that $b$ divides $N$.
          specialize n b; aesop;
        · specialize n c; aesop;
      rw [ Nat.cast_div, Nat.cast_div, Nat.cast_div ] <;> aesop;
      ring

/-
If an integer $N$ is divisible by 3 but not by 2, then $s(N) < N$.
-/
lemma lem_s_N_bound_yes_3_no_2 (N : ℕ) (hpos : 0 < N) (h_card : 3 ≤ N.properDivisors.card)
  (h3 : 3 ∣ N) (h2 : ¬ (2 ∣ N)) : s N < N := by
    -- Use the provided lemma lem_s_N_smallest_divisors to relate s(N) to the smallest divisors of N.
    have h_smallest : let d₁ := ((N.divisors.erase 1).sort (· ≤ ·))[0]!
      let d₂ := ((N.divisors.erase 1).sort (· ≤ ·))[1]!
      let d₃ := ((N.divisors.erase 1).sort (· ≤ ·))[2]!
      s N = N / d₁ + N / d₂ + N / d₃ := by
        exact?;
    -- Since $N$ is divisible by 3 but not by 2, the smallest three divisors of $N$ greater than 1 are at least 3, 5, and 7.
    have hd₁ : ((N.divisors.erase 1).sort (· ≤ ·))[0]! ≥ 3 := by
      have h_min_divisor1 : ∀ d ∈ N.divisors.erase 1, 3 ≤ d := by
        aesop;
        contrapose! left; interval_cases d <;> simp_all ( config := { decide := Bool.true } ) [ Nat.dvd_iff_mod_eq_zero ] ;
      rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors N |> Finset.erase <| 1 ) with ( _ | ⟨ d₁, _ | ⟨ d₂, _ | ⟨ d₃, _ | k ⟩ ⟩ ⟩ ) <;> aesop;
      · replace n := congr_arg List.length n; aesop;
        rw [ Finset.erase_eq_iff_eq_insert ] at n <;> aesop;
        rw [ Finset.eq_singleton_iff_unique_mem ] at n ; aesop;
      · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n d₁; aesop;
      · replace n := congr_arg List.length n; aesop;
        rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
        rcases N with ( _ | _ | N ) <;> simp_all +arith +decide;
      · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n d₁; aesop;
      · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n d₁; aesop;
    have hd₂ : ((N.divisors.erase 1).sort (· ≤ ·))[1]! ≥ 5 := by
      rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) ) with _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ; aesop;
      · replace n := congr_arg List.length n; aesop;
        rw [ Finset.card_erase_of_mem ] at n <;> aesop;
        rw [ ← Nat.cons_self_properDivisors ] at n <;> aesop;
      · have := Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
        have hb_ne_a : b ≠ a := by
          intro h; have := List.nodup_cons.mp ( n.symm ▸ Finset.sort_nodup _ _ ) ; aesop;
        have hb_odd : b % 2 = 1 := by
          replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n b; aesop;
          exact Nat.mod_two_ne_zero.mp fun con => by have := Nat.mod_eq_zero_of_dvd ( dvd_trans ( Nat.dvd_of_mod_eq_zero con ) left_3 ) ; aesop;
        contrapose! hb_ne_a; interval_cases b <;> interval_cases a ; trivial;
        · contradiction;
        · trivial
    have hd₃ : ((N.divisors.erase 1).sort (· ≤ ·))[2]! ≥ 7 := by
      have hd₃ : ((N.divisors.erase 1).sort (· ≤ ·))[2]! > ((N.divisors.erase 1).sort (· ≤ ·))[1]! := by
        rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ ) <;> aesop;
        · replace n := congr_arg List.length n ; simp_all +arith +decide;
          rw [ ← Nat.cons_self_properDivisors ] at * <;> aesop;
          rcases N with ( _ | _ | N ) <;> simp_all +arith +decide;
        · have := Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
          have := n ▸ Finset.sort_nodup ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
          exact lt_of_le_of_ne right right_2;
        · have := Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
          have := Finset.sort_nodup ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) ; aesop;
          exact lt_of_le_of_ne left_1 left_8;
      by_contra hd₃_lt_7;
      interval_cases _ : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) )[2]!;
      all_goals interval_cases _ : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) )[1]!;
      -- Since $6$ is a divisor of $N$, it must be that $2 \mid N$, contradicting $h2$.
      have h_contra : 6 ∣ N := by
        rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> aesop;
        · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 6; aesop;
        · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 6; aesop;
      exact h2 ( dvd_trans ( by decide ) h_contra );
    -- Substitute the bounds for the smallest divisors into the expression for $s(N)$.
    have h_bound : s N ≤ N / 3 + N / 5 + N / 7 := by
      exact h_smallest ▸ add_le_add_three ( Nat.div_le_div_left hd₁ ( by decide ) ) ( Nat.div_le_div_left hd₂ ( by decide ) ) ( Nat.div_le_div_left hd₃ ( by decide ) );
    grind

/-
If an integer $N$ is not divisible by 6, then $s(N) < N$.
-/
lemma lem_s_N_less_than_N_if_not_div_by_6 (N : ℕ) (hpos : 0 < N)
  (h_card : 3 ≤ N.properDivisors.card) (h6 : ¬ (6 ∣ N)) : s N < N := by
    -- Since $N$ is not divisible by 6, it must be either not divisible by 2, not divisible by 3, or both.
    by_cases h2 : 2 ∣ N;
    · -- Since $N$ is divisible by 2 but not by 3, we can apply the lemma lem_s_N_bound_yes_2_no_3.
      apply lem_s_N_bound_yes_2_no_3 N hpos h_card h2 (by
      exact fun h3 => h6 ( Nat.lcm_dvd h2 h3 ));
    · by_cases h3 : 3 ∣ N;
      · exact?;
      · exact?

/-
If $6|N$ and $v_2(N) \ge 2$, then $s(N) = \frac{13}{12}N$.
-/
lemma lem_s_N_val_div_by_6_v2_ge_2 (N : ℕ) (h_card : 3 ≤ N.properDivisors.card)
  (h6 : 6 ∣ N) (h_v2 : 2 ≤ padicValNat 2 N) : 12 * s N = 13 * N := by
    -- Since $6 \mid N$ and $v_2(N) \ge 2$, the three smallest divisors of $N$ greater than 1 are $2$, $3$, and $4$.
    have h_smallest_divisors : let d₁ := ((N.divisors.erase 1).sort (· ≤ ·))[0]!
                                  let d₂ := ((N.divisors.erase 1).sort (· ≤ ·))[1]!
                                  let d₃ := ((N.divisors.erase 1).sort (· ≤ ·))[2]!
                                  d₁ = 2 ∧ d₂ = 3 ∧ d₃ = 4 := by
                                    have h_smallest_divisors : ((Nat.divisors N).erase 1).sort (· ≤ ·) = (insert 2 (insert 3 (insert 4 (((Nat.divisors N).erase 1).filter (fun d => d > 4))))).sort (· ≤ ·) := by
                                      congr with x ; aesop;
                                      · rcases x with ( _ | _ | _ | _ | _ | x ) <;> simp_all +arith +decide;
                                      · exact dvd_trans ( by norm_num ) h6;
                                      · exact dvd_trans ( by norm_num ) h6;
                                      · exact dvd_trans ( pow_dvd_pow 2 h_v2 ) ( Nat.ordProj_dvd _ _ );
                                    rw [ h_smallest_divisors ];
                                    rw [ Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ] ; aesop;
                                    all_goals norm_num;
                                    · grind;
                                    · intros; linarith;
                                    · intros; linarith;
    -- Substitute the values of $d₁$, $d₂$, and $d₃$ into the formula for $s(N)$.
    have h_s_formula : s N = N * (1 / 2 + 1 / 3 + 1 / 4 : ℚ) := by
      -- Apply the formula for $s(N)$ with the known values of the divisors.
      rw [lem_s_N_formula N h_card]
      simp [h_smallest_divisors];
    exact_mod_cast ( by linarith : ( 12 : ℚ ) * s N = 13 * N )

/-
If $v_2(N)=1$, $3|N$, and $5 \nmid N$, then $s(N) = N$.
-/
lemma lem_s_N_val_div_by_6_v2_eq_1_no_5 (N : ℕ) (h_card : 3 ≤ N.properDivisors.card)
  (h_v2 : padicValNat 2 N = 1) (h3 : 3 ∣ N) (h5 : ¬ (5 ∣ N)) : s N = N := by
    -- Since $N$ is divisible by 3 and not by 5, the three largest proper divisors are $N/2$, $N/3$, and $N/6$.
    have h_divisors : (N.divisors.erase 1).sort (· ≤ ·) = [2, 3, 6] ++ ((N.divisors.erase 1).erase 2 |>.erase 3 |>.erase 6 |>.sort (· ≤ ·)) := by
      -- Since $2$, $3$, and $6$ are the smallest divisors of $N$ greater than $1$, they must appear first in the sorted list of divisors.
      have h_smallest_divisors : 2 ∈ N.divisors.erase 1 ∧ 3 ∈ N.divisors.erase 1 ∧ 6 ∈ N.divisors.erase 1 ∧ ∀ d ∈ N.divisors.erase 1, d < 2 → False ∧ ∀ d ∈ N.divisors.erase 1, d < 3 → False ∧ ∀ d ∈ N.divisors.erase 1, d < 6 → False := by
        aesop;
        · -- Since the 2-adic valuation of N is 1, it means that 2 divides N.
          have h_two_div : 2 ^ 1 ∣ N := by
            exact h_v2 ▸ Nat.ordProj_dvd _ _;
          exact h_two_div;
        · exact Nat.lcm_dvd h3 ( show 2 ∣ N from ( by contrapose! h_v2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ) );
        · exact Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos a_1 ( Nat.pos_of_ne_zero a_2 ) ) ( Ne.symm a );
      have h_sorted_divisors : Finset.sort (· ≤ ·) (insert 2 (insert 3 (insert 6 ((N.divisors.erase 1).erase 2 |>.erase 3 |>.erase 6)))) = [2, 3, 6] ++ Finset.sort (· ≤ ·) ((N.divisors.erase 1).erase 2 |>.erase 3 |>.erase 6) := by
        rw [ Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
        all_goals simp_all ( config := { decide := Bool.true } );
        · intro b hb hb' hb'' hb''' hb''''; contrapose! hb; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
          obtain ⟨ k, hk ⟩ := hb''''; simp_all ( config := { decide := Bool.true } ) [ padicValNat.mul ] ;
          exact absurd h_v2 ( by { exact ne_of_gt ( lt_add_of_lt_of_nonneg ( by native_decide ) ( Nat.zero_le _ ) ) } );
        · grind;
      convert h_sorted_divisors using 2;
      ext d; by_cases hd2 : d = 2 <;> by_cases hd3 : d = 3 <;> by_cases hd6 : d = 6 <;> aesop;
    -- Substitute the values of $d₁$, $d₂$, and $d₃$ into the formula for $s(N)$.
    have h_s_formula : s N = N * (1 / 2 + 1 / 3 + 1 / 6 : ℚ) := by
      rw [ lem_s_N_formula ];
      · -- Since the list is [2, 3, 6], the first three elements are indeed 2, 3, and 6. Therefore, the sum of their reciprocals is 1/2 + 1/3 + 1/6.
        simp [h_divisors];
      · assumption;
    exact_mod_cast ( by linarith : ( s N : ℚ ) = N )

/-
If $v_2(N)=1$, $3|N$, and $5|N$, then $s(N) = \frac{31}{30}N$.
-/
lemma lem_s_N_val_div_by_6_v2_eq_1_yes_5 (N : ℕ) (h_card : 3 ≤ N.properDivisors.card)
  (h_v2 : padicValNat 2 N = 1) (h3 : 3 ∣ N) (h5 : 5 ∣ N) : 30 * s N = 31 * N := by
    -- By Lemma~\ref{lem:s_N_formula}, $s(N) = N(\frac{1}{2}+\frac{1}{3}+\frac{1}{5})$.
    have h_s_formula : s N = N * (1 / 2 + 1 / 3 + 1 / 5 : ℚ) := by
      -- Since $N$ is divisible by 2, 3, and 5, and $v_2(N) = 1$, the three smallest divisors greater than 1 are 2, 3, and 5.
      have h_divisors : ((N.divisors.erase 1).sort (· ≤ ·))[0]! = 2 ∧ ((N.divisors.erase 1).sort (· ≤ ·))[1]! = 3 ∧ ((N.divisors.erase 1).sort (· ≤ ·))[2]! = 5 := by
        -- Since $N$ is divisible by $2$, $3$, and $5$, these are the smallest divisors greater than $1$.
        have h_smallest_divisors : (Nat.divisors N).erase 1 = insert 2 (insert 3 (insert 5 ((Nat.divisors N).erase 1 \ {2, 3, 5}))) := by
          ext; aesop;
          · tauto;
          · -- Since the p-adic valuation of 2 in N is 1, it means that 2 divides N.
            have h2 : 2 ^ 1 ∣ N := by
              exact h_v2 ▸ Nat.ordProj_dvd _ _;
            exact h2;
        -- Since the list is sorted, the first three elements are the smallest elements in the set.
        have h_sorted : (Finset.sort (· ≤ ·) (Insert.insert 2 (Insert.insert 3 (Insert.insert 5 ((Nat.divisors N).erase 1 \ {2, 3, 5}))))).take 3 = [2, 3, 5] := by
          rw [ Finset.sort_insert, Finset.sort_insert, Finset.sort_insert ];
          all_goals norm_num [ Finset.mem_insert, Finset.mem_singleton ];
          · intro b hb h2 h3 h4 h5 h6; contrapose! hb; interval_cases b <;> simp_all ( config := { decide := Bool.true } ) ;
            obtain ⟨ k, hk ⟩ := h2; simp_all ( config := { decide := Bool.true } ) [ padicValNat.mul ] ;
            exact absurd h_v2 ( by { exact ne_of_gt ( lt_add_of_lt_of_nonneg ( by native_decide ) ( Nat.zero_le _ ) ) } );
          · intro a ha₁ ha₂ ha₃ ha₄ ha₅ ha₆; contrapose! ha₁; interval_cases a <;> simp_all ( config := { decide := Bool.true } ) ;
          · exact fun a ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ => Nat.lt_of_le_of_ne ( Nat.pos_of_dvd_of_pos ha₂ ( Nat.pos_of_ne_zero ha₃ ) ) ( Ne.symm ha₁ );
        rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Insert.insert 2 ( Insert.insert 3 ( Insert.insert 5 ( N.divisors.erase 1 \ { 2, 3, 5 } ) ) ) ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ <;> simp ( config := { decide := Bool.true } ) [ n ] at h_sorted ⊢;
        · grind;
        · -- Substitute the values from h_sorted into the list n to conclude the proof.
          simp [h_sorted] at *;
          rw [ h_smallest_divisors ] ; simp ( config := { decide := Bool.true } ) [ n ] ;
      rw [ lem_s_N_formula N h_card ];
      aesop;
    exact_mod_cast ( by linarith : ( 30 : ℚ ) * s N = 31 * N )

/-
If $N$ is an odd integer, then $s(N)$ is odd and therefore not divisible by 6.
-/
lemma lem_preservation_of_not_div_6_odd (N : ℕ) (h_card : 3 ≤ N.properDivisors.card)
  (h_odd : Odd N) : Odd (s N) := by
    -- Since $N$ is odd, all its divisors are odd. Therefore, each of the three largest proper divisors is odd.
    have h_divisors_odd : ∀ d ∈ N.properDivisors, Odd d := by
      exact fun d hd => h_odd.of_dvd_nat <| Nat.mem_properDivisors.mp hd |>.1;
    -- Since the three largest proper divisors of $N$ are all odd, their sum $s(N)$ is also odd.
    have h_sum_odd : ∀ {l : List ℕ}, (∀ d ∈ l, Odd d) → List.length l ≥ 3 → Odd (l.get! 0 + l.get! 1 + l.get! 2) := by
      intros l hl hl'; rcases l with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | l ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide [ parity_simps ] ;
      · aesop;
        · exact absurd a_1 ( by simpa using left_1 );
        · exact absurd a_1 ( by simpa using right );
      · aesop;
        · -- Since $b$ is both odd and even, this is a contradiction.
          exfalso; exact absurd a_1 (by simpa using left_1);
        · exact absurd a_1 ( by simpa using left_2 );
    unfold s; aesop;

/-
If an integer $N$ satisfies the conditions of Lemma~\ref{lem:necessary_conditions_summary}, then $N$ is of the form $6 \cdot 12^a \cdot m$ for some integer $a \ge 0$ and a positive integer $m$ with $\gcd(m,10)=1$.
-/
lemma lem_conditions_imply_form (N a : ℕ) (hN : 0 < N) (h_v2 : padicValNat 2 N = 2 * a + 1)
  (h_v3 : a + 1 ≤ padicValNat 3 N) (h_v5 : padicValNat 5 N = 0) :
  ∃ m, 0 < m ∧ Nat.Coprime m 10 ∧ N = 6 * 12^a * m := by
    -- We can write $N = 2^{2a+1} \cdot 3^{a+1} \cdot M$, where $M$ is not divisible by 2, 3, or 5.
    obtain ⟨M, hM⟩ : ∃ M, N = 2^(2*a+1) * 3^(a+1) * M := by
      -- Since $2^{2a+1}$ and $3^{a+1}$ are coprime and both divide $N$, their product $2^{2a+1} \cdot 3^{a+1}$ must also divide $N$.
      have h_coprime : Nat.gcd (2^(2*a+1)) (3^(a+1)) = 1 := by
        norm_num;
      apply_mod_cast Nat.Coprime.mul_dvd_of_dvd_of_dvd <;> aesop;
      · exact h_v2 ▸ Nat.ordProj_dvd _ _;
      · exact dvd_trans ( pow_dvd_pow _ h_v3 ) ( Nat.ordProj_dvd _ _ );
    refine' ⟨ M, _, _, _ ⟩;
    · -- Since $N$ is positive and $N = 2^{2a+1} \cdot 3^{a+1} \cdot M$, if $M$ were zero or negative, then $N$ would be zero or negative, which contradicts $hN$. Therefore, $M$ must be positive.
      aesop;
    · rw [ show 10 = 2 * 5 by norm_num, Nat.coprime_mul_iff_right ] ; aesop;
      · contrapose! h_1;
        rw [ padicValNat.mul, padicValNat.mul ] at * <;> aesop;
        simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd, ← even_iff_two_dvd, parity_simps ];
      · exact Nat.Coprime.symm ( Nat.Prime.coprime_iff_not_dvd ( by norm_num ) |>.2 fun h => h_1 <| dvd_mul_of_dvd_right h _ );
    · rw [ hM ] ; ring;
      norm_num [ pow_mul', mul_assoc, ← mul_pow ]

/-
If $a_1$ has the form $6 \cdot 12^a \cdot m$ for $a \ge 0$ and $\gcd(m,10)=1$, it generates an infinite sequence.
-/
lemma lem_sufficiency_stabilization (a m : ℕ) (hm : 0 < m) (h_coprime : Nat.Coprime m 10) :
  ∃ a_seq : ℕ → ℕ, a_seq 0 = 6 * 12^a * m ∧
    (∀ n, 0 < a_seq n) ∧
    (∀ n, 3 ≤ (a_seq n).properDivisors.card) ∧
    (∀ n, a_seq (n + 1) = s (a_seq n)) := by
      -- Now consider the sequence starting at $a_1 = 6 \cdot 12^a \cdot m$. We need to show that this generates an infinite sequence.
      use fun n => if n ≤ a then (6 * 12^(a - n) * m) * 13^n else (6 * m) * 13^a;
      refine' ⟨ _, _, _, _ ⟩;
      · aesop;
      · aesop;
      · aesop;
        · -- Since $6 * 12^(a-n) * m * 13^n$ is divisible by $6$, it has at least the proper divisors $1$, $2$, and $3$.
          have h_divisors : {1, 2, 3} ⊆ (6 * 12^(a-n) * m * 13^n).properDivisors := by
            norm_num [ Finset.insert_subset_iff ];
            exact ⟨ by nlinarith [ pow_pos ( by decide : 0 < 12 ) ( a - n ), pow_pos ( by decide : 0 < 13 ) n, mul_pos hm ( pow_pos ( by decide : 0 < 12 ) ( a - n ) ) ], ⟨ Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.mul_mod, Nat.pow_mod ] ), by nlinarith [ pow_pos ( by decide : 0 < 12 ) ( a - n ), pow_pos ( by decide : 0 < 13 ) n, mul_pos hm ( pow_pos ( by decide : 0 < 12 ) ( a - n ) ) ] ⟩, Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.mul_mod, Nat.pow_mod ] ), by nlinarith [ pow_pos ( by decide : 0 < 12 ) ( a - n ), pow_pos ( by decide : 0 < 13 ) n, mul_pos hm ( pow_pos ( by decide : 0 < 12 ) ( a - n ) ) ] ⟩;
          exact Finset.card_mono h_divisors;
        · -- Let's choose any $n$ such that $a < n$. We need to show that $6 * m * 13^a$ has at least three proper divisors.
          have h_divisors : (6 * m * 13^a).properDivisors ⊇ {1, 2, 3} := by
            norm_num [ Finset.insert_subset_iff ];
            exact ⟨ by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ], ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ] ⟩, dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ] ⟩;
          exact Finset.card_mono h_divisors;
      · aesop;
        · -- By definition of $s$, we know that $s(N) = \frac{13}{12}N$ for $N = 6 \cdot 12^a \cdot m$.
          have h_s : ∀ a m : ℕ, 0 < m → Nat.Coprime m 10 → a ≥ 1 → s (6 * 12 ^ a * m) = 6 * 12 ^ (a - 1) * m * 13 := by
            intros a m hm h_coprime ha;
            have h_s : 12 * s (6 * 12 ^ a * m) = 13 * (6 * 12 ^ a * m) := by
              apply lem_s_N_val_div_by_6_v2_ge_2;
              · refine' Finset.two_lt_card.mpr _;
                norm_num;
                exact ⟨ 1, ⟨ one_dvd _, by nlinarith [ pow_pos ( by decide : 0 < 12 ) a ] ⟩, 2, ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 12 ) a ] ⟩, 3, ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 12 ) a ] ⟩, by decide, by decide, by decide ⟩;
              · exact dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
              · rw [ padicValNat.mul, padicValNat.mul ] <;> aesop;
                simp +arith +decide [ padicValNat.pow ];
                exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( by nlinarith [ show padicValNat 2 12 ≥ 2 by native_decide ] );
            cases a <;> norm_num [ pow_succ' ] at * ; linarith;
          rw [ show a - n = a - ( n + 1 ) + 1 by omega ] ; simp ( config := { decide := Bool.true } ) [ *, pow_succ, mul_assoc ];
          convert h_s ( a - ( n + 1 ) + 1 ) ( m * 13 ^ n ) ( by positivity ) ( by exact Nat.Coprime.mul h_coprime ( by cases n <;> norm_num ) ) ( by linarith [ Nat.sub_add_cancel h ] ) |> Eq.symm using 1 ; ring;
          · norm_num;
          · ring;
        · linarith;
        · cases eq_or_lt_of_le h_1 <;> first | linarith | aesop;
          -- By definition of $s$, we know that $s(6 * m * 13^n) = 6 * m * 13^n$.
          apply Eq.symm;
          apply lem_s_N_val_div_by_6_v2_eq_1_no_5;
          · -- Since $6 * m * 13^n$ is divisible by $6$, it has at least the proper divisors $1$, $2$, and $3$.
            have h_divisors : {1, 2, 3} ⊆ (6 * m * 13 ^ n).properDivisors := by
              norm_num [ Finset.insert_subset_iff ];
              exact ⟨ by nlinarith [ pow_pos ( by decide : 0 < 13 ) n ], ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) n ] ⟩, dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) n ] ⟩;
            exact Finset.card_mono h_divisors;
          · norm_num [ padicValNat.mul, hm.ne', show m ≠ 0 by linarith ];
            rw [ show ( 6 : ℕ ) = 2 * 3 by norm_num, padicValNat.mul ] <;> norm_num;
            norm_num [ padicValNat.eq_zero_of_not_dvd, Nat.Prime.dvd_iff_one_le_factorization ];
            exact Or.inr ( Nat.mod_two_ne_zero.mp fun contra => by have := Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero contra ) ( by decide : 2 ∣ 10 ) ; simp_all ( config := { decide := Bool.true } ) );
          · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _;
          · norm_num [ Nat.Prime.dvd_mul, Nat.Prime.dvd_iff_one_le_factorization ];
            exact fun h => by have := Nat.dvd_gcd h ( by decide : 5 ∣ 10 ) ; simp_all ( config := { decide := Bool.true } ) ;
        · -- By definition of $s$, we know that $s(6 * m * 13^a) = 6 * m * 13^a$.
          have h_s : s (6 * m * 13 ^ a) = 6 * m * 13 ^ a := by
            apply lem_s_N_val_div_by_6_v2_eq_1_no_5;
            · -- Since $6 * m * 13^a$ is divisible by $6$, it has at least the proper divisors $1$, $2$, and $3$.
              have h_divisors : Nat.properDivisors (6 * m * 13 ^ a) ⊇ {1, 2, 3} := by
                norm_num [ Finset.insert_subset_iff ];
                exact ⟨ by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ], ⟨ dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ] ⟩, dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _, by nlinarith [ pow_pos ( by decide : 0 < 13 ) a ] ⟩;
              exact Finset.card_mono h_divisors;
            · rw [ padicValNat.mul, padicValNat.mul ] <;> norm_num;
              · rw [ show ( 6 : ℕ ) = 2 * 3 by norm_num, padicValNat.mul ] <;> norm_num;
                norm_num [ padicValNat.eq_zero_of_not_dvd, Nat.Prime.dvd_iff_one_le_factorization ];
                exact Or.inr ( Nat.mod_two_ne_zero.mp fun contra => by have := Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero contra ) ( by decide : 2 ∣ 10 ) ; simp_all ( config := { decide := Bool.true } ) );
              · linarith;
              · linarith;
            · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( by decide ) _ ) _;
            · norm_num [ Nat.Prime.dvd_mul, Nat.Prime.dvd_iff_one_le_factorization ];
              exact fun h => by have := Nat.dvd_gcd h ( by decide : 5 ∣ 10 ) ; simp_all ( config := { decide := Bool.true } ) ;
          exact h_s.symm

/-
If an integer $N$ is even and not divisible by 3, then $s(N)$ is not divisible by 6.
-/
lemma lem_preservation_of_not_div_6_no_3_even (N : ℕ) (h_card : 3 ≤ N.properDivisors.card)
  (h_even : Even N) (h3 : ¬ (3 ∣ N)) : ¬ (6 ∣ s N) := by
    -- If $N$ is even, then $d_1 = 2$.
    obtain ⟨d₁, hd₁⟩ : ∃ d₁, ((N.divisors.erase 1).sort (· ≤ ·))[0]! = 2 ∧ d₁ ∈ N.divisors.erase 1 := by
      -- Since $N$ is even, $2$ is a divisor of $N$. Also, since $N$ is not divisible by $3$, $3$ is not a divisor. The smallest divisor greater than $1$ for an even number is $2$. So, $2$ must be in the set of divisors of $N$ excluding $1$.
      have h_two_div : 2 ∈ N.divisors.erase 1 := by
        aesop;
        exact even_iff_two_dvd.mp h_even;
      rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) with _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ; aesop;
      · replace n := congr_arg List.length n ; aesop;
        exact absurd n ( Nat.sub_ne_zero_of_lt ( lt_of_lt_of_le ( by decide ) ( Finset.one_lt_card.2 ⟨ 1, by aesop_cat, by aesop_cat ⟩ ) ) );
      · replace n := congr_arg List.length n; aesop;
        · rw [ ← Nat.cons_self_properDivisors ] at n <;> aesop;
        · exact ⟨ 2, by decide, left ⟩;
      · have := Finset.sort_sorted ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) ; aesop;
        · have := n ▸ Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 ( show 2 ∈ N.divisors.erase 1 from by aesop ) ; aesop;
          · interval_cases x <;> simp_all ( config := { decide := Bool.true } );
            · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
            · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 1; aesop;
          · have := right_2 2 h_2; have := left_2 2 h_2; interval_cases x <;> interval_cases y <;> simp_all ( config := { decide := Bool.true } ) ;
            · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
            · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
            · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 0; aesop;
            · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 1; aesop;
            · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n 1; aesop;
        · exact ⟨ 2, by decide, left ⟩;
    -- Let $d_2$ and $d_3$ be the second and third smallest divisors of $N$ greater than 1.
    obtain ⟨d₂, hd₂⟩ : ∃ d₂, ((N.divisors.erase 1).sort (· ≤ ·))[1]! = d₂ ∧ d₂ ∈ N.divisors.erase 1 ∧ d₂ > 2 := by
      rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Nat.divisors N |> Finset.erase <| 1 ) with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> aesop;
      · replace x := congr_arg List.length x ; aesop;
        rw [ ← Nat.cons_self_properDivisors right ] at x ; aesop;
      · have := x ▸ Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
      · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x b; aesop;
      · have := Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
        refine' lt_of_le_of_ne left ( Ne.symm _ );
        have := x ▸ Finset.sort_nodup ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
    -- Let $d_3$ be the third smallest divisor of $N$ greater than 1.
    obtain ⟨d₃, hd₃⟩ : ∃ d₃, ((N.divisors.erase 1).sort (· ≤ ·))[2]! = d₃ ∧ d₃ ∈ N.divisors.erase 1 ∧ d₃ > d₂ := by
      rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ <;> aesop;
      all_goals have := Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; simp_all ( config := { decide := Bool.true } );
      · replace n := congr_arg List.length n ; simp_all ( config := { decide := Bool.true } );
        rw [ ← Nat.cons_self_properDivisors ] at n <;> aesop;
      · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n c; aesop;
      · -- Since the divisors are distinct, b cannot be equal to c, so we must have b < c.
        have h_distinct : b ≠ c := by
          have := Finset.sort_nodup ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
        exact lt_of_le_of_ne this.2 h_distinct;
      · replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n c; aesop;
      · have := n ▸ Finset.sort_nodup ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
        exact lt_of_le_of_ne left_5 left_6;
    -- If $v_2(N) \ge 2$, then $d_2 = 4$. Since $3 \nmid N$, we have $3 \nmid d_3$. Then $s(N) = N(\frac{1}{2}+\frac{1}{4}+\frac{1}{d_3}) = N\frac{3d_3+4}{4d_3}$. Since $s(N)$ is an integer, and $v_3(N)=0, v_3(d_3)=0$, we must have $v_3(s(N)) = v_3(3d_3+4)$. As $d_3 \not\equiv 0 \pmod 3$, $3d_3+4 \equiv 1 \pmod 3$, so $v_3(3d_3+4)=0$. Thus, $v_3(s(N))=0$, so $s(N)$ is not divisible by 3, and therefore not by 6.
    by_cases h_v2 : d₂ = 4;
    · have h_s_formula : (s N : ℚ) = (N : ℚ) * (1 / 2 + 1 / 4 + 1 / d₃) := by
        have := lem_s_N_formula N h_card; aesop;
      -- Since $s(N)$ is an integer, and $v_3(N)=0, v_3(d_3)=0$, we must have $v_3(s(N)) = v_3(3d_3+4)$. As $d_3 \not\equiv 0 \pmod 3$, $3d_3+4 \equiv 1 \pmod 3$, so $v_3(3d_3+4)=0$. Thus, $v_3(s(N))=0$, so $s(N)$ is not divisible by 3, and therefore not by 6.
      have h_not_div_3 : ¬(3 ∣ s N) := by
        -- Since $s(N)$ is an integer, and $v_3(N)=0, v_3(d_3)=0$, we must have $v_3(s(N)) = v_3(3d_3+4)$. As $d_3 \not\equiv 0 \pmod 3$, $3d_3+4 \equiv 1 \pmod 3$, so $v_3(3d_3+4)=0$. Thus, $v_3(s(N))=0$, so $s(N)$ is not divisible by 3.
        have h_not_div_3 : ¬(3 ∣ (N * (3 * d₃ + 4))) := by
          norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod ] at * ; aesop;
        contrapose! h_not_div_3;
        convert h_not_div_3.mul_right ( 4 * d₃ ) using 1;
        rw [ ← @Nat.cast_inj ℚ ] ; push_cast ; rw [ h_s_formula ] ; ring;
        simpa [ show d₃ ≠ 0 by linarith ] using by ring;
      exact fun h => h_not_div_3 ( dvd_trans ( by decide ) h );
    · -- If $v_2(N) = 1$, then $d_2$ is an odd prime $p$. Since $3 \nmid N$, $p \ge 5$. The third smallest divisor $d_3$ is the minimum of $\{p^2, q, 2p\}$, where $q$ is the next smallest prime factor of $N$.
      by_cases h_odd_p : d₂ % 2 = 1;
      · -- If $d_3$ is odd, then $N/2$ is odd, while $N/d_2$ and $N/d_3$ are even. Their sum $s(N)$ is odd. An odd number is not divisible by 6.
        by_cases h_odd_d3 : d₃ % 2 = 1;
        · -- Since $N/2$ is odd and $N/d₂$ and $N/d₃$ are even, their sum $s(N)$ is odd.
          have h_odd_sN : Odd (s N) := by
            have h_odd_sN : Odd (N / 2 + N / d₂ + N / d₃) := by
              have h_odd_sN : Odd (N / 2) ∧ Even (N / d₂) ∧ Even (N / d₃) := by
                aesop;
                · -- Since the second smallest divisor is an odd prime, N cannot be divisible by 4, which implies that N/2 is odd.
                  have h_not_div_4 : ¬(4 ∣ N) := by
                    contrapose! h_v2;
                    rcases x : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | k ⟩ ⟩ ⟩ <;> aesop;
                    · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 4; aesop;
                    · have y := @x ▸ Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
                      replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x 4; aesop;
                      · interval_cases b <;> interval_cases c <;> trivial;
                      · grind;
                  exact Nat.odd_iff.mpr ( by obtain ⟨ k, hk ⟩ := even_iff_two_dvd.mp h_even; omega );
                · rw [ Nat.even_iff ];
                  rw [ ← Nat.dvd_iff_mod_eq_zero ];
                  exact Nat.Coprime.dvd_of_dvd_mul_left ( show Nat.Coprime 2 ( ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) )[1]?.getD 0 ) from Nat.prime_two.coprime_iff_not_dvd.mpr <| by omega ) <| Nat.dvd_trans ( even_iff_two_dvd.mp h_even ) <| by simpa [ Nat.mul_div_cancel' right_3 ] ;
                · rw [ even_iff_two_dvd ];
                  rw [ Nat.dvd_div_iff_mul_dvd ];
                  · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by rw [ ← Nat.mod_add_div ( ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) )[2]?.getD 0 ) 2 ] ; aesop ) right_4 ( even_iff_two_dvd.mp h_even );
                  · aesop;
              simp_all ( config := { decide := Bool.true } ) [ parity_simps ];
            convert h_odd_sN using 1;
            convert lem_s_N_smallest_divisors N h_card using 1;
            rw [ hd₁.1, hd₂.1, hd₃.1 ];
          exact fun h => absurd ( h_odd_sN.of_dvd_nat h ) ( by decide );
        · -- If $d_3$ is even, then $d_3 = 2p$. This is the smallest even divisor greater than 2. This case applies if $2p$ is smaller than any odd divisor of $N$ greater than $p$. Then $s(N) = N(\frac{1}{2}+\frac{1}{p}+\frac{1}{2p}) = N\frac{p+3}{2p}$. Since $p \ge 5$, $p$ is not divisible by 3. $p+3$ is divisible by 3 only if $p$ is, so $v_3(p+3)=0$. As $v_3(N)=0$ and $v_3(p)=0$, we have $v_3(s(N))=v_3(N)+v_3(p+3)-v_3(2p)=0$. So $3 \nmid s(N)$, which means $6 \nmid s(N)$.
          have h_even_d3 : d₃ = 2 * d₂ := by
            have h_even_d3 : d₃ ≤ 2 * d₂ := by
              have h_even_d3 : 2 * d₂ ∈ N.divisors.erase 1 := by
                aesop;
                exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by omega ) ( even_iff_two_dvd.mp h_even ) right_3;
              have h_even_d3 : 2 * d₂ ∈ Finset.sort (· ≤ ·) (N.divisors.erase 1) := by
                exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 h_even_d3;
              rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ <;> aesop;
              · linarith;
              · linarith;
              · have := Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
              · have := Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
            have h_even_d3 : d₃ ≥ 2 * d₂ := by
              have h_even_d3 : d₃ % 2 = 0 := by
                exact Nat.mod_two_ne_one.mp h_odd_d3;
              have h_even_d3 : d₃ / 2 ≥ d₂ := by
                have h_even_d3 : d₃ / 2 ∈ N.divisors.erase 1 := by
                  aesop;
                  · grind;
                  · exact Nat.dvd_trans ( Nat.div_dvd_of_dvd <| Nat.dvd_of_mod_eq_zero h_even_d3 ) right_4;
                have h_even_d3 : d₃ / 2 ∈ Finset.sort (· ≤ ·) (N.divisors.erase 1) := by
                  exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 h_even_d3;
                rcases n : Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) with _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | n ⟩ ⟩ ⟩ <;> aesop;
                any_goals omega;
                · have := Nat.div_mul_cancel ( Nat.dvd_of_mod_eq_zero h_even_d3_2 ) ; aesop;
                  interval_cases b ; trivial;
                · have := Nat.div_mul_cancel ( Nat.dvd_of_mod_eq_zero h_even_d3_2 ) ; aesop;
                  interval_cases b ; trivial;
                · have := n ▸ Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
                · have := Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
              linarith [ Nat.mod_add_div d₃ 2 ];
            linarith;
          have h_simplified : s N = (N : ℚ) * (1 / 2 + 1 / d₂ + 1 / (2 * d₂)) := by
            have := lem_s_N_formula N h_card; aesop;
          -- Since $p \ge 5$, $p$ is not divisible by 3. $p+3$ is divisible by 3 only if $p$ is, so $v_3(p+3)=0$. As $v_3(N)=0$ and $v_3(p)=0$, we have $v_3(s(N))=v_3(N)+v_3(p+3)-v_3(2p)=0$. So $3 \nmid s(N)$, which means $6 \nmid s(N)$.
          have h_not_div_3 : ¬(3 ∣ s N) := by
            have h_not_div_3 : ¬(3 ∣ (N * (d₂ + 3))) := by
              simp_all ( config := { decide := Bool.true } ) [ Nat.Prime.dvd_mul ];
              exact fun h => h3 <| dvd_trans h hd₂.2.1.2;
            -- Since $3 \nmid N * (d₂ + 3)$ and $2 * d₂$ is not divisible by 3, the division by $2 * d₂$ doesn't introduce any factors of 3. Therefore, $s N$ can't be divisible by 3.
            have h_div : s N = (N * (d₂ + 3)) / (2 * d₂) := by
              rw [ Nat.div_eq_of_eq_mul_left ];
              · linarith;
              · rw [ ← @Nat.cast_inj ℚ ] ; push_cast ; rw [ h_simplified ] ; ring;
                simpa [ show d₂ ≠ 0 by linarith ] using by ring;
            exact fun h => h_not_div_3 <| dvd_trans h <| h_div.symm ▸ Nat.div_dvd_of_dvd <| show 2 * d₂ ∣ N * ( d₂ + 3 ) from Nat.Coprime.mul_dvd_of_dvd_of_dvd ( show Nat.Coprime ( 2 ) ( d₂ ) from Nat.prime_two.coprime_iff_not_dvd.mpr <| by omega ) ( show 2 ∣ N * ( d₂ + 3 ) from dvd_mul_of_dvd_left ( even_iff_two_dvd.mp h_even ) _ ) ( show d₂ ∣ N * ( d₂ + 3 ) from dvd_mul_of_dvd_left ( Nat.dvd_of_mem_divisors <| Finset.mem_of_mem_erase hd₂.2.1 ) _ );
          exact fun h => h_not_div_3 ( dvd_trans ( by decide ) h );
      · contrapose! h_v2;
        aesop;
        rcases n : ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( N.divisors.erase 1 ) ) with _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ; aesop;
        · aesop;
        · -- Since the second element is even and greater than 2, the smallest possible value is 4.
          have h_second : (Finset.sort (fun x1 x2 => x1 ≤ x2) (N.divisors.erase 1))[1]?.getD 0 = 4 := by
            have h_even : (Finset.sort (fun x1 x2 => x1 ≤ x2) (N.divisors.erase 1))[1]?.getD 0 % 2 = 0 := h_odd_p
            have h_gt_two : 2 < (Finset.sort (fun x1 x2 => x1 ≤ x2) (N.divisors.erase 1))[1]?.getD 0 := right_1
            aesop;
            have := Nat.dvd_of_mod_eq_zero h_odd_p; obtain ⟨ k, hk ⟩ := this; aesop;
            have := Finset.sort_sorted ( · ≤ · ) ( N.divisors.erase 1 ) ; aesop;
            replace n := congr_arg List.toFinset n; rw [ Finset.ext_iff ] at n; specialize n ( k ) ; aesop;
            rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
            exact n.mp ( dvd_of_mul_left_dvd right_3 ) |> Or.resolve_right <| fun h => by linarith [ left_1 _ h ] ;
          aesop

/-
If an integer $N$ is not divisible by 6, then $s(N)$ is not divisible by 6.
-/
lemma lem_preservation_of_not_div_6 (N : ℕ) (h_card : 3 ≤ N.properDivisors.card)
  (h6 : ¬ (6 ∣ N)) : ¬ (6 ∣ s N) := by
    by_cases h_even : Even N;
    · -- Since $N$ is even and not divisible by 3, we can apply Lemma~\ref{lem:preservation_of_not_div_6_no_3_even}.
      have h_not_div_3 : ¬ (3 ∣ N) := by
        exact fun h => h6 ( Nat.lcm_dvd h_even.two_dvd h );
      exact?;
    · replace := lem_preservation_of_not_div_6_odd N h_card; aesop;
      exact absurd ( this.of_dvd_nat a ) ( by decide )

/-
If a sequence $(a_n)$ contains a term $a_k$ not divisible by 6, the sequence must terminate.
-/
lemma lem_non_div_6_terminates (a : ℕ → ℕ) (h_pos : ∀ n, 0 < a n)
  (h_succ : ∀ n, a (n + 1) = s (a n)) (h_inf : ∀ n, 3 ≤ (a n).properDivisors.card) :
  ∀ k, 6 ∣ a k := by
    -- If $a_k$ is not divisible by 6, then $s(a_k) < a_k$ and $6 \nmid s(a_k)$.
    have h_not_div_6_implies_lt_and_not_div (k : ℕ) (h_not_div : ¬(6 ∣ a k)) : s (a k) < a k ∧ ¬(6 ∣ s (a k)) := by
      -- Apply the lemma that states if $a_k$ is not divisible by 6, then $s(a_k) < a_k$.
      have h_lt : s (a k) < a k := by
        -- Apply the lemma that states if $a_k$ is not divisible by 6, then $s(a_k) < a_k$ using the given hypotheses.
        apply lem_s_N_less_than_N_if_not_div_by_6; exact h_pos k; exact h_inf k; exact h_not_div;
      -- Apply the lemma that states if $N$ is not divisible by 6, then $s(N)$ is not divisible by 6.
      apply And.intro h_lt;
      exact?;
    -- Suppose a term $a_k$ is not divisible by 6. By Lemma~\ref{lem:s_N_less_than_N_if_not_div_by_6}, we have $s(a_k) < a_k$. For the sequence to continue, $a_{k+1}=s(a_k)$ must be defined, which requires $\tau(a_k) \ge 4$. If this condition is met, we have $a_{k+1} < a_k$. By Lemma~\ref{lem:preservation_of_not_div_6}, since $6 \nmid a_k$, it follows that $6 \nmid a_{k+1}$. This argument can be applied inductively: for all $m \ge k$, if $a_m$ is defined, then $6 \nmid a_m$, so $s(a_m) < a_m$. This implies $a_{m+1} < a_m$. Thus, the sequence $(a_m)_{m \ge k}$ is a strictly decreasing sequence of positive integers.
    have h_strict_decreasing_if_not_div_6 (k : ℕ) (h_not_div : ¬(6 ∣ a k)) : ∀ m ≥ k, a (m + 1) < a m := by
      -- By induction, if $a_k$ is not divisible by 6, then all $a_m$ for $m \geq k$ are also not divisible by 6.
      have h_not_div_6_for_all_m_ge_k (k : ℕ) (h_not_div : ¬(6 ∣ a k)) : ∀ m ≥ k, ¬(6 ∣ a m) := by
        intro m hm;
        induction hm <;> aesop;
      exact fun m hm => h_succ m ▸ h_not_div_6_implies_lt_and_not_div m ( h_not_div_6_for_all_m_ge_k k h_not_div m hm ) |>.1;
    -- Such a sequence must eventually either terminate because a term has fewer than three proper divisors, or reach the value 1. In either case, the sequence terminates.
    have h_finite_if_not_div_6 (k : ℕ) (h_not_div : ¬(6 ∣ a k)) : Set.Finite (Set.range (fun m => a (k + m))) := by
      exact Set.finite_iff_bddAbove.mpr ⟨ a k, by rintro x ⟨ m, rfl ⟩ ; exact Nat.recOn m ( by norm_num ) fun n ihn => by linarith! [ h_strict_decreasing_if_not_div_6 k h_not_div ( k + n ) ( by linarith ) ] ⟩;
    -- Assume there exists some $k$ such that $6 \nmid a_k$. Then the sequence starting at $k$ is strictly decreasing and finite, contradicting the assumption that the sequence is infinite.
    by_contra h_contra
    obtain ⟨k, hk⟩ : ∃ k, ¬(6 ∣ a k) := by
      exact not_forall.mp h_contra;
    exact absurd ( h_finite_if_not_div_6 k hk ) ( Set.infinite_range_of_injective ( StrictAnti.injective ( strictAnti_nat_of_succ_lt fun m => h_strict_decreasing_if_not_div_6 k hk _ ( Nat.le_add_right _ _ ) ) ) )

/-
If $v_2(a_1)$ is an even integer, the sequence terminates.
-/
lemma lem_v2_even_terminates (a : ℕ → ℕ) (h_pos : ∀ n, 0 < a n)
  (h_succ : ∀ n, a (n + 1) = s (a n)) (h_inf : ∀ n, 3 ≤ (a n).properDivisors.card) :
  Odd (padicValNat 2 (a 0)) := by
    -- By Lemma lem_non_div_6_terminates, all terms must be divisible by 6.
    have h_all_div_6 : ∀ n, 6 ∣ a n := by
      exact?;
    -- By Lemma lem_v2_decreasing, if $v_2(a_k)$ is even, then $v_2(a_{k+1})$ is also even and smaller.
    have h_v2_decreasing : ∀ n, padicValNat 2 (a n) ≥ 2 → Even (padicValNat 2 (a n)) → padicValNat 2 (a (n + 1)) = padicValNat 2 (a n) - 2 := by
      intros n hn_ge_2 hn_even;
      -- By Lemma lem_s_N_val_div_by_6_v2_ge_2, $s(a_n) = \frac{13}{12}a_n$.
      have h_s_val : 12 * s (a n) = 13 * a n := by
        exact?;
      rw [ h_succ, show s ( a n ) = a n * 13 / 12 by rw [ Nat.div_eq_of_eq_mul_left ] <;> linarith ];
      rw [ padicValNat.div_of_dvd ];
      · rw [ padicValNat.mul ] <;> norm_num;
        · rw [ show padicValNat 2 12 = 2 by native_decide, show padicValNat 2 13 = 0 by native_decide ] ; norm_num;
        · linarith [ h_pos n ];
      · exact ⟨ s ( a n ), by linarith ⟩;
    -- By contradiction, assume $v_2(a_0)$ is even.
    by_contra h_even;
    -- Since $v_2(a_0)$ is even, by induction, $v_2(a_n)$ is also even and smaller for all $n$.
    have h_v2_even_all : ∀ n, Even (padicValNat 2 (a n)) := by
      -- By induction on $n$, we can show that $v_2(a_n)$ is even for all $n$.
      intro n
      induction' n with n ih;
      · simpa using h_even;
      · by_cases h₂ : padicValNat 2 (a n) ≥ 2;
        · rw [ h_v2_decreasing n h₂ ih ];
          exact even_iff_two_dvd.mpr ( Nat.dvd_sub' ( even_iff_two_dvd.mp ih ) ( dvd_refl 2 ) );
        · interval_cases _ : padicValNat 2 ( a n ) <;> simp_all ( config := { decide := Bool.true } );
          exact absurd ( ‹a n = 0 ∨ a n % 2 = 1›.resolve_left ( ne_of_gt ( h_pos n ) ) ) ( by obtain ⟨ k, hk ⟩ := h_all_div_6 n; norm_num [ Nat.add_mod, Nat.mul_mod, hk ] );
    -- Since $v_2(a_n)$ is even and smaller for all $n$, it must eventually become negative.
    have h_v2_neg : ∃ n, padicValNat 2 (a n) < 2 := by
      -- Since $v_2(a_n)$ is even and smaller for all $n$, it must eventually become negative. We can use induction to show this.
      have h_v2_decreasing_induction : ∀ n, padicValNat 2 (a n) ≥ 2 → padicValNat 2 (a (n + 1)) < padicValNat 2 (a n) := by
        exact fun n hn => h_v2_decreasing n hn ( h_v2_even_all n ) ▸ Nat.sub_lt ( by linarith ) ( by linarith );
      by_cases h₂ : ∀ n, padicValNat 2 (a n) ≥ 2;
      · -- Since $v_2(a_n)$ is strictly decreasing and bounded below by 2, it must eventually reach 0.
        have h_v2_finite : Set.Finite (Set.range (fun n => padicValNat 2 (a n))) := by
          exact Set.finite_iff_bddAbove.mpr ⟨ padicValNat 2 ( a 0 ), by rintro x ⟨ n, rfl ⟩ ; exact Nat.recOn n ( by norm_num ) fun n ihn => by linarith [ h_v2_decreasing_induction n ( h₂ n ) ] ⟩;
        exact False.elim <| h_v2_finite.not_infinite <| Set.infinite_range_of_injective ( StrictAnti.injective <| strictAnti_nat_of_succ_lt fun n => h_v2_decreasing_induction n <| h₂ n );
      · aesop;
    obtain ⟨ n, hn ⟩ := h_v2_neg;
    interval_cases _ : padicValNat 2 ( a n ) <;> simp_all ( config := { decide := Bool.true } );
    · exact absurd ( ‹a n = 0 ∨ a n % 2 = 1›.resolve_left ( ne_of_gt ( h_pos n ) ) ) ( by obtain ⟨ k, hk ⟩ := h_all_div_6 n; norm_num [ Nat.add_mod, Nat.mul_mod, hk ] );
    · exact absurd ( h_v2_even_all n ) ( by norm_num [ * ] )

/-
For an infinite sequence, if $v_2(a_1) = 2k+1$ for some integer $k \ge 0$, it is necessary that $v_3(a_1) \ge k+1$.
-/
lemma lem_v3_condition_for_v2_odd (a : ℕ → ℕ) (h_pos : ∀ n, 0 < a n)
  (h_succ : ∀ n, a (n + 1) = s (a n)) (h_inf : ∀ n, 3 ≤ (a n).properDivisors.card) (k : ℕ)
  (h_v2 : padicValNat 2 (a 0) = 2 * k + 1) : k + 1 ≤ padicValNat 3 (a 0) := by
    -- By Lemma~\ref{lem:all_terms_must_be_div_by_6_not_5}, all terms in the sequence are divisible by 6.
    have h_div_6 : ∀ n, 6 ∣ a n := by
      -- Apply the lemma that states if a sequence contains a term not divisible by 6, it must terminate.
      intros n
      apply lem_non_div_6_terminates a h_pos h_succ h_inf n;
    -- If $v_2(a_1) = 2k+1$, then by Lemma~\ref{lem:exponent_evolution}, $v_3(a_{k+1}) = v_3(a_1) - k$.
    have h_v3_k1 : padicValNat 3 (a (k)) = padicValNat 3 (a 0) - k := by
      have h_evolution : ∀ n ≤ k, padicValNat 2 (a n) = 2 * k + 1 - 2 * n ∧ padicValNat 3 (a n) = padicValNat 3 (a 0) - n := by
        -- We proceed by induction on $n$.
        intro n hn
        induction' n with n ih;
        · aesop;
        · -- By Lemma~\ref{lem:exponent_evolution}, $a_{n+1} = \frac{13}{12}a_n$.
          have h_an1 : a (n + 1) = (13 * a n) / 12 := by
            have h_an1 : 12 * s (a n) = 13 * a n := by
              apply lem_s_N_val_div_by_6_v2_ge_2;
              · exact h_inf n;
              · exact h_div_6 n;
              · exact ih ( Nat.le_of_succ_le hn ) |>.1 ▸ Nat.le_sub_of_add_le ( by linarith );
            rw [ h_succ, ← h_an1, Nat.mul_div_cancel_left _ ( by decide ) ];
          -- Using the properties of $p$-adic valuations, we can simplify the expressions for $v_2(a_{n+1})$ and $v_3(a_{n+1})$.
          have h_valuations : padicValNat 2 (13 * a n / 12) = padicValNat 2 (13 * a n) - padicValNat 2 12 ∧ padicValNat 3 (13 * a n / 12) = padicValNat 3 (13 * a n) - padicValNat 3 12 := by
            constructor <;> rw [ padicValNat.div_of_dvd ];
            · have h_div_4 : 4 ∣ a n := by
                have h_div_4 : 2 ^ (2 * k + 1 - 2 * n) ∣ a n := by
                  exact ih ( Nat.le_of_succ_le hn ) |>.1 ▸ Nat.ordProj_dvd _ _;
                exact dvd_trans ( pow_dvd_pow _ ( show 2 ≤ 2 * k + 1 - 2 * n from le_tsub_of_add_le_left ( by linarith ) ) ) h_div_4;
              exact dvd_mul_of_dvd_right ( Nat.lcm_dvd h_div_4 ( h_div_6 n ) ) _;
            · have h_div_4 : 4 ∣ a n := by
                have h_div_4 : 2 ^ (2 * k + 1 - 2 * n) ∣ a n := by
                  exact ih ( Nat.le_of_succ_le hn ) |>.1 ▸ Nat.ordProj_dvd _ _;
                exact dvd_trans ( pow_dvd_pow _ ( show 2 ≤ 2 * k + 1 - 2 * n from le_tsub_of_add_le_left ( by linarith ) ) ) h_div_4;
              exact dvd_mul_of_dvd_right ( Nat.lcm_dvd h_div_4 ( h_div_6 n ) ) _;
          rw [ padicValNat.mul, padicValNat.mul ] at h_valuations <;> simp_all ( config := { decide := Bool.true } );
          · norm_num [ show padicValNat 2 12 = 2 by native_decide, show padicValNat 3 12 = 1 by native_decide, show padicValNat 2 13 = 0 by native_decide, show padicValNat 3 13 = 0 by native_decide ] at * ; omega;
          · linarith [ h_pos n ];
          · exact?;
      exact h_evolution k le_rfl |>.2;
    -- Since $a_k$ is divisible by 6, its 3-adic valuation must be at least 1.
    have h_v3_ak_ge_1 : 1 ≤ padicValNat 3 (a k) := by
      -- Since $a_k$ is divisible by 6, it is also divisible by 3.
      have h_div_3 : 3 ∣ a k := by
        exact dvd_trans ( by decide ) ( h_div_6 k );
      rw [ padicValNat ] ; aesop;
    omega

/-
For the sequence $(a_n)$ to be infinite, $a_1$ must satisfy: for some integer $a \ge 0$, $v_2(a_1)=2a+1$, $v_3(a_1) \ge a+1$, and $v_5(a_1)=0$.
-/
lemma lem_necessary_conditions_summary (a : ℕ → ℕ) (h_pos : ∀ n, 0 < a n)
  (h_succ : ∀ n, a (n + 1) = s (a n)) (h_inf : ∀ n, 3 ≤ (a n).properDivisors.card) :
  ∃ val_a, padicValNat 2 (a 0) = 2 * val_a + 1 ∧
    val_a + 1 ≤ padicValNat 3 (a 0) ∧ padicValNat 5 (a 0) = 0 := by
      have h_v2_odd : Odd ( padicValNat 2 ( a 0 ) ) := by
        exact?;
      have h_v3_ge_v2_div_2_plus_1 : (padicValNat 3 (a 0)) ≥ (padicValNat 2 (a 0) + 1) / 2 := by
        cases h_v2_odd ; aesop;
        convert lem_v3_condition_for_v2_odd a h_pos h_succ h_inf w h using 1;
        norm_num [ Nat.add_div ];
      have h_v5_zero : ¬(5 ∣ a 0) := by
        -- Suppose $5 \mid a_0$. Then $a_0$ is divisible by 6 and 5, so by 30.
        by_contra h_v5_div
        have h_div_30 : 30 ∣ a 0 := by
          have h_div_6 : 6 ∣ a 0 := by
            exact?;
          exact Nat.lcm_dvd h_v5_div h_div_6;
        -- Let $v_2(a_0) = 2k+1$ for some integer $k \ge 0$.
        obtain ⟨k, hk⟩ : ∃ k, padicValNat 2 (a 0) = 2 * k + 1 := by
          exact h_v2_odd;
        -- Then $a_1 = \frac{13}{12}a_0$ if $k \ge 1$, or $a_1 = \frac{31}{30}a_0$ if $k = 0$.
        have h_a1 : ∀ n ≤ k, a n = (13 / 12 : ℚ) ^ n * a 0 := by
          intro n hn;
          induction n <;> aesop;
          have h_a1_step : 12 * s (a n) = 13 * a n := by
            apply lem_s_N_val_div_by_6_v2_ge_2;
            · exact h_inf n;
            · exact?;
            · have := a_1 ( Nat.le_of_succ_le hn );
              rw [ show a n = ( 13 ^ n * a 0 ) / 12 ^ n from ?_ ];
              · rw [ padicValNat.div_of_dvd ];
                · rw [ padicValNat.mul ] <;> norm_num;
                  · rw [ show ( 12 ^ n : ℕ ) = 2 ^ ( 2 * n ) * 3 ^ n by rw [ pow_mul ] ; rw [ ← mul_pow ] ; norm_num, padicValNat.mul, padicValNat.pow, padicValNat.pow ] <;> norm_num;
                    rw [ show padicValNat 2 ( 3 ^ n ) = 0 by exact padicValNat.eq_zero_of_not_dvd <| by norm_num [ Nat.Prime.dvd_iff_one_le_factorization ] ] ; omega;
                  · linarith [ h_pos 0 ];
                · field_simp at this;
                  norm_cast at this; exact this ▸ dvd_mul_left _ _;
              · -- By multiplying both sides of the equation $(a n : ℚ) = (13 / 12) ^ n * (a 0 : ℚ)$ by $12^n$, we obtain $12^n * a n = 13^n * a 0$.
                have h_mul : 12^n * a n = 13^n * a 0 := by
                  rw [ ← @Nat.cast_inj ℚ ] ; push_cast ; rw [ this ] ; ring;
                  norm_num [ mul_assoc, div_pow ];
                rw [ ← h_mul, Nat.mul_div_cancel_left _ ( pow_pos ( by decide ) _ ) ];
          rw [ pow_succ' ] ; rw [ ← @Nat.cast_inj ℚ ] at *; push_cast at *; linarith [ a_1 <| Nat.le_of_succ_le hn ] ;
        -- Applying the lemma lem_s_N_val_div_by_6_v2_eq_1_yes_5 to aₖ, we get that s(aₖ) = (31/30)aₖ.
        have h_s_ak : s (a k) = (31 / 30 : ℚ) * a k := by
          have h_s_ak : padicValNat 2 (a k) = 1 ∧ 3 ∣ a k ∧ 5 ∣ a k := by
            bound;
            · have h_ak_div_30_not_4 : padicValNat 2 (a k) = padicValNat 2 (a 0) - 2 * k := by
                -- Using the properties of $p$-adic valuations, we can simplify the expression for $padicValNat 2 (a k)$.
                have h_padic_val : padicValNat 2 (a k) = padicValNat 2 ((13 ^ k * a 0) / 12 ^ k) := by
                  rw [ Nat.div_eq_of_eq_mul_left ];
                  · positivity;
                  · rw [ ← @Nat.cast_inj ℚ ] ; push_cast ; rw [ h_a1 k le_rfl ] ; ring;
                    field_simp;
                rw [ h_padic_val, padicValNat.div_of_dvd ];
                · rw [ padicValNat.mul ] <;> norm_num;
                  · rw [ show ( 12 ^ k : ℕ ) = 2 ^ ( 2 * k ) * 3 ^ k by rw [ pow_mul ] ; rw [ ← mul_pow ] ; norm_num, padicValNat.mul, padicValNat.pow, padicValNat.pow ] <;> norm_num;
                    rw [ show padicValNat 2 ( 3 ^ k ) = 0 by exact padicValNat.eq_zero_of_not_dvd <| by norm_num [ Nat.Prime.dvd_iff_one_le_factorization ] ] ; norm_num;
                    norm_num [ padicValNat.eq_zero_of_not_dvd ];
                  · linarith [ h_pos 0 ];
                · have h_div : 2 ^ (2 * k) ∣ a 0 := by
                    -- Since $padicValNat 2 (a₀) = 2*k + 1$, we have $2^{2*k} \mid a₀$ by definition of $padicValNat$.
                    have h_div : 2 ^ (padicValNat 2 (a 0)) ∣ a 0 := by
                      exact Nat.ordProj_dvd _ _;
                    exact dvd_trans ( pow_dvd_pow _ ( by linarith ) ) h_div;
                  -- Since $2^{2k}$ divides $a0$ and $13^k$ is odd, $2^{2k}$ divides $13^k * a0$. Also, since $3^k$ divides $a0$ (because $30$ divides $a0$), $3^k$ divides $13^k * a0$. Therefore, $12^k = 2^{2k} * 3^k$ divides $13^k * a0$.
                  have h_div_12k : 2 ^ (2 * k) ∣ 13 ^ k * a 0 ∧ 3 ^ k ∣ 13 ^ k * a 0 := by
                    exact ⟨ dvd_mul_of_dvd_right h_div _, dvd_mul_of_dvd_right ( dvd_trans ( pow_dvd_pow _ <| show k ≤ padicValNat 3 ( a 0 ) from by omega ) <| Nat.ordProj_dvd _ _ ) _ ⟩;
                  convert Nat.lcm_dvd h_div_12k.1 h_div_12k.2 using 1;
                  norm_num [ pow_mul, Nat.lcm ];
                  norm_num [ ← mul_pow, Nat.gcd_comm ];
                  norm_num [ Nat.gcd_comm, Nat.Coprime, Nat.Coprime.pow ];
              aesop;
            · specialize h_a1 k le_rfl;
              field_simp at h_a1;
              norm_cast at h_a1;
              replace h_a1 := congr_arg ( ·.factorization 3 ) h_a1 ; simp_all ( config := { decide := Bool.true } ) [ Nat.factorization_mul, ne_of_gt ( h_pos _ ) ];
              rw [ show ( 12 : ℕ ) = 2 ^ 2 * 3 by norm_num, Nat.factorization_mul, Nat.factorization_pow ] at h_a1 <;> norm_num at *;
              simp_all ( config := { decide := Bool.true } ) [ Nat.factorization ];
              exact Nat.dvd_of_mod_eq_zero ( Nat.mod_eq_zero_of_dvd <| by contrapose! h_a1; simp_all ( config := { decide := Bool.true } ) [ padicValNat.eq_zero_of_not_dvd ] ; omega );
            · specialize h_a1 k le_rfl;
              -- Since $a_0$ is divisible by 5, we can write $a_0 = 5m$ for some integer $m$.
              obtain ⟨m, hm⟩ : ∃ m, a 0 = 5 * m := h_v5_div;
              field_simp at h_a1;
              norm_cast at h_a1; replace h_a1 := congr_arg ( · % 5 ) h_a1; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hm ] at h_a1;
              rw [ Nat.dvd_iff_mod_eq_zero ] ; rw [ ← Nat.mod_add_div k 4 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt k four_pos; interval_cases k % 4 <;> simp_all ( config := { decide := Bool.true } ) ;
              · rw [ Nat.mul_mod ] at h_a1; have := Nat.mod_lt ( a ( 1 + 4 * ( k / 4 ) ) ) ( by decide : 5 > 0 ) ; interval_cases a ( 1 + 4 * ( k / 4 ) ) % 5 <;> trivial;
              · rw [ Nat.mul_mod ] at h_a1; have := Nat.mod_lt ( a ( 2 + 4 * ( k / 4 ) ) ) ( by decide : 5 > 0 ) ; interval_cases a ( 2 + 4 * ( k / 4 ) ) % 5 <;> trivial;
              · rw [ Nat.mul_mod ] at h_a1; have := Nat.mod_lt ( a ( 3 + 4 * ( k / 4 ) ) ) ( by decide : 5 > 0 ) ; interval_cases a ( 3 + 4 * ( k / 4 ) ) % 5 <;> trivial;
          have := lem_s_N_val_div_by_6_v2_eq_1_yes_5 ( a k ) ( h_inf k ) h_s_ak.1 h_s_ak.2.1 h_s_ak.2.2;
          rw [ div_mul_eq_mul_div, eq_div_iff ] <;> norm_cast ; linarith;
        -- This implies $v_2(a_{k+1}) = v_2(a_k) - 1 = 1 - 1 = 0$, so $a_{k+1}$ is not divisible by 2.
        have h_ak1_not_div_2 : ¬(2 ∣ a (k + 1)) := by
          have h_ak1_not_div_2 : padicValNat 2 (a (k + 1)) = 0 := by
            have h_ak1_not_div_2 : padicValNat 2 (a (k + 1)) = padicValNat 2 (31 * a k) - padicValNat 2 30 := by
              have h_ak1_not_div_2 : a (k + 1) * 30 = 31 * a k := by
                rw [ h_succ, ← @Nat.cast_inj ℚ ] ; push_cast ; linarith;
              rw [ ← h_ak1_not_div_2, padicValNat.mul ] <;> norm_num;
              linarith [ h_pos ( k + 1 ) ];
            rw [ h_ak1_not_div_2, padicValNat.mul ] <;> norm_num;
            · rw [ show padicValNat 2 ( a k ) = padicValNat 2 ( a 0 ) - 2 * k by
                have h_ak1_not_div_2 : ∀ n ≤ k, padicValNat 2 (a n) = padicValNat 2 (a 0) - 2 * n := by
                  intro n hn;
                  have := h_a1 n hn;
                  field_simp at this;
                  norm_cast at this;
                  have := congr_arg ( fun x => x.factorization 2 ) this ; norm_num [ Nat.factorization_mul, ne_of_gt ( h_pos _ ) ] at this;
                  exact eq_tsub_of_add_eq ( by erw [ show ( Nat.factorization 12 ) 2 = 2 by native_decide ] at this; norm_num [ ← Nat.factorization_def ] at *; linarith );
                exact h_ak1_not_div_2 k le_rfl ] ; simp +arith +decide [ hk ];
              native_decide;
            · linarith [ h_pos k ];
          -- If the 2-adic valuation of $a_{k+1}$ is zero, then $2$ does not divide $a_{k+1}$.
          simp [padicValNat] at h_ak1_not_div_2;
          exact?;
        -- This contradicts the assumption that the sequence is infinite, as $a_{k+1}$ would not be divisible by 6.
        have h_contradiction : ¬(6 ∣ a (k + 1)) := by
          exact fun h => h_ak1_not_div_2 ( dvd_trans ( by decide ) h );
        exact h_contradiction ( lem_non_div_6_terminates a h_pos h_succ h_inf ( k + 1 ) );
      cases h_v2_odd ; aesop;
      omega

/-
Let $\bigl(a_n\bigr)_{n\ge 1}$ be a sequence of positive integers such that each $a_n$ has at least three proper divisors, meaning $\tau(a_n) \ge 4$. For each $n\ge 1$, let $a_{n+1}$ be the sum of the three largest proper divisors of $a_n$. Such a sequence can be continued indefinitely if and only if $a_1$ is an integer of the form
\[
a_1\;=\;6\cdot12^{\,a}\,m
\]
for some integer $a \ge 0$ and a positive integer $m$ with $\gcd(m,10)=1$.
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
    } = { n | ∃ a m, Nat.Coprime m 10 ∧ n = 6 * 12 ^ a * m } := by
      -- To prove equality of sets, we show each set is a subset of the other.
      apply Set.eq_of_subset_of_subset;
      · intro a₁ ha₁;
        -- Let's obtain the sequence $a$ and its properties from $ha₁$.
        obtain ⟨a, ha_pos, ha_card, ha_succ, rfl⟩ := ha₁;
        -- By Lemma~\ref{lem:necessary_conditions_summary}, $a_1$ must satisfy: for some integer $a \ge 0$, $v_2(a_1)=2a+1$, $v_3(a_1) \ge a+1$, and $v_5(a_1)=0$.
        obtain ⟨val_a, h2, h3, h5⟩ : ∃ val_a, padicValNat 2 (a 0) = 2 * val_a + 1 ∧ val_a + 1 ≤ padicValNat 3 (a 0) ∧ padicValNat 5 (a 0) = 0 := by
          apply lem_necessary_conditions_summary;
          · assumption;
          · unfold s; aesop;
          · assumption;
        have := lem_conditions_imply_form ( a 0 ) val_a ( ha_pos 0 ) h2 h3 h5;
        aesop;
      · -- By Lemma~\ref{lem:sufficiency_stabilization}, if $a_1$ is of the form $6 \cdot 12^a \cdot m$ with $m$ coprime to 10, then there exists a sequence $a_seq$ such that $a_seq 0 = a_1$ and each term is the sum of the three largest proper divisors of the previous term.
        intro n hn
        obtain ⟨a, m, hm_coprime, rfl⟩ := hn
        obtain ⟨a_seq, ha_seq⟩ := lem_sufficiency_stabilization a m (by
        exact Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hm_coprime )) hm_coprime;
        unfold s at *; aesop;

#print axioms main_theorem
