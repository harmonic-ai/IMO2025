/-
Let $\mathbb{N}$ denote the set of positive integers.
A function $f\colon\mathbb{N} \to \mathbb{N}$ is said to be \emph{bonza} if
$$ f(a) \ \ \text{divides} \ \ b^a - f(b)^{f(a)} $$
for all positive integers $a$ and $b$.
Determine the smallest real constant $c$ such that
$f(n)\leqslant cn$ for all bonza functions $f$ and all positive integers $n$.
Answer: 4
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

namespace IMO2025P3

/-
A function $f\colon\mathbb{N} \to \mathbb{N}$ is said to be \emph{bonza} if
$$f(a) \text{ divides } b^a - f(b)^{f(a)}$$
for all positive integers $a$ and $b$.
-/
def isBonza (f : ℕ+ → ℕ+) : Prop :=
  ∀ a b : ℕ+, (b : ℕ) ^ (a : ℕ) ≡ (f b : ℕ) ^ (f a : ℕ) [MOD f a]

/-
For a bonza function $f$, let $S$ be the set of prime numbers $p$ for which $f(p) > 1$.
-/
def S (f : ℕ+ → ℕ+) : Set ℕ+ :=
  {p | Nat.Prime (p : ℕ) ∧ f p > 1}

/-
The function $f: \mathbb{N} \to \mathbb{N}$ defined by
$$f(n) = \begin{cases}
1 & \text{if } n \text{ is odd} \\
4 & \text{if } n \equiv 2 \pmod{4} \\
16 & \text{if } n \equiv 0 \pmod{4}
\end{cases}$$
is a bonza function.
-/
def f_construction : ℕ+ → ℕ+ := fun n ↦
  if Odd (n : ℕ) then
    1
  else if (n : ℕ) % 4 = 2 then
    4
  else
    16

/-
If $f$ is a bonza function, then $f(n) \mid n^n$ for all $n \in \mathbb{N}$.
-/
lemma f_n_divides_n_n (f : ℕ+ → ℕ+) (h : isBonza f) (n : ℕ+) : (f n : ℕ) ∣ (n : ℕ) ^ (n : ℕ) := by
  have := h n n;
  exact Nat.dvd_of_mod_eq_zero ( this.symm ▸ Nat.modEq_zero_iff_dvd.mpr ( dvd_pow_self _ ( PNat.ne_zero _ ) ) )

/-
If $f$ is a bonza function and $p$ is a prime number, then $f(p)$ must be a power of $p$.
-/
lemma prime_power_form (f : ℕ+ → ℕ+) (h : isBonza f) (p : ℕ+) (hp : Nat.Prime (p : ℕ)) :
  ∃ k : ℕ, (f p : ℕ) = (p : ℕ) ^ k := by
  have := h p p;
  -- From Lemma 2, we know that f(p) divides p^p.
  have h_div : (f p : ℕ) ∣ (p : ℕ) ^ (p : ℕ) := by
    exact Nat.dvd_of_mod_eq_zero ( this.symm ▸ Nat.modEq_zero_iff_dvd.mpr ( dvd_pow_self _ ( PNat.ne_zero _ ) ) );
  rw [ Nat.dvd_prime_pow ] at h_div <;> aesop

lemma construction_bonza : isBonza f_construction := by
  -- By definition of $f_construction$, we know that for any $a$, $f(a)$ is either $1$, $4$, or $16$.
  have h_cases : ∀ a : ℕ+, f_construction a = 1 ∨ f_construction a = 4 ∨ f_construction a = 16 := by
    aesop;
    unfold f_construction;
    split_ifs <;> simp ( config := { decide := Bool.true } );
  -- Now consider the three cases for $f(a)$ and show that $f(a) \mid b^a - f(b)^{f(a)}$ for all $a$ and $b$.
  intros a b
  rcases h_cases a with ha | ha | ha;
  · -- Since $f_construction a = 1$, the congruence $b^a \equiv f_construction b \pmod{1}$ holds trivially because any integer is congruent to any other integer modulo 1.
    simp [ha, Nat.ModEq];
    rw [ Nat.mod_one, Nat.mod_one ];
  · rcases h_cases b with ( hb | hb | hb ) <;> simp_all ( config := { decide := Bool.true } );
    · unfold f_construction at * ; aesop;
      · rw [ Nat.odd_iff ] at hb; omega;
      · -- Since $b$ is odd, we can write $b = 2k + 1$ for some integer $k$.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, b = 2 * k + 1 := hb;
        norm_num [ Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hk ];
        rw [ ← Nat.mod_add_div a 4, h_2 ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ; have := Nat.mod_lt k zero_lt_four ; interval_cases k % 4 <;> norm_num;
    · rcases Nat.even_or_odd' ( b : ℕ ) with ⟨ c, d | d ⟩ <;> norm_num [ Nat.ModEq, Nat.pow_mod, Nat.mul_mod, d ];
      · rcases a with ( _ | _ | a ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;
        · contradiction;
        · cases ha;
        · have := Nat.mod_lt c zero_lt_four; interval_cases c % 4 <;> norm_num [ Nat.pow_mod ] ;
      · unfold f_construction at hb; aesop;
    · -- Since $f(b) = 16$, we know that $b$ is divisible by $4$. Therefore, $b^{a}$ is divisible by $4^2 = 16$, making $b^{a} \equiv 0 \pmod{4}$.
      have hb_div : 4 ∣ (b : ℕ) := by
        unfold f_construction at hb; aesop;
        exact Nat.dvd_of_mod_eq_zero ( by rw [ Nat.even_iff ] at h; omega );
      norm_num [ Nat.ModEq, Nat.pow_mod, Nat.mod_eq_zero_of_dvd hb_div ];
  · -- Since $a$ is a multiple of 4, we can write $a = 4k$ for some $k \in \mathbb{N}$.
    obtain ⟨k, rfl⟩ : ∃ k : ℕ+, a = 4 * k := by
      -- Since $a$ is even and $f_construction a = 16$, it follows that $a$ must be a multiple of 4.
      have ha_mod : (a : ℕ) % 4 = 0 := by
        unfold f_construction at ha ; aesop;
        rw [ Nat.even_iff ] at h; omega;
      exact PNat.dvd_iff.mpr ( Nat.dvd_of_mod_eq_zero ha_mod );
    cases h_cases b <;> aesop;
    · -- Since $b$ is odd, we can write $b = 2m + 1$ for some $m \in \mathbb{N}$.
      obtain ⟨m, hm⟩ : ∃ m : ℕ, b = 2 * m + 1 := by
        unfold f_construction at h; aesop;
      norm_num [ Nat.ModEq, Nat.pow_mul, Nat.pow_mod, hm ];
      norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] ; have := Nat.mod_lt m ( by decide : 0 < 16 ) ; interval_cases m % 16 <;> norm_num;
    · unfold f_construction at * ; aesop;
      norm_num [ Nat.ModEq, Nat.pow_mul, Nat.pow_mod, h_2 ];
      rw [ ← Nat.mod_mod_of_dvd _ ( by decide : 4 ∣ 16 ) ] at h_2; have := Nat.mod_lt ( b : ℕ ) ( by decide : 0 < 16 ) ; interval_cases ( b : ℕ ) % 16 <;> norm_num at h_2 ⊢;
    · -- Since $b$ is a multiple of 4, we can write $b = 4m$ for some $m \in \mathbb{N}$.
      obtain ⟨m, rfl⟩ : ∃ m : ℕ+, b = 4 * m := by
        unfold f_construction at h_2;
        aesop;
        exact PNat.dvd_iff.mpr ( show 4 ∣ ( b : ℕ ) from Nat.dvd_of_mod_eq_zero ( by obtain ⟨ m, hm ⟩ := h; omega ) );
      norm_num [ Nat.ModEq, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ];
      have := Nat.mod_lt ( m : ℕ ) ( by decide : 0 < 16 ) ; interval_cases ( m : ℕ ) % 16 <;> norm_num [ Nat.pow_mod ] ;

/-
If $f$ is a bonza function for which $S=\{2\}$, then for any odd integer $n>1$, $f(n)=1$.
-/
lemma odd_n_gives_f_n_one (f : ℕ+ → ℕ+) (h : isBonza f) (hS : S f = {(2 : ℕ+)}) (n : ℕ+)
    (hn_odd : Odd (n : ℕ)) (hn_gt_one : n > 1) :
  f n = 1 := by
  -- Since $n$ is odd and greater than 1, all its prime factors are odd primes. For any odd prime $p$, we have $f(p) = 1$ because $S(f) = \{2\}$.
  have h_prime_factors : ∀ p : ℕ+, Nat.Prime p → p ∣ n → f p = 1 := by
    rw [ Set.eq_singleton_iff_unique_mem ] at hS;
    -- Since $p$ is a prime divisor of $n$ and $n$ is odd, $p$ cannot be $2$. Therefore, $p$ is not in $S(f)$, which implies $f(p) \leq 1$.
    intros p hp_prime hp_div
    have hp_not_in_S : p ∉ S f := by
      intros H; specialize hS; have := hS.2 p H; simp_all ( config := { decide := Bool.true } ) [ PNat.dvd_iff, Nat.prime_dvd_prime_iff_eq ] ;
      -- Since $n$ is odd, $2$ cannot divide $n$, leading to a contradiction.
      exact absurd hp_div (by simpa [ ← even_iff_two_dvd ] using hn_odd);
    unfold S at *; aesop;
  -- Since $f(n)$ divides $p^n - 1$ for any prime factor $p$ of $n$, and $p$ divides $n$, it follows that $f(n)$ is coprime with $p$.
  have h_coprime : ∀ p : ℕ+, Nat.Prime p → p ∣ n → Nat.gcd (f n) p = 1 := by
    intros p hp_prime hp_div
    have h_div : (f n : ℕ) ∣ (p : ℕ) ^ (n : ℕ) - 1 := by
      have := h n p;
      rw [ ← Nat.modEq_zero_iff_dvd ] ; have := this.symm.dvd; simp_all ( config := { decide := Bool.true } ) [ ← ZMod.eq_iff_modEq_nat ] ;
    refine' Nat.Coprime.coprime_dvd_left h_div _;
    refine' Nat.Coprime.symm ( hp_prime.coprime_iff_not_dvd.mpr _ );
    haveI := Fact.mk hp_prime; simp_all ( config := { decide := Bool.true } ) [ ← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_sub ( Nat.one_le_pow _ _ hp_prime.pos ) ] ;
  -- Since $f(n)$ is coprime with all prime factors of $n$, it must be coprime with $n$ itself.
  have h_coprime_n : Nat.gcd (f n) n = 1 := by
    refine' Nat.Coprime.symm <| Nat.coprime_of_dvd <| _;
    exact fun k hk hk' hk'' => hk.not_dvd_one <| h_coprime ⟨ k, hk.pos ⟩ hk ( PNat.dvd_iff.mpr hk' ) ▸ Nat.dvd_gcd hk'' ( dvd_refl _ );
  -- Since $f(n)$ divides $n^n$ and $f(n)$ is coprime with $n$, it follows that $f(n)$ must divide $1$.
  have h_div_one : (f n : ℕ) ∣ (n : ℕ) ^ (n : ℕ) ∧ Nat.gcd (f n) n = 1 → (f n : ℕ) ∣ 1 := by
    exact fun h => by have := Nat.dvd_gcd ( dvd_refl _ ) h.1; simp_all ( config := { decide := Bool.true } ) [ Nat.Coprime, Nat.Coprime.pow_right ] ;
  exact PNat.eq ( Nat.eq_one_of_dvd_one <| h_div_one ⟨ f_n_divides_n_n f h n, h_coprime_n ⟩ )

/-
If $f$ is a bonza function and $p \in S$ (per Definition~\ref{def:S}), then $f(b) \equiv b \pmod{p}$ for all $b \in \mathbb{N}$.
-/
lemma fermat_congruence (f : ℕ+ → ℕ+) (h : isBonza f) (p : ℕ+) (hp : p ∈ S f) (b : ℕ+) :
  (f b : ℕ) ≡ (b : ℕ) [MOD p] := by
  -- Since $p$ is a prime and $f(p) > 1$, we know that $f(p)$ is a power of $p$. Let $f(p) = p^k$ for some $k \geq 1$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (f p : ℕ) = (p : ℕ) ^ k := by
    -- Apply the lemma that states $f(p)$ must be a power of $p$ for a bonza function $f$ and a prime $p$.
    apply prime_power_form f h p hp.left;
  -- Applying the definition of $P(a,b)$ with $a=p$, we get $b^p \equiv f(b)^{f(p)} \pmod{p}$.
  have hb_mod_p : (b : ℕ) ^ (p : ℕ) ≡ (f b : ℕ) ^ (f p : ℕ) [MOD p] := by
    have hb_mod_p : (b : ℕ) ^ (p : ℕ) ≡ (f b : ℕ) ^ (f p : ℕ) [MOD f p] := by
      exact?;
    -- Since $p$ divides $f(p)$, the congruence modulo $f(p)$ implies the congruence modulo $p$.
    have h_div : (p : ℕ) ∣ (f p : ℕ) := by
      rcases k with ( _ | k ) <;> simp_all ( config := { decide := Bool.true } ) [ pow_succ' ];
      have := hp.2; aesop;
    exact hb_mod_p.of_dvd h_div;
  haveI := Fact.mk hp.left; simp_all ( config := { decide := Bool.true } ) [ ← ZMod.eq_iff_modEq_nat ] ;

/-
If $f$ is a bonza function for which $S=\{2\}$, and $n$ is an even integer, then $f(n)$ is a power of 2.
-/
lemma even_n_power_of_two (f : ℕ+ → ℕ+) (h : isBonza f) (hS : S f = {(2 : ℕ+)}) (n : ℕ+)
    (hn_even : Even (n : ℕ)) :
  ∃ k : ℕ, (f n : ℕ) = 2 ^ k := by
  have h_prime_factors : ∀ p : ℕ+, Nat.Prime p → p ≠ 2 → ¬ (p ∣ f n) := by
    -- If $p$ divides $f(n)$, then by the definition of $S(f)$, $p$ must be in $S(f)$.
    have h_prime_in_S : ∀ p : ℕ+, Nat.Prime p → p ∣ f n → p ∈ S f := by
      -- If $p$ divides $f(n)$, then by the definition of $S(f)$, $p$ must be in $S(f)$ because $f(p)$ must be greater than 1.
      intros p hp hpn
      have h_fp_gt_one : f p > 1 := by
        have := h n p;
        replace := this.of_dvd ( PNat.dvd_iff.mp hpn );
        rw [ Nat.ModEq, Nat.pow_mod ] at this; rcases p with ( _ | _ | p ) <;> rcases n with ( _ | _ | n ) <;> norm_num at *;
        · contradiction;
        · exact lt_of_le_of_ne ( PNat.one_le _ ) ( Ne.symm <| by intro t; simp ( config := { decide := Bool.true } ) [ t ] at this );
      -- Since $p$ is a prime and $f(p) > 1$, we can conclude that $p \in S(f)$ by definition.
      exact ⟨hp, h_fp_gt_one⟩;
    exact fun p pp p2 hpn => p2 <| hS.subset ( h_prime_in_S p pp hpn );
  -- Since $f(n)$ has no prime factors other than 2, it must be a power of 2.
  have h_prime_factors_two : ∀ p : ℕ, Nat.Prime p → p ∣ (f n : ℕ) → p = 2 := by
    exact fun p pp dp => Classical.not_not.1 fun hp => h_prime_factors ⟨ p, pp.pos ⟩ pp ( ne_of_apply_ne PNat.val hp ) ( PNat.dvd_iff.2 dp );
  rw [ ← Nat.prod_primeFactorsList ( PNat.ne_zero ( f n ) ) ];
  rw [ List.prod_eq_pow_single 2 ] <;> aesop;
  exact?

/-
For a bonza function $f$, any prime $q \notin S$ must satisfy $q \equiv 1 \pmod{p}$ for all $p \in S$.
-/
lemma S_definition (f : ℕ+ → ℕ+) (h : isBonza f) (q : ℕ+) (hq_prime : Nat.Prime (q : ℕ))
    (hq_not_in_S : q ∉ S f) (p : ℕ+) (hp_in_S : p ∈ S f) :
  (q : ℕ) ≡ 1 [MOD p] := by
  -- Let's substitute $b = q$ into Lemma fermat_congruence.
  have h_subst : (f q : ℕ) ≡ q [MOD p] := by
    exact?;
  -- From Lemma odd_n_gives_f_n_one, we know that $f(q) = 1$.
  have h_fq_one : f q = 1 := by
    unfold S at *; aesop;
  exact h_subst.symm.trans ( by simp? ( config := { decide := Bool.true } ) [ h_fq_one ] )

/-
If $f$ is a bonza function and the set $S$ is finite and non-empty, then $S=\{2\}$.
-/
lemma finite_S_constraint (f : ℕ+ → ℕ+) (h : isBonza f) (hS_fin : (S f).Finite)
    (hS_nonempty : (S f).Nonempty) :
  S f = {(2 : ℕ+)} := by
  -- Suppose $S$ is non-empty and finite. If $S \neq \{2\}$, it must contain an odd prime, and therefore also 2.
  by_cases h_odd_prime : ∃ p ∈ S f, p ≠ 2;
  · -- Let $M = \prod_{p \in S} p$. Any prime $q \notin S$ must satisfy $q \equiv 1 \pmod M$.
    obtain ⟨p, hp_in_S, hp_odd⟩ : ∃ p ∈ S f, p ≠ 2 := h_odd_prime
    have hM : ∀ q : ℕ+, Nat.Prime (q : ℕ) → q ∉ S f → (q : ℕ) ≡ 1 [MOD ∏ p in hS_fin.toFinset, (p : ℕ)] := by
      intros q hq_prime hq_not_in_S
      have hq_cong : ∀ p ∈ S f, (q : ℕ) ≡ 1 [MOD p] := by
        exact?;
      simp_all ( config := { decide := Bool.true } ) [ Nat.modEq_iff_dvd ];
      convert Finset.prod_dvd_of_coprime _ _ <;> aesop;
      intros p hp q hq hpq; specialize hq_cong p hp; specialize hq_cong ; aesop;
      refine' Int.gcd_eq_one_iff_coprime.mp _;
      have := Nat.coprime_primes ( show Nat.Prime ( p : ℕ ) from by cases hp; aesop ) ( show Nat.Prime ( q : ℕ ) from by cases hq; aesop ) ; aesop;
    -- Let $M = \prod_{p \in S} p$. If $M > 2$, then $M-1 > 1$ and must have a prime divisor $q$.
    set M := ∏ p in hS_fin.toFinset, (p : ℕ)
    have hM_gt_two : M > 2 → False := by
      intro hM_gt_two
      obtain ⟨q, hq_prime, hq_div⟩ : ∃ q : ℕ+, Nat.Prime (q : ℕ) ∧ (q : ℕ) ∣ (M - 1) := by
        exact ⟨ ⟨ Nat.minFac ( M - 1 ), Nat.minFac_pos _ ⟩, Nat.minFac_prime ( Nat.ne_of_gt <| lt_tsub_iff_left.mpr <| by linarith ), Nat.minFac_dvd _ ⟩;
      -- Since $q \mid M - 1$, we have $q \equiv 1 \pmod M$.
      have hq_mod : (q : ℕ) ≡ 1 [MOD M] := by
        apply hM q hq_prime;
        intro hq_in_S;
        have := Nat.dvd_sub' ( show ( q : ℕ ) ∣ M from Finset.dvd_prod_of_mem _ <| hS_fin.mem_toFinset.mpr hq_in_S ) hq_div;
        rw [ Nat.sub_sub_self ( by linarith ) ] at this ; aesop;
      have := Nat.modEq_iff_dvd.mp hq_mod.symm;
      exact absurd ( Int.le_of_dvd ( by simpa using hq_prime.one_lt ) this ) ( by norm_num; linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ M ), Nat.le_of_dvd ( Nat.sub_pos_of_lt ( by linarith : 1 < M ) ) hq_div ] );
    contrapose! hM_gt_two; aesop;
    -- Since $p \in S$ and $p \neq 2$, we have $p \geq 3$.
    have hp_ge_three : 3 ≤ (p : ℕ) := by
      exact lt_of_le_of_ne ( Nat.succ_le_of_lt ( show ( p : ℕ ) > 1 from Nat.Prime.one_lt hp_in_S.1 ) ) ( Ne.symm <| by simpa only [ Ne, ← PNat.coe_inj ] using hp_odd );
    exact lt_of_lt_of_le hp_ge_three <| Nat.le_of_dvd ( Finset.prod_pos fun x hx => Nat.cast_pos.mpr <| PNat.pos x ) <| Finset.dvd_prod_of_mem _ <| hS_fin.mem_toFinset.mpr hp_in_S;
  · exact Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨ hS_nonempty, fun p hp => Classical.not_not.1 fun hp' => h_odd_prime ⟨ p, hp, hp' ⟩ ⟩

/-
If $f$ is a bonza function for which $S=\{2\}$, and $n=2^k m$ with $m$ odd and $k \ge 1$, then $v_2(f(n)) \le k+2$, where $v_2(x)$ denotes the exponent of the highest power of 2 dividing $x$.
-/
lemma v2_bound_formula (f : ℕ+ → ℕ+) (h : isBonza f) (hS : S f = {(2 : ℕ+)}) (n : ℕ+)
    (k m : ℕ) (hk : k ≥ 1) (hm_odd : Odd m) (hn_def : (n : ℕ) = 2 ^ k * m) :
  padicValNat 2 (f n : ℕ) ≤ k + 2 := by
  -- By Lemma~\ref{lem:even_n_power_of_two}, $f(n)$ must be a power of 2. Let's write $f(n)=2^\ell$.
  have h_fn_power_of_two : ∃ ℓ : ℕ, (f n : ℕ) = 2 ^ ℓ := by
    -- By Lemma~\ref{lem:even_n_power_of_two}, $f(n)$ must be a power of 2. Let's write $f(n)=2^{\ell}$.
    have := even_n_power_of_two f h hS n (show Even (n : ℕ) from by
      exact hn_def ▸ even_iff_two_dvd.mpr ( dvd_mul_of_dvd_left ( pow_dvd_pow _ hk ) _ ));
    aesop;
  -- However, we can also apply the divisibility condition with $n$ and any odd prime $p$. For an odd prime $p$, $P(n,p)$ implies $f(n) \mid p^n - 1$.
  have h_divides_odd_prime : ∀ p : ℕ+, Nat.Prime (p : ℕ) → p ≠ 2 → (f n : ℕ) ∣ (p : ℕ) ^ (n : ℕ) - 1 := by
    intros p hp_prime hp_ne_two
    have h_divides_p : (f n : ℕ) ∣ (p : ℕ) ^ (n : ℕ) - (f p : ℕ) ^ (f n : ℕ) := by
      have := h n p;
      rw [ ← Nat.modEq_zero_iff_dvd ];
      cases le_total ( ( p : ℕ ) ^ ( n : ℕ ) ) ( ( f p : ℕ ) ^ ( f n : ℕ ) ) <;> simp_all ( config := { decide := Bool.true } ) [ ← ZMod.eq_iff_modEq_nat ];
    -- Since $p$ is an odd prime, we have $f(p) = 1$ by definition of $S$.
    have h_fp_one : f p = 1 := by
      simp_all ( config := { decide := Bool.true } ) [ Set.eq_singleton_iff_unique_mem ];
      exact le_antisymm ( not_lt.mp fun contra => hp_ne_two <| hS.2 p ⟨ hp_prime, contra ⟩ ) bot_le;
    aesop;
  -- Applying this with $p=3$, we have $f(n) \mid 3^n - 1 = 3^{2^km} - 1$.
  have h_divides_three : (f n : ℕ) ∣ 3 ^ (2 ^ k * m) - 1 := by
    simpa [ hn_def ] using h_divides_odd_prime 3 Nat.prime_three ( by decide );
  -- Using the lemma on the 2-adic valuation of $3^{2^t}-1$, we have $v_2(3^{2^k m}-1) = v_2(3^{2^k}-1) + v_2(m)$.
  have h_val_three : (padicValNat 2 (3 ^ (2 ^ k * m) - 1)) = (padicValNat 2 (3 ^ (2 ^ k) - 1)) + (padicValNat 2 m) := by
    -- Applying the lemma on the 2-adic valuation of $3^{2^t}-1$, we can simplify the expression.
    have h_val_simplified : padicValNat 2 (3 ^ (2 ^ k * m) - 1) = padicValNat 2 ((3 ^ (2 ^ k) - 1) * (∑ i in Finset.range m, (3 ^ (2 ^ k)) ^ i)) := by
      zify;
      norm_num [ mul_geom_sum, pow_mul ];
    rw [ h_val_simplified, padicValNat.mul ] <;> norm_num;
    · rw [ padicValNat.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd ] <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, Finset.sum_nat_mod ];
      · exact Nat.odd_iff.mp hm_odd;
      · exact Nat.odd_iff.mp hm_odd;
    · exact ne_of_gt ( Nat.sub_pos_of_lt ( one_lt_pow₀ ( by decide ) ( by positivity ) ) );
    · exact ⟨ 0, hm_odd.pos ⟩;
  -- Using the lemma on the 2-adic valuation of $3^{2^t}-1$, we have $v_2(3^{2^k}-1) = k+2$.
  have h_val_three_k : (padicValNat 2 (3 ^ (2 ^ k) - 1)) = k + 2 := by
    refine' Nat.le_induction _ _ k hk;
    · native_decide;
    · intro n hn ih; rw [ show ( 3 : ℕ ) ^ 2 ^ ( n + 1 ) - 1 = ( 3 ^ 2 ^ n - 1 ) * ( 3 ^ 2 ^ n + 1 ) by convert Nat.sq_sub_sq ( 3 ^ 2 ^ n ) 1 using 1 <;> ring ] ; rw [ padicValNat.mul ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ ( by decide ) ( by positivity ) ) ) ( by positivity ) ] ; simp +arith +decide [ ih ] ;
      rw [ padicValNat ];
      norm_num [ Nat.find_eq_iff ];
      exact ⟨ by rw [ Nat.dvd_iff_mod_eq_zero ] ; rcases n with ( _ | _ | n ) <;> norm_num [ Nat.add_mod, Nat.pow_succ', Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *, by rw [ ← even_iff_two_dvd ] ; simp ( config := { decide := Bool.true } ) [ parity_simps ] ⟩;
  have := Nat.factorization_le_iff_dvd ( by aesop ) ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ ( by decide : 1 < 3 ) ( by aesop ) ) ) |>.2 h_divides_three ; aesop;
  simp_all ( config := { decide := Bool.true } ) [ Nat.factorization ];
  replace := this 2 ; simp_all ( config := { decide := Bool.true } );
  erw [ padicValNat.eq_zero_of_not_dvd ( by simpa [ ← even_iff_two_dvd, Nat.one_le_iff_ne_zero, parity_simps ] using hm_odd ) ] at this ; linarith

/-
If $f$ is a bonza function, then $f(n) \le 4n$ for all $n \in \mathbb{N}$.
-/
lemma upper_bound_four (f : ℕ+ → ℕ+) (h : isBonza f) (n : ℕ+) :
  (f n : ℕ) ≤ 4 * (n : ℕ) := by
  -- Consider two cases: $S$ is finite or infinite.
  by_cases hS_finite : (S f).Finite;
  · -- If $S$ is non-empty and finite, then $S=\{2\}$.
    by_cases hS_nonempty : (S f).Nonempty;
    · -- Since $S = \{2\}$, we can use the results from the lemmas. For any $n$, if $n$ is odd, then $f(n) = 1$, which is trivially $\leq 4n$. If $n$ is even, then $f(n)$ is a power of 2.
      have h_even : ∀ n : ℕ+, Even (n : ℕ) → (f n : ℕ) ≤ 4 * (n : ℕ) := by
        -- Since $S = \{2\}$, we can use the results from the lemmas. For any $n$, if $n$ is even, then $f(n)$ is a power of 2.
        intros n hn_even
        obtain ⟨k, hk⟩ : ∃ k : ℕ, (f n : ℕ) = 2 ^ k := by
          have := even_n_power_of_two f h ( by
            apply finite_S_constraint;
            · assumption;
            · assumption;
            · assumption ) n hn_even;
          exact this;
        -- Since $n$ is even, we can write $n = 2^m \cdot l$ where $l$ is odd and $m \geq 1$.
        obtain ⟨m, l, hm, hl⟩ : ∃ m l : ℕ, m ≥ 1 ∧ Odd l ∧ (n : ℕ) = 2 ^ m * l := by
          use Nat.factorization n 2, n / 2 ^ Nat.factorization n 2;
          -- Since $n$ is even, its factorization must include at least one 2, so $m \geq 1$.
          have hm_ge_one : 1 ≤ Nat.factorization n 2 := by
            exact Nat.pos_of_ne_zero fun h => by simp_all ( config := { decide := Bool.true } ) [ even_iff_two_dvd, Nat.factorization_eq_zero_iff ] ;
          exact ⟨ hm_ge_one, by rw [ Nat.odd_iff ] ; exact Nat.mod_two_ne_zero.mp fun contra => absurd ( Nat.dvd_of_mod_eq_zero contra ) ( Nat.not_dvd_ord_compl ( by norm_num ) <| by aesop ), Eq.symm <| Nat.mul_div_cancel' <| Nat.ord_proj_dvd _ _ ⟩;
        -- By Lemma~\ref{lem:v2_bound_formula}, we have $v_2(f(n)) \le m + 2$.
        have h_v2_bound : k ≤ m + 2 := by
          have h_v2_bound : padicValNat 2 (f n : ℕ) ≤ m + 2 := by
            -- Applying Lemma~\ref{lem:v2_bound_formula} with $n = 2^m \cdot l$, we get $v_2(f(n)) \le m + 2$.
            apply v2_bound_formula;
            any_goals tauto;
            exact?;
          simp_all ( config := { decide := Bool.true } ) [ padicValNat.pow ];
        aesop;
        exact le_trans ( pow_le_pow_right₀ ( by decide ) h_v2_bound ) ( by ring_nf; norm_num; nlinarith [ pow_pos ( by decide : 0 < ( 2 : ℕ ) ) m, left.pos ] );
      -- For any odd integer $n$, if $n > 1$, then $f(n) = 1$ by the lemma odd_n_gives_f_n_one. If $n = 1$, then $f(1) = 1$ by the lemma f_one_equals_one.
      have h_odd : ∀ n : ℕ+, Odd (n : ℕ) → (f n : ℕ) ≤ 4 * (n : ℕ) := by
        intros n hn_odd
        by_cases hn_gt_one : n > 1;
        · have := odd_n_gives_f_n_one f h ( show S f = { ( 2 : ℕ+ ) } from ?_ ) n hn_odd hn_gt_one;
          · aesop;
            linarith [ PNat.pos n ];
          · exact?;
        · have := h 1 1 ; simp_all ( config := { decide := Bool.true } ) [ Nat.ModEq, Nat.pow_mod ];
      exact if hn : Even ( n : ℕ ) then h_even n hn else h_odd n ( by simpa using hn );
    · -- If $S$ is empty, then $f(p)=1$ for all prime numbers $p$. The condition $P(n,p)$ implies $f(n) \mid p^n - f(p)^{f(n)} = p^n - 1$. Since this holds for all primes $p$, we must have $f(n)=1$.
      have h_empty_S : ∀ p : ℕ+, Nat.Prime (p : ℕ) → f p = 1 := by
        aesop;
        exact le_antisymm ( not_lt.mp fun contra => hS_nonempty ⟨ p, a, contra ⟩ ) bot_le;
      -- The condition $P(n,p)$ implies $f(n) \mid p^n - f(p)^{f(n)} = p^n - 1$. Since this holds for all primes $p$, we must have $f(n)=1$.
      have h_divides_one : ∀ p : ℕ+, Nat.Prime (p : ℕ) → (f n : ℕ) ∣ (p : ℕ) ^ (n : ℕ) - 1 := by
        intro p hp; specialize h n p; aesop;
        simpa [ ← Int.natCast_dvd_natCast, Nat.cast_sub ( Nat.one_le_pow _ _ hp.pos ) ] using h.symm.dvd;
      -- Since this holds for all primes $p$, we must have $f(n)=1$.
      have h_fn_one : f n = 1 := by
        -- Assume for contradiction that $f(n) > 1$. Then there exists a prime $q$ such that $q \mid f(n)$.
        by_contra h_contra
        obtain ⟨q, hq_prime, hq_div⟩ : ∃ q : ℕ, Nat.Prime q ∧ q ∣ (f n : ℕ) := by
          exact Nat.exists_prime_and_dvd ( by simpa using h_contra );
        have := Nat.dvd_trans hq_div ( h_divides_one ⟨ q, hq_prime.pos ⟩ hq_prime );
        haveI := Fact.mk hq_prime; simp_all ( config := { decide := Bool.true } ) [ ← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_sub ( Nat.one_le_pow _ _ hq_prime.pos ) ] ;
      simp ( config := { decide := Bool.true } ) [ h_fn_one ];
      linarith [ PNat.pos n ];
  · -- If $f$ is a bonza function for which $S$ is infinite, then $f(n) \le n$ for all $n \in \mathbb{N}$.
    have infinite_S_constraint (f : ℕ+ → ℕ+) (h : isBonza f) (hS_inf : (S f).Infinite) :
      ∀ n : ℕ+, (f n : ℕ) ≤ n := by
        -- Take any $n$. Since $S$ is infinite, there exists a prime $p \in S$ such that $p > f(n)$.
        intro n
        obtain ⟨p, hpS, hp_gt⟩ : ∃ p ∈ S f, (p : ℕ) > (f n : ℕ) := by
          exact Exists.elim ( hS_inf.exists_gt ( f n ) ) fun p hp => ⟨ p, hp.1, hp.2 ⟩;
        -- By Lemma~\ref{lem:fermat_congruence}, $f(n) \equiv n \pmod{p}$.
        have h_congr : (f n : ℕ) ≡ (n : ℕ) [MOD p] := by
          exact?;
        rw [ Nat.ModEq ] at h_congr;
        contrapose! h_congr;
        rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> linarith;
    exact le_trans ( infinite_S_constraint f h hS_finite n ) ( le_mul_of_one_le_left' ( by decide ) )

/-
Let $\mathbb{N}$ denote the set of positive integers. A function $f\colon\mathbb{N} \to \mathbb{N}$ is said to be \emph{bonza} if
$$f(a) \text{ divides } b^a - f(b)^{f(a)}$$
for all positive integers $a$ and $b$.
The smallest real constant $c$ such that $f(n) \leq cn$ for all bonza functions $f$ and all positive integers $n$ is $4$.
-/
theorem main_theorem (IsBonza : (ℕ+ → ℕ+) → Prop)
  (hisBonza : ∀ f, IsBonza f ↔ ∀ a b : ℕ+, (b : ℕ) ^ (a : ℕ) ≡ (f b : ℕ) ^ (f a : ℕ) [MOD f a]) :
  IsLeast {c : ℝ | ∀ f, IsBonza f → ∀ n : ℕ+, (f n : ℝ) ≤ c * (n : ℝ)} 4 := by
  -- To prove that 4 is the least such constant, we need to show that for any $c < 4$, there exists a bonza function $f$ and an $n$ such that $f(n) > cn$.
  have h_least : ∀ c : ℝ, c < 4 → ∃ f : ℕ+ → ℕ+, IsBonza f ∧ ∃ n : ℕ+, (f n : ℝ) > c * (n : ℝ) := by
    -- For any $c < 4$, we can choose the bonza function $f$ defined by $f(n) = 1$ if $n$ is odd, $f(n) = 4$ if $n \equiv 2 \pmod{4}$, and $f(n) = 16$ if $n \equiv 0 \pmod{4}$, and $n = 4$.
    intros c hc
    use f_construction;
    constructor;
    · exact hisBonza _ |>.2 construction_bonza;
    · exact ⟨ 4, show c * 4 < 16 by linarith ⟩;
  constructor;
  · aesop;
    exact_mod_cast upper_bound_four f ( by aesop ) n;
  · exact fun c hc => by contrapose! h_least; tauto;

#print axioms main_theorem
