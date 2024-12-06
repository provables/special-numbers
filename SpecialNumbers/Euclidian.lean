import Mathlib.Tactic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Euclid Numbers

This file introduces the Euclid numbers as defined in [knuth1989concrete].

## Main results

- Recurrence with a product of euclid numbers.
- Co-primality of euclid numbers.
- Explicit formula.

-/

/--
Definition by a simple recurrence. The more explicit recurrence is proved in
Theorem `euclid_eq_prod_euclid`.
-/
def euclid : ℕ -> ℕ
  | 0 => 1
  | 1 => 2
  | n+1 => (euclid n)^2 - (euclid n) + 1

-- The definition conforms to the standard one for the first few examples
@[simp]
theorem euclid_zero: euclid 0 = 1 := by rfl

@[simp]
theorem euclid_one: euclid 1 = 2 := by rfl

@[simp]
theorem euclid_two: euclid 2 = 3 := by rfl

@[simp]
theorem euclid_three: euclid 3 = 7 := by rfl

lemma factor (n : ℕ) : n^2 - n = (n-1)*n := by
  rw [Nat.pow_two]
  exact Eq.symm (Nat.sub_one_mul n n)

/--
The Euclid numbers satisfy the recurrence:
$$
e_{n+1} = \prod_{i=1}^n e_i + 1.
$$
-/
theorem euclid_eq_prod_euclid (n: ℕ):
    euclid (n+1) = ∏ x∈ Finset.Icc 1 n, euclid x + 1 := by
  induction' n with n ih
  simp
  by_cases c: n = 0
  rw[c]
  simp
  rw[euclid]
  simp
  rw[factor]
  rw[Finset.prod_Icc_succ_top]
  apply mul_eq_mul_right_iff.mpr
  apply Or.inl
  rw[ih]
  simp
  omega
  intro
  linarith

theorem euclid_n_geq_one (n: ℕ) (h: n ≥ 1) : euclid n > 1 := by
  induction' n with n ih
  contradiction
  by_cases c: n+1 = 1
  rw[c]
  simp
  have x: n ≥ 1 := by omega
  rw[euclid]
  simp
  have y: euclid n > 1 := ih x
  rw[pow_two]
  simp
  omega
  intro
  linarith

theorem euclid_geq_one (n : ℕ) : 1 <= euclid n := by
  by_cases h : n = 0
  · simp [h]
  · exact Nat.one_le_of_lt (euclid_n_geq_one n (by omega))

theorem euclid_m_n_mod_1 (m n : ℕ) (h1: m < n) (h2: m > 0) :
    euclid n % euclid m = 1 := by
  by_cases c: n=0
  omega
  have c2: n ≥ 1 := by omega
  have h1: n = n -1 + 1 := by omega
  rw [h1]
  rw[euclid_eq_prod_euclid]
  have : (euclid m) ∣  ∏ x ∈ Finset.Icc 1 (n-1), euclid x := by
    apply Finset.dvd_prod_of_mem
    refine Finset.mem_Icc.mpr ?ha.a
    omega

  rw[Nat.add_mod]
  have z : (∏ x ∈ Finset.Icc 1 (n-1), euclid x) % euclid m = 0 := by
    exact Nat.dvd_iff_mod_eq_zero.mp this
  rw[z]
  simp
  have h3: euclid m > 1 := by
    apply euclid_n_geq_one
    omega
  apply Nat.mod_eq_of_lt h3

lemma gcd_a_b_mod_b_a (a b: ℕ ) : gcd a b = gcd (b % a) a := by
  apply Nat.gcd_rec

lemma euclid_rel_prime_lt (m n : ℕ) (h: m < n) :
    gcd (euclid m) (euclid n) = 1 := by
  by_cases c: m = 0
  rw[c]
  simp
  have h3: m ≥ 1 := by omega
  rw[gcd_a_b_mod_b_a]
  rw[euclid_m_n_mod_1]
  have h4: euclid m > 1 := by
    apply euclid_n_geq_one
    linarith
  apply Nat.gcd_one_left
  assumption
  linarith

/--
The Euclid numbers are co-prime: $\gcd(e_n, e_m) = 1$, for $n\neq m$.
-/
theorem euclid_rel_prime (m n : ℕ) (h: m ≠ n) :
    gcd (euclid m) (euclid n) = 1 := by
    by_cases mltn : m < n
    exact euclid_rel_prime_lt m n mltn
    rw[gcd_comm]
    simp at mltn
    have h1: n < m := by omega
    apply euclid_rel_prime_lt
    exact h1

/--
Auxiliary sequences for proving the explicity form of the Euclidean numbers.
-/
noncomputable def a (n : ℕ) : ℝ := (1/2^n)*Real.log (euclid n - 1/2)
noncomputable def b (n : ℕ) : ℝ := (1/2^n)*Real.log (euclid n + 1/2)

example : a 0 = -Real.log 2 := by
  simp [a]
  norm_num
  simp

/--
The sequences $a$ and $b$ satisfy the inequality $a_n < b_n$ for all $n : ℕ$.
-/
theorem a_lt_b (n : ℕ) : a n < b n := by
  simp [a, b]
  have h : (1 : ℝ) <= euclid n := by
    norm_cast
    exact euclid_geq_one n
  refine (Real.log_lt_log_iff ?_ ?_).mpr ?_
  · simp
    have h2 : 2⁻¹ < (1 : ℝ) := by norm_num
    exact lt_of_lt_of_le h2 h
  · rw [<- add_zero 0]
    apply add_lt_add
    linarith
    norm_num
  · apply (add_lt_add_iff_left ((euclid n) : ℝ)).mpr
    norm_num

theorem a_increasing : Monotone a := by sorry
theorem b_decreasing : Antitone b := by sorry

/--
The sequence $a$ is bounded: there exists $M$ such that $a_n ≤ M$, for all $n$.
-/
theorem a_bounded_above : BddAbove (Set.range a) := by
  refine bddAbove_def.mpr ?_
  use (b 0)
  intro y h
  simp at h
  obtain ⟨ z, hz ⟩ := h
  rw [<- hz]
  have c : a z < b z := a_lt_b z
  have d : b z <= b 0 := by
    apply Antitone.imp
    exact b_decreasing
    linarith
  linarith

open Filter

/--
The sequence $a$ is bounded, so it cannot diverge to $+\infty$.
-/
lemma a_not_diverging : ¬Tendsto a atTop atTop := by
  by_contra h
  have c : ¬BddAbove (Set.range a) := Filter.unbounded_of_tendsto_atTop h
  have d : BddAbove (Set.range a) := a_bounded_above
  contradiction

/--
The sequence $a$ converges.
-/
theorem a_converges : ∃ l, Tendsto a atTop (nhds l) := by
  have h2 : ¬Tendsto a atTop atTop := a_not_diverging
  refine Or.resolve_left ?_ h2
  apply tendsto_of_monotone
  exact a_increasing
