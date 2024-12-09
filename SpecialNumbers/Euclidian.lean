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


theorem euclid_n_gt_one (n: ℕ) (h: n ≥ 1) : euclid n > 1 := by
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
  · exact Nat.one_le_of_lt (euclid_n_gt_one n (by omega))

theorem zero_lt_euc_m_minus_one_half (m : ℕ) : 0 < (↑(euclid m) - (2:ℝ)⁻¹) := by
  let em := euclid_geq_one m
  simp
  have emr : (1:ℝ) ≤ euclid m := by
    exact Nat.one_le_cast.mpr em
  linarith


lemma f_gt_zero (n : ℕ) (f: ℕ → ℕ) (h: f n ≥ 1) :  f n  > 0 := by
  exact h


theorem euclid_n_geq_zero (n: ℕ) : euclid n > 0 := by
  by_cases z: n = 0
  rw[z]
  simp
  have hh: euclid n > 1 := by
    apply euclid_n_gt_one
    omega
  exact Nat.one_le_of_lt hh


theorem euclid_increasing (n: ℕ) : euclid n < euclid (n+1) := by
  by_cases c: n = 0
  rw[c]
  rw[euclid]
  simp
  have h1: n ≥ 1 := by omega
  have h2: euclid n -1 ≥ 1 := by
    let _:= euclid_n_gt_one n h1
    omega
  calc euclid (n+1) = (euclid n)^2 - euclid n + 1 := by simp[euclid]
    _ = (euclid n) * (euclid n - 1) + 1 := by
        rw[pow_two]
        simp
        rw[Nat.mul_sub_one]
    _ ≥ euclid n + 1 := by
        apply add_le_add_right
        apply le_mul_of_one_le_right
        simp
        linarith
    _ > euclid n := by linarith


#eval 1%1
#eval 2%1
#eval 2%0
#eval 1%1


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
    apply euclid_n_gt_one
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
    apply euclid_n_gt_one
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


noncomputable def pl_euc_m (n: ℕ) : ℝ := 1/2^n * Real.log (euclid n - 1/2)


example (a b c : ℝ) (h1: c > 0) (h2: a ≤ b) : (c * a ≤ c * b) := by
  exact (mul_le_mul_iff_of_pos_left h1).mpr h2


#check mul_le_mul_iff_of_pos_left
#check @mul_le_mul_iff_of_pos_left


theorem powers_two (m: ℕ) : 2^(m+1) * ((2:ℝ)^(m))⁻¹ = 2 := by
  refine (mul_inv_eq_iff_eq_mul₀ ?hb).mpr ?a
  simp
  rw[← Real.rpow_natCast]
  rw[← Real.rpow_natCast]
  nth_rw 2 [← pow_one 2]
  rw[Nat.cast_add]
  rw[Real.rpow_add]
  ring
  simp


example (x : ℝ) : x^2 = x^(2:ℝ) := by
  exact Eq.symm (Real.rpow_two x)


#leansearch "(a b: R)(h: log(a) ≤ log(b)) : a ≤ b."

#check Real.partialOrder.proof_2
#check Real.le_rpow_iff_log_le

#check Real.log_le_log_iff

#leansearch "(a b : R) : (a - b)^2 = a^2 -2a*b - b^2."


theorem euc_recurrence (m : ℕ) (h: m ≥ 1) : euclid (m+1) = (euclid m)^2 - euclid m + 1 := by
  by_cases c: m = 1
  · simp[c]
  · rw[euclid]
    simp
    omega

theorem euc_recurrence_real (m : ℕ) (h: m ≥ 1) : euclid (m+1) = ((euclid m:ℝ))^2 - euclid m + 1 := by
  rw[euclid]
  · simp
    rw[← Nat.cast_pow]
    apply Nat.cast_sub
    apply Nat.le_self_pow
    omega
  · intro
    linarith


lemma log_fact : Real.log (1 / 2) ≤ 1 / 2 ^ 1 * Real.log (↑2 - 1 / 2) := by
  norm_num
  have h1: Real.log (1/2) < 0 := by
    refine Real.log_neg ?b0 ?b1
    linarith
    linarith
  have h2: Real.log (3/2) > 0 := by
    refine (Real.log_pos_iff ?hx).mpr ?a1
    linarith
    linarith
  linarith


-- The pl_euc_m sequence is increasing
theorem pl_euc_m_monoton : Monotone pl_euc_m := by
  refine monotone_nat_of_le_succ ?ha
  intro m
  by_cases c: m = 0
  · simp[c]
    rw[pl_euc_m]
    norm_num
    rw[pl_euc_m]
    rw[euclid]
    exact log_fact

  have h1: m ≥ 1 := by omega
  simp[pl_euc_m]
  refine le_of_mul_le_mul_left ?h1 (?h2:(0:ℝ)<(2^(m+1)))
  · simp
    rw[← mul_assoc]
    rw[powers_two]
    rw[← Real.log_rpow]
    refine (Real.log_le_log_iff ?b1 ?b2).mpr ?b3
    · rw[Real.rpow_two]
      apply sq_pos_iff.mpr
      simp
      by_contra c
      let em := zero_lt_euc_m_minus_one_half m
      linarith
    · exact zero_lt_euc_m_minus_one_half (m+1)
    · calc (euclid m - (2:ℝ)⁻¹)^(2:ℝ) = (euclid m - (2:ℝ)⁻¹)^(2:ℕ) := by exact Real.rpow_two _
        _ = ((euclid m):ℝ)^2 - 2*((euclid m):ℝ) *2⁻¹ + (2⁻¹)^2 := by rw[sub_pow_two]
        _ = ((euclid m):ℝ)^2 - euclid m + 1 - 3/4 := by ring
        _ = (euclid (m+1):ℝ) - 3/4 := by rw[← euc_recurrence_real]; exact h1
        _ ≤ (euclid (m+1):ℝ) - 2⁻¹ := by linarith
    · exact zero_lt_euc_m_minus_one_half _
  · refine pow_pos (by linarith) (m+1)


-- The pl_euc_p sequence is decreasing
noncomputable def pl_euc_p (n: ℕ) : ℝ := 1/2^n * Real.log (euclid n + 1/2)

-- lemma pow_log_euclid_plus_decreasing (n : ℕ) :
--     pl_euc_p n > pl_euc_p (n+1) := by sorry

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
  let c := a_lt_b z
  have d : b z <= b 0 := by
    apply Antitone.imp
    exact b_decreasing
    linarith
  linarith

open Filter

/--
The sequence $a$ converges.
-/
theorem a_converges : ∃ l, Tendsto a atTop (nhds l) := by
  have h2 : ¬Tendsto a atTop atTop := by
    by_contra h
    have c : ¬BddAbove (Set.range a) := Filter.unbounded_of_tendsto_atTop h
    have d : BddAbove (Set.range a) := a_bounded_above
    contradiction
  exact Or.resolve_left (tendsto_of_monotone a_increasing) h2


/--
Logarithm of the constant E, where $e_n = \lfloor E^{2^n} \rfloor$.
-/
noncomputable def euclid_log_constant : ℝ := Exists.choose a_converges

/--
Constant E, where $e_n = \lfloor E^{2^n} \rfloor$.
-/
noncomputable def euclid_constant : ℝ := Real.exp euclid_log_constant

@[simp]
theorem exp_of_log_const_eq_const : Real.exp euclid_log_constant = euclid_constant := by
  simp [euclid_log_constant, euclid_constant]

@[simp]
theorem log_of_const_eq_log_const : Real.log euclid_constant = euclid_log_constant := by
  simp [euclid_log_constant, euclid_constant]

/--
The sequence `a` converges to `euclid_log_constant`.
-/
theorem a_tendsto_euclid_log_constant : Tendsto a atTop (nhds euclid_log_constant) := by
  simp [euclid_log_constant]
  apply Exists.choose_spec a_converges

/--
The sequence `a` is bounded above by `euclid_log_constant`.
-/
theorem a_le_euclid_log_constant (n : ℕ) : a n <= euclid_log_constant := by
  exact Monotone.ge_of_tendsto a_increasing a_tendsto_euclid_log_constant n

/--
The sequence `b` is bounded below by `euclid_log_constant`.
-/
theorem euclid_log_constant_le_b (n : ℕ) : euclid_log_constant <= b n := by
  have h : b n ∈ upperBounds (Set.range a) := by
    refine mem_upperBounds.mpr ?h
    intros x h
    simp at h
    obtain ⟨ m, h2 ⟩ := h
    rw [<- h2]
    let z := max m n
    have a1 : a m <= a z := by
      apply a_increasing
      omega
    have a2 : b z <= b n := by
      apply b_decreasing
      omega
    have a3 : a z <= b z := le_of_lt (a_lt_b z)
    linarith
  let c := a_tendsto_euclid_log_constant
  let d := isLUB_of_tendsto_atTop a_increasing c
  exact (isLUB_le_iff d).mpr h
