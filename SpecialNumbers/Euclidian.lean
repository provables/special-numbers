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
def euclid : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 1 => (euclid n) ^ 2 - (euclid n) + 1

-- The definition conforms to the standard one for the first few examples
@[simp]
theorem euclid_zero : euclid 0 = 1 := by rfl

@[simp]
theorem euclid_one : euclid 1 = 2 := by rfl

@[simp]
theorem euclid_two : euclid 2 = 3 := by rfl

@[simp]
theorem euclid_three : euclid 3 = 7 := by rfl

/--
The Euclid numbers satisfy the recurrence:
$$
e_{n+1} = \prod_{i=1}^n e_i + 1.
$$
-/
theorem euclid_eq_prod_euclid (n : ℕ) :
    euclid (n + 1) = ∏ x ∈ Finset.Icc 1 n, euclid x + 1 := by
  induction' n with n ih
  · simp
  · rw[euclid]
    · simp [Nat.pow_two, Finset.prod_Icc_succ_top]
      rw [← Nat.sub_one_mul]
      apply mul_eq_mul_right_iff.mpr
      left
      simp [ih]
    · simp

/--
Another expression of `euclid_eq_prod_euclid` for easier application when $n\ge 1$:
$$
e_n = \prod_{i=1}^{n-1} e_i + 1.
$$
-/
theorem euclid_of_n_eq_prod_euclid (n : ℕ) (h : n ≥ 1) :
    euclid n = ∏ x∈Finset.Icc 1 (n - 1), euclid x + 1 := by
  have c : n = (n - 1) + 1 := by omega
  rw [c, euclid_eq_prod_euclid]
  simp

/--
Euclid numbers are positive.
-/
theorem euclid_gt_zero (n : ℕ) : 0 < euclid n := by
  unfold euclid
  split
  · linarith
  · linarith
  · simp [Nat.pow_two]

/--
Euclid numbers are $\ge 1$.
-/
theorem euclid_ge_one (n : ℕ) : 1 ≤ euclid n := by
  simp [Nat.one_le_iff_ne_zero]
  linarith [euclid_gt_zero n]

/--
Only $e_0 = 1$.
-/
theorem euclid_gt_one (n : ℕ) (h : n ≥ 1) : 1 < euclid n := by
  cases n
  · contradiction
  · simp [euclid_eq_prod_euclid, euclid_gt_zero]

/--
The Euclid numbers are strictly increasing: $e_n < e_{n+1}$, for all $n\in\N$.
-/
theorem euclid_increasing (n : ℕ) : euclid n < euclid (n + 1) := by
  by_cases c : n = 0
  · simp [c, euclid]
  · have h2 : euclid n - 1 ≥ 1 := Nat.le_sub_one_of_lt (euclid_gt_one n (by omega))
    calc
      euclid (n + 1) = (euclid n) * (euclid n) - euclid n + 1 := by simp [euclid, pow_two]
      _ = (euclid n) * (euclid n - 1) + 1 := by rw [Nat.mul_sub_one]
      _ ≥ (euclid n) * 1 + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ h2) 1
      _ > euclid n := by linarith

theorem euclid_monotone : Monotone euclid :=
  monotone_nat_of_le_succ (fun n => Nat.le_of_succ_le (euclid_increasing n))

theorem euclid_m_n_mod_one (m n : ℕ) (h1 : m < n) (h2 : m > 0) :
    euclid n % euclid m = 1 := by
  by_cases c : n=0
  · omega
  · rw [euclid_of_n_eq_prod_euclid]
    · have d : (euclid m) ∣  ∏ x ∈ Finset.Icc 1 (n-1), euclid x := by
        apply Finset.dvd_prod_of_mem
        exact Finset.mem_Icc.mpr (by omega)
      rw [Nat.add_mod]
      simp [Nat.dvd_iff_mod_eq_zero.mp d]
      exact Nat.mod_eq_of_lt (euclid_gt_one _ (by linarith))
    · linarith

lemma euclid_rel_prime_lt (m n : ℕ) (h : m < n) :
    (euclid m).gcd (euclid n) = 1 := by
  by_cases c : m = 0
  · simp [c]
  · rw [Nat.gcd_rec, euclid_m_n_mod_one]
    · simp
    · linarith
    · omega

/--
The Euclid numbers are co-prime: $\gcd(e_n, e_m) = 1$, for $n\neq m$.
-/
theorem euclid_rel_prime (m n : ℕ) (h : m ≠ n) :
    (euclid m).gcd (euclid n) = 1 := by
  by_cases c : m < n
  · exact euclid_rel_prime_lt m n c
  · rw [Nat.gcd_comm]
    exact euclid_rel_prime_lt n m (by omega)

noncomputable def pl_euc_m (n : ℕ) : ℝ := 1 / 2 ^ n * Real.log (euclid n - 1 / 2)

theorem pl_euc_m_monotone : Monotone pl_euc_m := by
  have euclid_ge_real_one (m : ℕ) : (1 : ℝ) ≤ euclid m := Nat.one_le_cast.mpr <| euclid_ge_one m
  refine monotone_nat_of_le_succ ?ha
  intro m
  simp [pl_euc_m]
  refine le_of_mul_le_mul_left ?h1 ((by simp) : (0 : ℝ)<(2 ^ (m + 1)))
  simp
  rw [← mul_assoc, ← pow_sub₀ 2 (by linarith) (by linarith), Nat.add_sub_self_left m 1,
      pow_one, ← Real.log_rpow, Real.rpow_two]
  · refine (Real.log_le_log_iff ?hh1 ?hh2).mpr ?hh3
    · apply sq_pos_iff.mpr
      exact Ne.symm <| ne_of_lt <| by linarith [euclid_ge_real_one m]
    · linarith [euclid_ge_real_one (m + 1)]
    · cases m
      case zero => norm_num
      case succ m =>
        calc
          (((euclid (m + 1)) : ℝ) - 2⁻¹) ^ 2 = (euclid (m + 1)) ^ 2 - euclid (m + 1) + 1 - 3 / 4 := by ring
          _ = ((euclid (m + 1 + 1)) : ℝ) - 3 / 4 := by
            simp
            rw [← Nat.cast_pow, <- Nat.cast_sub]
            norm_cast
            exact Nat.le_self_pow (by linarith) (euclid (m + 1))
          _ ≤ ((euclid (m + 1 + 1)) : ℝ) - 2⁻¹ := by linarith
  · linarith [euclid_ge_real_one m]

-- The pl_euc_p sequence is decreasing
noncomputable def pl_euc_p : ℕ → ℝ
  | 0 => 1
  | n => 1 / 2 ^ n * Real.log (euclid n + 1 / 2)

theorem pl_euc_p_antitone : StrictAnti pl_euc_p := by
  have euclid_ge_real_one (m : ℕ) : (1 : ℝ) ≤ euclid m := Nat.one_le_cast.mpr <| euclid_ge_one m
  refine strictAnti_nat_of_succ_lt ?ha
  intro m
  simp [pl_euc_p]
  split
  · simp
    rw [<- Real.log_rpow]
    · refine (Real.log_lt_iff_lt_exp ?hu).mpr ?hv
      · exact Real.rpow_pos_of_pos (by linarith) (2⁻¹)
      · let h := @Real.quadratic_le_exp_of_nonneg (1 : ℝ) (by linarith)
        norm_num at h
        have z : ((2 : ℝ) + 2⁻¹) ^ ((2 : ℝ)⁻¹) < 5 / 2 := by
          refine (Real.rpow_inv_lt_iff_of_pos ?hx ?hy ?hz).mpr ?hw
          all_goals linarith
        linarith
    · linarith
  · refine lt_of_mul_lt_mul_left ?h1 ((by simp) : (0 : ℝ) ≤ (2 ^ (m + 1)))
    simp
    rw [← mul_assoc, ← pow_sub₀ 2 (by linarith) (by linarith), Nat.add_sub_self_left m 1,
        pow_one, ← Real.log_rpow, Real.rpow_two]
    · refine (Real.log_lt_log_iff ?hh1 ?hh2).mpr ?hh3
      · linarith
      · apply sq_pos_iff.mpr
        exact Ne.symm <| ne_of_lt <| by linarith [euclid_ge_real_one m]
      · by_cases c : m = 1
        · rw [c]
          norm_num
        · rename_i h
          simp at h
          calc
            ((euclid (m + 1)) : ℝ) + 2⁻¹ = (euclid m) ^ 2 - euclid m + 3 / 2 := by
              simp [euclid]
              rw [<- Nat.cast_pow, <- Nat.cast_sub]
              · simp [add_assoc]
                norm_num
              · exact Nat.le_self_pow (by linarith) (euclid m)
            _ = (euclid m + 2⁻¹) ^ 2 - 2 * euclid m + 5 / 4 := by ring
            _ < (euclid m + 2⁻¹) ^ 2 := by
              apply lt_sub_iff_add_lt.mp
              apply sub_lt_sub_left
              linarith [euclid_ge_real_one m]
    · linarith [euclid_ge_real_one m]

/--
The sequences $a$ and $b$ satisfy the inequality $a_n < b_n$ for all $n : ℕ$.
-/
theorem pl_euc_m_lt_pl_euc_p (n : ℕ) : pl_euc_m n < pl_euc_p n := by
  simp [pl_euc_m, pl_euc_p]
  cases n
  case zero =>
    simp
    norm_num
    have c : Real.log (1 / 2) < 0 := (Real.log_neg_iff (by linarith)).mpr (by linarith)
    linarith
  case succ m =>
    simp
    have h : (1 : ℝ) ≤ euclid (m + 1) := Nat.one_le_cast.mpr <| euclid_ge_one (m + 1)
    refine (Real.log_lt_log_iff ?_ ?_).mpr ?_
    · simp
      exact lt_of_lt_of_le (by norm_num) h
    · exact add_pos_of_nonneg_of_pos (by linarith) (by norm_num)
    · exact (add_lt_add_iff_left ((euclid (m + 1)) : ℝ)).mpr (by norm_num)

/--
The sequence $a$ is bounded: there exists $M$ such that $a_n ≤ M$, for all $n$.
-/
theorem pl_euc_m_bounded_above : BddAbove (Set.range pl_euc_m) := by
  refine bddAbove_def.mpr ?_
  use (pl_euc_p 0)
  intro y h
  obtain ⟨ z, hz ⟩ := h
  rw [<- hz]
  have d : pl_euc_p z ≤ pl_euc_p 0 := StrictAnti.antitone pl_euc_p_antitone (by linarith)
  linarith [pl_euc_m_lt_pl_euc_p z]

open Filter

/--
The sequence $a$ converges.
-/
theorem pl_euc_m_converges : ∃ l, Tendsto pl_euc_m atTop (nhds l) := by
  have h2 : ¬Tendsto pl_euc_m atTop atTop := by
    by_contra h
    let c := Filter.unbounded_of_tendsto_atTop h
    let d := pl_euc_m_bounded_above
    contradiction
  exact Or.resolve_left (tendsto_of_monotone pl_euc_m_monotone) h2


/--
Logarithm of the constant E, where $e_n = \lfloor E^{2^n} + 1/2\rfloor$.
-/
noncomputable def euclid_log_constant : ℝ := Exists.choose pl_euc_m_converges

/--
Constant E, where $e_n = \lfloor E^{2^n} + 1/2\rfloor$.
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
theorem pl_euc_m_tendsto_euclid_log_constant : Tendsto pl_euc_m atTop (nhds euclid_log_constant) := by
  simp [euclid_log_constant]
  apply Exists.choose_spec pl_euc_m_converges

/--
The sequence `a` is bounded above by `euclid_log_constant`.
-/
theorem pl_euc_m_le_euclid_log_constant (n : ℕ) : pl_euc_m n ≤ euclid_log_constant := by
  exact Monotone.ge_of_tendsto pl_euc_m_monotone pl_euc_m_tendsto_euclid_log_constant n

/--
The sequence `b` is bounded below by `euclid_log_constant`.
-/
theorem euclid_log_constant_le_pl_euc_p (n : ℕ) : euclid_log_constant < pl_euc_p n := by
  have h : pl_euc_p (n + 1) ∈ upperBounds (Set.range pl_euc_m) := by
    refine mem_upperBounds.mpr ?h
    intros x h
    obtain ⟨ m, h2 ⟩ := h
    rw [<- h2]
    let z := max m (n + 1)
    have a1 : pl_euc_m m ≤ pl_euc_m z := pl_euc_m_monotone (by omega)
    have a2 : pl_euc_p z ≤ pl_euc_p (n + 1) := StrictAnti.antitone pl_euc_p_antitone (by omega)
    have a3 : pl_euc_m z < pl_euc_p z := pl_euc_m_lt_pl_euc_p z
    linarith
  have c : euclid_log_constant ≤ pl_euc_p (n + 1) := (isLUB_le_iff
    (isLUB_of_tendsto_atTop pl_euc_m_monotone pl_euc_m_tendsto_euclid_log_constant)).mpr h
  have d : pl_euc_p (n + 1) < pl_euc_p n := pl_euc_p_antitone (by linarith)
  linarith

theorem euclid_constant_pos : 0 < euclid_constant := Real.exp_pos euclid_log_constant

theorem euc_le_euclid_constant (n : ℕ) : euclid n ≤ euclid_constant ^ (2 ^ n) + 1 / 2 := by
  have euclid_ge_real_one (m : ℕ) : (1 : ℝ) ≤ euclid m := Nat.one_le_cast.mpr <| euclid_ge_one m
  apply tsub_le_iff_right.mp
  refine (Real.log_le_log_iff ?ha ?hb).mp ?h
  · linarith [euclid_ge_real_one n]
  · exact pow_pos euclid_constant_pos (2 ^ n)
  · rw [Real.log_pow]
    refine (div_le_iff₀' (by positivity)).mp ?h2
    rw [log_of_const_eq_log_const]
    push_cast
    have c : pl_euc_m n ≤ euclid_log_constant := by
      exact pl_euc_m_le_euclid_log_constant n
    rw [div_eq_inv_mul]
    simp [pl_euc_m] at *
    exact c

theorem euclid_constant_lt_euc (n : ℕ) : euclid_constant ^ (2 ^ n) + 1 / 2 < euclid n + 1 := by
  have euclid_ge_real_one (m : ℕ) : (1 : ℝ) ≤ euclid m := Nat.one_le_cast.mpr <| euclid_ge_one m
  apply lt_tsub_iff_right.mp
  rw [add_sub_assoc]
  norm_num
  refine (Real.log_lt_log_iff ?ha ?hb).mp ?h
  · exact pow_pos euclid_constant_pos (2 ^ n)
  · linarith [euclid_ge_real_one n]
  · norm_num
    refine (lt_div_iff₀' (by positivity)).mp ?he
    rw [div_eq_inv_mul]
    simp
    let c := euclid_log_constant_le_pl_euc_p n
    simp [pl_euc_p] at c
    split at c
    · let d := euclid_log_constant_le_pl_euc_p 2
      simp [pl_euc_p] at d
      norm_num at *
      have e : (1 / 4) * Real.log (7 / 2) < Real.log (3 / 2) := by
        rw [<- Real.log_rpow]
        refine (Real.log_lt_log_iff ?haa ?hbb).mpr ?hcc
        any_goals positivity
        · refine (Real.lt_rpow_inv_iff_of_pos ?hhx ?hy ?hz).mp ?aa
          any_goals positivity
          norm_num
      linarith
    · exact c

theorem euclid_formula (n : ℕ) : euclid n = ⌊euclid_constant ^ (2 ^ n) + 1 / 2⌋₊ := by
  symm
  refine (Nat.floor_eq_iff ?h).mpr ?hb
  · linarith [pow_pos euclid_constant_pos (2 ^ n)]
  · exact ⟨ euc_le_euclid_constant n, euclid_constant_lt_euc n ⟩
