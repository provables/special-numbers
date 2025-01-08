import Mathlib.Tactic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Euclid Numbers

This file introduces the Euclid numbers as defined in [knuth1989concrete].
This is sequence [A129871](https://oeis.org/A129871) in [oeis]

## Implementation notes

The reference [knuth1989concrete] names the sequence $(e_n)_{n\ge 1}$ as
*Euclid numbers*, while [oeis] names it
$(e_n)_{n\ge 0}$ as *Sylvester's sequence*. We chose to follow
the notation from [knuth1989concrete].

## Main results

- Recurrence with a product of Euclid numbers.
- Co-primality of Euclid numbers.
- Explicit formula.

## References

* [Concrete Mathematics][knuth1989concrete]
* [The On-Line Encyclopedia of Integer Sequences][oeis]
-/

namespace Euclid

/--
The sequence of Euclid numbers $(e_n)_{n\ge 0}$.

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
theorem euclid_prod_finset_add_one {n : ℕ} :
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
theorem euclid_prod_finset_add_one_of_pos {n : ℕ} (h : n ≥ 1) :
    euclid n = ∏ x∈Finset.Icc 1 (n - 1), euclid x + 1 := by
  have c : n = (n - 1) + 1 := by omega
  rw [c, euclid_prod_finset_add_one]
  simp

/--
Euclid numbers are positive.
-/
theorem euclid_gt_zero {n : ℕ} : 0 < euclid n := by
  unfold euclid
  split
  · linarith
  · linarith
  · simp [Nat.pow_two]

theorem euclid_ne_zero {n : ℕ} : NeZero (euclid n) := NeZero.of_pos euclid_gt_zero

/--
Euclid numbers are $\ge 1$.
-/
theorem euclid_ge_one {n : ℕ} : 1 ≤ euclid n := by
  simp [Nat.one_le_iff_ne_zero]
  linarith [@euclid_gt_zero n]

/--
Only $e_0 = 1$.
-/
theorem euclid_gt_one_of_pos {n : ℕ} (h : n ≥ 1) : 1 < euclid n := by
  cases n
  · contradiction
  · simp [euclid_prod_finset_add_one, euclid_gt_zero]

/--
The Euclid numbers are strictly increasing: $e_n < e_{n+1}$, for all $n\in\mathbb{N}$.
-/
theorem euclid_strictMono : StrictMono euclid := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases c : n = 0
  · simp [c, euclid]
  · have h : euclid n - 1 ≥ 1 := Nat.le_sub_one_of_lt <| euclid_gt_one_of_pos <| by omega
    calc
      euclid (n + 1) = (euclid n) * (euclid n - 1) + 1 := by simp [euclid, pow_two, Nat.mul_sub_one]
      _ ≥ (euclid n) * 1 + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _
      _ > euclid n := by linarith

/--
$e_n \equiv 1\ (\mathrm{mod}~e_m)$, when $0 < m < n$.
-/
theorem euclid_mod_eq_one {m n : ℕ} (h1 : m < n) (h2 : 0 < m) :
    euclid n % euclid m = 1 := by
  by_cases c : n=0
  · omega
  · rw [euclid_prod_finset_add_one_of_pos]
    · have d : (euclid m) ∣  ∏ x ∈ Finset.Icc 1 (n-1), euclid x := by
        apply Finset.dvd_prod_of_mem
        exact Finset.mem_Icc.mpr (by omega)
      rw [Nat.add_mod]
      simp [Nat.dvd_iff_mod_eq_zero.mp d]
      exact Nat.mod_eq_of_lt (euclid_gt_one_of_pos (by linarith))
    · linarith

private lemma euclid_coprime_of_lt {m n : ℕ} (h : m < n) :
    Nat.Coprime (euclid m) (euclid n) := by
  by_cases c : m = 0
  · simp [c]
  · simp [Nat.Coprime]
    rw [Nat.gcd_rec, euclid_mod_eq_one]
    · simp
    · linarith
    · omega

/--
The Euclid numbers are co-prime: $\gcd(e_n, e_m) = 1$, for $n\neq m$.
-/
theorem euclid_coprime {m n : ℕ} (h : m ≠ n) : Nat.Coprime (euclid m) (euclid n) := by
  by_cases c : m < n
  · exact euclid_coprime_of_lt c
  · exact Nat.coprime_comm.mp <| euclid_coprime_of_lt <| by omega

-- An auxiliary sequence that converges to the constant in the explicit formula for
-- the Euclid numbers.
private noncomputable def logEuclidSubHalf (n : ℕ) : ℝ := 1 / 2 ^ n * Real.log (euclid n - 1 / 2)

private theorem logEuclidSubHalf_monotone : Monotone logEuclidSubHalf := by
  have euclid_ge_real_one (m : ℕ) : (1 : ℝ) ≤ euclid m := Nat.one_le_cast.mpr euclid_ge_one
  refine monotone_nat_of_le_succ ?ha
  intro m
  simp [logEuclidSubHalf]
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

-- An auxiliary sequence that bounds `logEuclidSubHalf` from above and helps proving
-- its convergence.
private noncomputable def logEuclidAddHalf : ℕ → ℝ
  | 0 => 1
  | n => 1 / 2 ^ n * Real.log (euclid n + 1 / 2)

private theorem logEuclidAddHalf_strictAnti : StrictAnti logEuclidAddHalf := by
  have euclid_ge_real_one (m : ℕ) : (1 : ℝ) ≤ euclid m := Nat.one_le_cast.mpr euclid_ge_one
  refine strictAnti_nat_of_succ_lt ?ha
  intro m
  simp [logEuclidAddHalf]
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

private theorem logEuclidSubHalf_lt_logEuclidAddHalf {n : ℕ} :
    logEuclidSubHalf n < logEuclidAddHalf n := by
  simp [logEuclidSubHalf, logEuclidAddHalf]
  cases n
  case zero =>
    norm_num
    have c : Real.log (1 / 2) < 0 := (Real.log_neg_iff <| by linarith).mpr <| by linarith
    linarith
  case succ m =>
    simp
    have h : (1 : ℝ) ≤ euclid (m + 1) := Nat.one_le_cast.mpr euclid_ge_one
    refine (Real.log_lt_log_iff ?_ ?_).mpr ?_
    · simp
      exact lt_of_lt_of_le (by norm_num) h
    · exact add_pos_of_nonneg_of_pos (by linarith) (by norm_num)
    · exact (add_lt_add_iff_left ((euclid (m + 1)) : ℝ)).mpr (by norm_num)

private theorem bddAbove_logEuclidSubHalf : BddAbove (Set.range logEuclidSubHalf) := by
  refine bddAbove_def.mpr ?_
  use logEuclidAddHalf 0
  intro y h
  obtain ⟨ z, hz ⟩ := h
  rw [<- hz]
  have d : logEuclidAddHalf z ≤ logEuclidAddHalf 0 := StrictAnti.antitone logEuclidAddHalf_strictAnti (by linarith)
  linarith [@logEuclidSubHalf_lt_logEuclidAddHalf z]

open Filter

/--
The sequence `pl_euc_m` converges to $\log E$, where $E$ is the contant in the
explicit `euclid_formula`.
-/
private theorem logEuclidSubHalf_tendsto : ∃ l, Tendsto logEuclidSubHalf atTop (nhds l) := by
  have h2 : ¬Tendsto logEuclidSubHalf atTop atTop := by
    by_contra h
    let c := unbounded_of_tendsto_atTop h
    let d := bddAbove_logEuclidSubHalf
    contradiction
  exact Or.resolve_left (tendsto_of_monotone logEuclidSubHalf_monotone) h2


/--
The constant $\log E$ in the explicit formula for the Euclid numbers
`euclid_formula`.
-/
private noncomputable def euclidLogConstant : ℝ := Exists.choose logEuclidSubHalf_tendsto

/--
Constant $E$ in the explicit `euclid_formula`.
-/
noncomputable def euclidConstant : ℝ := Real.exp euclidLogConstant

private theorem logEuclidSubHalf_tendsto_euclidLogConstant : Tendsto logEuclidSubHalf atTop (nhds euclidLogConstant) := by
  simp [euclidLogConstant]
  apply Exists.choose_spec logEuclidSubHalf_tendsto

/--
The sequence `pl_euc_m` is bounded above by `euclid_log_constant`:
$$
\frac{1}{2^n}\log\left(e_n - \frac{1}{2}\right) \le \log E
$$
for all $n\in\mathbb{N}$.
-/
private theorem logEuclidSubHalf_le_euclidLogConstant {n : ℕ} : logEuclidSubHalf n ≤ euclidLogConstant := by
  exact Monotone.ge_of_tendsto logEuclidSubHalf_monotone logEuclidSubHalf_tendsto_euclidLogConstant n

private theorem euclidLogConstant_lt_logEuclidAddHalf {n : ℕ} : euclidLogConstant < logEuclidAddHalf n := by
  have h : logEuclidAddHalf (n + 1) ∈ upperBounds (Set.range logEuclidSubHalf) := by
    refine mem_upperBounds.mpr ?h
    intros x h
    obtain ⟨ m, h2 ⟩ := h
    rw [<- h2]
    let z := max m (n + 1)
    have a1 : logEuclidSubHalf m ≤ logEuclidSubHalf z := logEuclidSubHalf_monotone (by omega)
    have a2 : logEuclidAddHalf z ≤ logEuclidAddHalf (n + 1) := StrictAnti.antitone logEuclidAddHalf_strictAnti (by omega)
    have a3 : logEuclidSubHalf z < logEuclidAddHalf z := logEuclidSubHalf_lt_logEuclidAddHalf
    linarith
  have c : euclidLogConstant ≤ logEuclidAddHalf (n + 1) := (isLUB_le_iff
    (isLUB_of_tendsto_atTop logEuclidSubHalf_monotone logEuclidSubHalf_tendsto_euclidLogConstant)).mpr h
  have d : logEuclidAddHalf (n + 1) < logEuclidAddHalf n := logEuclidAddHalf_strictAnti (by linarith)
  linarith

/--
$0 < E$.
-/
theorem euclidConstant_pos : 0 < euclidConstant := Real.exp_pos euclidLogConstant

/--
$e_n \le E^{2^n} + \frac{1}{2}$ for all $n\in\mathbb{N}$.
-/
theorem euclid_le_constant_pow {n : ℕ} : euclid n ≤ euclidConstant ^ (2 ^ n) + 1 / 2 := by
  have euclid_ge_real_one (m : ℕ) : (1 : ℝ) ≤ euclid m := Nat.one_le_cast.mpr euclid_ge_one
  apply tsub_le_iff_right.mp
  refine (Real.log_le_log_iff ?ha ?hb).mp ?h
  · linarith [euclid_ge_real_one n]
  · exact pow_pos euclidConstant_pos (2 ^ n)
  · rw [Real.log_pow]
    refine (div_le_iff₀' (by positivity)).mp ?h2
    simp [euclidConstant]
    have c : logEuclidSubHalf n ≤ euclidLogConstant := by
      exact logEuclidSubHalf_le_euclidLogConstant
    rw [div_eq_inv_mul]
    simp [logEuclidSubHalf] at *
    exact c

/--
$E^{2^n} + \frac{1}{2} < e_n + 1$ for all $n\in\mathbb{N}$.
-/
theorem constant_pow_lt_euclid_add_one {n : ℕ} : euclidConstant ^ (2 ^ n) + 1 / 2 < euclid n + 1 := by
  have euclid_ge_real_one (m : ℕ) : (1 : ℝ) ≤ euclid m := Nat.one_le_cast.mpr euclid_ge_one
  apply lt_tsub_iff_right.mp
  rw [add_sub_assoc]
  norm_num
  refine (Real.log_lt_log_iff ?ha ?hb).mp ?h
  · exact pow_pos euclidConstant_pos (2 ^ n)
  · linarith [euclid_ge_real_one n]
  · norm_num
    refine (lt_div_iff₀' (by positivity)).mp ?he
    rw [div_eq_inv_mul]
    simp [euclidConstant]
    let c := @euclidLogConstant_lt_logEuclidAddHalf n
    simp [logEuclidAddHalf] at c
    split at c
    · let d := @euclidLogConstant_lt_logEuclidAddHalf 2
      simp [logEuclidAddHalf] at d
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

/--
$e_n = \lfloor E^{2^n} + \frac{1}{2}\rfloor$ for all $n\in\mathbb{N}$.
-/
theorem euclid_eq_floor_constant_pow {n : ℕ} : euclid n = ⌊euclidConstant ^ (2 ^ n) + 1 / 2⌋₊ := by
  symm
  refine (Nat.floor_eq_iff ?h).mpr ?hb
  · linarith [pow_pos euclidConstant_pos (2 ^ n)]
  · exact ⟨ euclid_le_constant_pow, constant_pow_lt_euclid_add_one ⟩

end Euclid
