import Mathlib.Tactic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Sylvester sequence

This file introduces the Sylvester sequence.
This is sequence [A000058](https://oeis.org/A000058) in [oeis]

## Implementation notes

We follow the presentantion from https://en.wikipedia.org/wiki/Sylvester%27s_sequence.

## Main results

- Basic facts.
- Sylvester sequence is strictly monotonic.
- Recurrence formula.
- Pairwise co-primality.
- Explicit formula.

## References

* https://en.wikipedia.org/wiki/Sylvester%27s_sequence
* [The On-Line Encyclopedia of Integer Sequences][oeis]
-/

open Nat

-- set_option linter.all true

def sylvester : ℕ -> ℕ
  | 0 => 2
  | n + 1 => (sylvester n) * (sylvester n - 1) + 1

@[simp]
theorem sylvester_zero : sylvester 0 = 2 := by rfl

@[simp]
theorem sylvester_one : sylvester 1 = 3 := by rfl

@[simp]
theorem sylvester_two : sylvester 2 = 7 := by rfl

@[simp]
theorem sylvester_three : sylvester 3 = 43 := by rfl

theorem sylvester_ge_two (n : ℕ) : 2 ≤ sylvester n := by
  induction' n with n ih
  · simp
  · simp only [sylvester, reduceLeDiff]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by omega)

theorem sylvester_gt_one (n : ℕ) : 1 < sylvester n := sylvester_ge_two _
theorem sylvester_ge_one (n : ℕ) : 1 ≤ sylvester n := by linarith [sylvester_gt_one n]
theorem sylvester_ne_one (n : ℕ) : sylvester n ≠ 1 := by linarith [sylvester_gt_one n]

theorem sylvester_prod_finset_add_one {n : ℕ} :
    sylvester n = ∏ i ∈ Finset.range n, sylvester i + 1 := by
  rw [Finset.prod_range_induction _ (fun n => sylvester n - 1)] <;> try simp [sylvester_ge_one]
  simp [sylvester, mul_comm]

theorem sylvester_strictMono : StrictMono sylvester := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [sylvester]
  calc
    sylvester n * (sylvester n - 1) + 1 > sylvester n * (sylvester n - 1) := by linarith
    _ ≥ sylvester n := Nat.le_mul_of_pos_right _ <| le_sub_one_of_lt <| sylvester_gt_one n

-- Coprimality

-- TODO: translate the proof from `Euclid.euclid_mod_eq_one` here
theorem sylvester_mod_eq_one {m n : ℕ} (h1 : m < n) (h2 : 0 < m) :
    sylvester n % sylvester m = 1 := by sorry

-- TODO: translate the proof from `Euclid.euclid_coprime_of_lt` here
private theorem sylvester_coprime_of_lt {m n : ℕ} (h : m < n) :
    Coprime (sylvester m) (sylvester n) := by sorry

theorem sylvester_coprime {m n : ℕ} (h : m ≠ n) : Coprime (sylvester m) (sylvester n) := by
  by_cases c : m < n
  · exact sylvester_coprime_of_lt c
  · exact coprime_comm.mp <| sylvester_coprime_of_lt <| by omega

-- Explicit formula

private noncomputable def logSylvesterBelow (n : ℕ) : ℝ := (2 ^ n)⁻¹ * Real.log (sylvester n - 2⁻¹)
private noncomputable def logSylvesterAbove (n : ℕ) : ℝ := (2 ^ n)⁻¹ * Real.log (sylvester n + 2⁻¹)

private theorem rsylvester_gt_one (n : ℕ) : (1 : ℝ) < sylvester n :=
  Nat.one_lt_cast.mpr <| sylvester_gt_one n

private theorem logSylvesterBelow_monotone : Monotone logSylvesterBelow := by
  refine monotone_nat_of_le_succ ?h
  intro m
  simp only [logSylvesterBelow]
  refine le_of_mul_le_mul_left ?h1 ((by simp) : (0 : ℝ) < (2 ^ (m + 1)))
  move_mul [<- 2 ^ _]
  rw [mul_inv_cancel_of_invertible, <- pow_sub₀, one_mul, Nat.add_sub_cancel_left, pow_one]
    <;> try linarith
  refine (Real.pow_le_iff_le_log ?_ ?_).mp ?_
  any_goals try linarith [rsylvester_gt_one m, rsylvester_gt_one (m + 1)]
  simp only [sylvester]
  push_cast [sylvester_gt_one]
  rw [sub_sq]
  ring_nf
  gcongr
  linarith

private theorem logSylvesterAbove_strictAnti : StrictAnti logSylvesterAbove := by
  refine strictAnti_nat_of_succ_lt ?h
  intro m
  simp only [logSylvesterAbove]
  refine lt_of_mul_lt_mul_left ?h1 ((by simp) : (0 : ℝ) ≤ (2 ^ (m + 1)))
  move_mul [<- 2 ^ _]
  rw [mul_inv_cancel_of_invertible, <- pow_sub₀, one_mul, Nat.add_sub_cancel_left, pow_one]
    <;> try linarith
  refine (Real.lt_pow_iff_log_lt ?_ ?_).mp ?_
  any_goals try linarith
  simp only [sylvester]
  push_cast [sylvester_gt_one]
  rw [add_sq]
  ring_nf
  gcongr
  linarith [rsylvester_gt_one m]

private theorem logSylvesterBelow_lt_logSylvesterAbove {n : ℕ} :
    logSylvesterBelow n < logSylvesterAbove n := by
  dsimp only [logSylvesterBelow, logSylvesterAbove]
  gcongr
  all_goals linarith [rsylvester_gt_one n]

private theorem logSylvesterAbove_mem_upperBounds {n : ℕ} :
    logSylvesterAbove n ∈ upperBounds (Set.range logSylvesterBelow) := by
  intro y h
  obtain ⟨z, hz⟩ := h
  trans logSylvesterAbove (z ⊔ n)
  · trans logSylvesterBelow (z ⊔ n)
    · linarith [logSylvesterBelow_monotone <| Nat.le_max_left z n]
    · exact le_of_lt logSylvesterBelow_lt_logSylvesterAbove
  · linarith [(StrictAnti.antitone logSylvesterAbove_strictAnti) <| Nat.le_max_right z n]

private theorem bddAbove_logSylvesterBelow : BddAbove (Set.range logSylvesterBelow) := by
  use logSylvesterAbove 0
  exact logSylvesterAbove_mem_upperBounds

private noncomputable def sylvesterLogConstant : ℝ := ⨆ i, logSylvesterBelow i
noncomputable def sylvesterConstant : ℝ := Real.exp sylvesterLogConstant

@[simp]
private theorem log_sylvesterConstant_eq_sylvesterConstant :
    Real.log sylvesterConstant = sylvesterLogConstant := by
  simp [sylvesterConstant]

open Filter

private theorem logSylvesterBelow_tendsto_sylvesterLogConstant :
    Tendsto logSylvesterBelow atTop (nhds sylvesterLogConstant) :=
  tendsto_atTop_ciSup logSylvesterBelow_monotone bddAbove_logSylvesterBelow

private theorem logSylvesterBelow_le_sylvesterLogConstant {n : ℕ} :
    logSylvesterBelow n ≤ sylvesterLogConstant :=
  Monotone.ge_of_tendsto logSylvesterBelow_monotone logSylvesterBelow_tendsto_sylvesterLogConstant n

private theorem sylvesterLogConstant_lt_logSylvesterAbove {n : ℕ} :
    sylvesterLogConstant < logSylvesterAbove n := by
  have h : sylvesterLogConstant ≤ logSylvesterAbove (n + 1) :=
    (isLUB_le_iff <| isLUB_of_tendsto_atTop logSylvesterBelow_monotone
      logSylvesterBelow_tendsto_sylvesterLogConstant).mpr <| logSylvesterAbove_mem_upperBounds
  have h2 : logSylvesterAbove (n + 1) < logSylvesterAbove n :=
    logSylvesterAbove_strictAnti (by linarith)
  linarith

theorem sylvesterConstant_pos : 0 < sylvesterConstant := by sorry

theorem sylvester_le_const_pow {n : ℕ} :
    sylvester n ≤ sylvesterConstant ^ (2 ^ (n + 1)) + 1 / 2 := by
  sorry

theorem const_pow_lt_sylvester_add_one {n : ℕ} :
    sylvesterConstant ^ (2 ^ (n + 1)) + 1 / 2 < sylvester n + 1 := by
  sorry

theorem sylvester_eq_floor_constant_pow {n : ℕ} :
    sylvester n = ⌊sylvesterConstant ^ (2 ^ (n + 1)) + 1 / 2⌋₊ := by
  refine ((Nat.floor_eq_iff ?h).mpr ?hb).symm
  · linarith [pow_pos sylvesterConstant_pos (2 ^ (n + 1))]
  · exact ⟨sylvester_le_const_pow, const_pow_lt_sylvester_add_one⟩
