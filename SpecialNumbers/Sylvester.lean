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
  · simp [sylvester]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by omega)

theorem sylvester_gt_one (n : ℕ) : 1 < sylvester n := sylvester_ge_two _
theorem sylvester_ge_one (n : ℕ) : 1 ≤ sylvester n := by linarith [sylvester_gt_one n]
theorem sylvester_ne_one (n : ℕ) : sylvester n ≠ 1 := by linarith [sylvester_gt_one n]

theorem sylvester_prod_finset_add_one {n : ℕ} :
    sylvester n = ∏ i ∈ Finset.range n, sylvester i + 1 := by
  rw [Finset.prod_range_induction _ (fun n => sylvester n - 1)]
  any_goals try simp [sylvester_ge_one]
  simp [sylvester, mul_comm]

theorem sylvester_strictMono : StrictMono sylvester := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp [sylvester]
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
  simp [logSylvesterBelow]
  refine le_of_mul_le_mul_left ?h1 ((by simp) : (0 : ℝ) < (2 ^ (m + 1)))
  rw [<- mul_assoc, <- mul_assoc, <- pow_sub₀]
  simp
  refine (Real.rpow_le_iff_le_log ?_ ?_).mp ?_
  any_goals try linarith [rsylvester_gt_one m, rsylvester_gt_one (m + 1)]
  simp [sylvester]
  rw [cast_sub]
  ring_nf
  gcongr
  any_goals try linarith [rsylvester_gt_one m, sylvester_gt_one m]

noncomputable def sylvesterConstant : ℝ := sorry

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
