import Mathlib.Tactic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Complex.ExponentialBounds

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

theorem sylvester_mod_eq_one {m n : ℕ} (h1 : m < n) (h2 : 0 < m) :
    sylvester n % sylvester m = 1 := by sorry

private theorem sylvester_coprime_of_lt {m n : ℕ} (h : m < n) :
    Coprime (sylvester m) (sylvester n) := by sorry

theorem sylvester_coprime {m n : ℕ} (h : m ≠ n) : Coprime (sylvester m) (sylvester n) := by
  sorry

-- Explicit formula

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
