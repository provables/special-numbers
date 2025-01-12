import Mathlib.Tactic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Complex.ExponentialBounds

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

-- theorem sylvester_strictMono : StrictMono sylvester := by
--   apply strictMono_nat_of_lt_succ
--   intro n
--   simp [sylvester]
--   have : 1 ≤ sylvester n - 1 := by
--     apply Nat.le_sub_one_of_lt
--     exact sylvester_gt_one n

theorem sylvester_prod_finset_add_one {n : ℕ} :
    sylvester n = ∏ i ∈ Finset.range n, sylvester i + 1 := by
  rw [Finset.prod_range_induction _ (fun n => sylvester n - 1)]
  any_goals try simp [sylvester_ge_one]
  simp [sylvester, Nat.mul_comm]
