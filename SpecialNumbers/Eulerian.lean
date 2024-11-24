import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def eulerian (n k:ℕ) : ℕ :=
  match n, k with
    | _, 0 => 1
    | 0, _ => 0
    | n+1, k => (k+1)*eulerian n k + (n+1-k)*eulerian n (k-1)

theorem eulerian_of_n_zero (n:ℕ) : eulerian n 0 = 1 := by
  simp [eulerian]

theorem eulerian_of_0 : eulerian 0 0 = 1 := eulerian_of_n_zero 0

theorem eulerian_of_0_k (k:ℕ) (h:k>0): eulerian 0 k = 0 := by
  by_cases k = 0
  linarith
  simp [eulerian]

theorem eulerian_of_n_succ_n (n:ℕ) (h:n>0) : ∀ k, k>=n -> eulerian n k = 0 := by
  induction n with
    | zero => linarith
    | succ n ih =>
        intros k jh
        rw [eulerian]
        by_cases c : n = 0
        · rw [c]
          simp
          constructor
          · apply eulerian_of_0_k; linarith
          · by_cases d : 1-k = 0
            · omega
            · apply Or.inr
              apply eulerian_of_0_k
              omega
        · have x : eulerian n k = 0 := by
            apply ih
            repeat omega
          have y : eulerian n (k-1) = 0 := by
            apply ih
            repeat omega
          rw [x, y]
          omega
        omega

theorem eulerian_of_succ_n_n (n:ℕ) : eulerian (n+1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [eulerian]; simp
      rw [ih]; simp
      apply eulerian_of_n_succ_n
      repeat omega
