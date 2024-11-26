import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Eulerian Numbers

This module formalizes the definition of Eulerian numbers (Section 6.2 from
[Concrete Mathematics][knuth1989concrete]).

The Eulerian number $\left\langle{n\atop k}\right\rangle$ counts the number of permutations
of $\{1,2,\ldots,n\}$ with $k$ ascents.

## References

* [Concrete Mathematics][knuth1989concrete]
-/

def eulerian (n k:ℕ) : ℕ :=
  match n, k with
    | _, 0 => 1
    | 0, _ => 0
    | n+1, k => (k+1)*eulerian n k + (n+1-k)*eulerian n (k-1)

theorem eulerian_0_0 : eulerian 0 0 = 1 := by rfl

theorem eulerian_of_n_zero (n:ℕ) : eulerian n 0 = 1 := by
  simp [eulerian]

theorem eulerian_of_zero : eulerian 0 0 = 1 := eulerian_of_n_zero 0

theorem eulerian_of_zero_k (k:ℕ) (h:k>0): eulerian 0 k = 0 := by
  by_cases c : k = 0
  linarith
  simp [eulerian]

theorem eulerian_of_n_succ_n (n:ℕ) (h:n>0) : ∀ k, k>=n -> eulerian n k = 0 := by
  induction n with
    | zero => contradiction
    | succ n ih =>
        intros k jh
        rw [eulerian]
        by_cases c : n = 0
        · rw [c]
          simp
          constructor
          · apply eulerian_of_zero_k; linarith
          · by_cases d : 1-k = 0
            · exact Or.inl d
            · apply Or.inr
              apply eulerian_of_zero_k
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
