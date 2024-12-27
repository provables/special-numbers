import Mathlib.Tactic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer

open Ring Polynomial

/-!
# Eulerian Numbers

This module formalizes the definition of Eulerian numbers (Section 6.2 from
[Concrete Mathematics][knuth1989concrete]).

The Eulerian number $\left\langle{n\atop k}\right\rangle$ counts the number of permutations
of $\{1,2,\ldots,n\}$ with $k$ ascents.

## References

* [Concrete Mathematics][knuth1989concrete]
-/

def eulerian (n k : ℕ) : ℕ :=
  match n, k with
    | _, 0 => 1
    | 0, _ => 0
    | n+1, k => (k+1)*eulerian n k + (n+1-k)*eulerian n (k-1)

theorem eulerian_0_0 : eulerian 0 0 = 1 := by rfl

theorem eulerian_of_n_zero (n:ℕ) : eulerian n 0 = 1 := by
  simp [eulerian]

theorem eulerian_of_zero : eulerian 0 0 = 1 := eulerian_of_n_zero 0

theorem eulerian_of_zero_k (k : ℕ) (h : k>0): eulerian 0 k = 0 := by
  by_cases c : k = 0
  linarith
  simp [eulerian]

theorem eulerian_of_n_succ_n (n : ℕ) (h : n>0) : ∀ k, k>=n -> eulerian n k = 0 := by
  induction n with
    | zero => contradiction
    | succ n ih =>
        intros k jh
        rw [eulerian]
        · by_cases c : n = 0
          · rw [c]
            simp
            constructor
            · exact eulerian_of_zero_k k (by linarith)
            · by_cases d : 1-k = 0
              · exact Or.inl d
              · exact Or.inr <| eulerian_of_zero_k (k-1) (by omega)
          · simp [ih (by omega) k (by omega), ih (by omega) (k-1) (by omega)]
        · omega

theorem eulerian_of_succ_n_n (n : ℕ) : eulerian (n+1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [eulerian]
      simp [ih]
      apply eulerian_of_n_succ_n
      repeat omega

lemma bar [NonAssocRing S] (r s : S) (a : ℕ) : (a • r) * s = r * (a • s) := by
  rw [mul_smul_comm]
  exact smul_mul_assoc a r s

variable [NonAssocRing R] [Pow R ℕ] [BinomialRing R] [NatPowAssoc R]

lemma foo (r : R) (n : ℕ) :
    (n+1) • choose (r+1) (n+1) = (r+1) * choose r n := by
  suffices h : (n+1).factorial • choose (r+1) (n+1) = n.factorial • (r+1) * choose r n by
    rw [Nat.factorial] at h
    nth_rw 1 [Nat.mul_comm] at h
    rw [mul_smul] at h
    rw [smul_mul_assoc] at h
    refine nsmul_right_injective n.factorial ?_ h
    exact Nat.factorial_ne_zero n
  rw [<- descPochhammer_eq_factorial_smul_choose]
  simp only [descPochhammer]
  rw [smeval_mul, smeval_X, smeval_comp, bar]
  simp [descPochhammer_eq_factorial_smul_choose]
