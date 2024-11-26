import Mathlib.Tactic

--  Function defining the nth Euclid number:
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


theorem euclid_eq_prod_euclid (n: ℕ) (h: n≥ 1) :
    euclid (n+1) = ∏ x∈ Finset.Icc 1 n, euclid x + 1 := by
  induction' n with n ih
  contradiction
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
  omega
  intro
  linarith
