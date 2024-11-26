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

theorem euclid_eq_prod_euclid (n: ℕ) (h: n≥ 1) :
    euclid n+1 = ∏ x∈ Finset.Icc 1 n, euclid x + 1 := by
  induction' n with n ih
  contradiction
  simp
  by_cases c: n = 1
  rw[c]
  simp
  rw[Finset.prod_Icc_succ_top]
  rw[Finset.empty_product]
