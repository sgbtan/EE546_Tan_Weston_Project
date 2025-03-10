import Mathlib.Tactic

@[simp]
def ofBlocks {n m p : ℕ}
(A : Matrix (Fin n) (Fin m) ℚ)
(B : Matrix (Fin n) (Fin p) ℚ)
: Matrix (Fin n) (Fin (m+p)) ℚ :=
  λ i j => if h : j.val < m then
  let k : Fin m := ⟨ j.val, h ⟩
  A i k
  else
  have : j-m < p := by
    have h1 : j ≥ m := by exact Nat.le_of_not_lt h
    have h2 : j < m+p := by exact j.isLt
    simp[h1,h2]
    exact Nat.sub_lt_left_of_lt_add h1 h2
  let k : Fin p := ⟨ j.val - m, this ⟩
  B i k

@[simp]
def getBlock {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
(a b: ℕ) (h: a ≤ b ∧ b < m)
: Matrix (Fin n) (Fin (b-a)) ℚ :=
  λ i j =>
  let k : Fin m := ⟨ j.val+a, by
  obtain ⟨ h1, h2 ⟩ := h
  have ha : a < m := by exact Nat.lt_of_le_of_lt h1 h2
  have hj : j < b-a := by exact j.isLt
  have hjb : j + a < b := by exact Nat.add_lt_of_lt_sub hj
  exact Nat.lt_trans hjb h2
  ⟩
  A i k

namespace Test

variable (A : Matrix (Fin 4) (Fin 4) ℚ)
         (B : Matrix (Fin 4) (Fin 1) ℚ)
         (q : Matrix (Fin 1) (Fin 4) ℚ)

#check getBlock (q*(ofBlocks A B)) 0 4 ⟨ by exact Nat.zero_le 4, by exact lt_add_one 4 ⟩
#check getBlock (q*(ofBlocks A B)) 4 4 ⟨ by exact Nat.le_of_ble_eq_true rfl, by exact lt_add_one 4 ⟩

def W : Matrix (Fin 2) (Fin 2) ℚ := !![1,2;3,4]
def R : Matrix (Fin 2) (Fin 1) ℚ := !![1;1]
def s : Matrix (Fin 1) (Fin 2) ℚ := !![1,1]

#eval ofBlocks W R
#eval getBlock (ofBlocks W R) 0 1 ⟨ by exact Nat.zero_le 1, by exact Nat.one_lt_succ_succ 1 ⟩

end Test

@[simp]
theorem distrib_ofBlocks {n m p : ℕ}
(q : Matrix (Fin 1) (Fin n) ℚ)
(A : Matrix (Fin n) (Fin m) ℚ)
(B : Matrix (Fin n) (Fin p) ℚ)
: q * (ofBlocks A B) = ofBlocks (q*A) (q*B) := by
  ext i j
  rcases i
  rcases j
  rename_i i hi j ji
  unfold ofBlocks
  by_cases hj: j < m
  <;>
  simp[Matrix.mul_apply]

@[simp]
theorem distrib_getBlock {n m: ℕ}
(q : Matrix (Fin 1) (Fin n) ℚ)
(A : Matrix (Fin n) (Fin m) ℚ)
(a b : ℕ) (h: a ≤ b ∧ b < m)
: q * (getBlock A a b h) = getBlock (q*A) a b h := by
  ext i j
  rcases i
  rcases j
  rename_i i hi j ji
  unfold getBlock
  simp[Matrix.mul_apply]
