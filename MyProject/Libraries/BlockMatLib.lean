import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs


-- Create n x m+p matrix out of n x m and n x p matrices
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

-- Gets a-b columns of n x m matrix
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

-- Proves that q*[A B] = [q*A q*B] where q is row vector and A and B are matrices or column vectors
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

-- Proves that block B of q*[A B C] is equal to q*B
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
