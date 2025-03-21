import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs


-- Combines matrices A and B to form a block matrix [A B]
@[simp]
def ofBlocks {n m p : ℕ}
(A : Mat n m)
(B : Mat n p)
: Mat n (m+p):=
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


-- Extracts a block made from columns of matrix A staring at column index a and ending at index a+l
@[simp]
def getBlock {n m : ℕ}
(A : Mat n m)
(a l: ℕ)
(h: a + l ≤ m)
: Mat n l :=
  λ i j =>
    let k : Fin m := ⟨j.val + a, by
    have hj : j<l := by exact j.isLt
    have hjl : l>j := by trivial
    have hjmja : j<m-a → j+a<m := by exact fun a_1 ↦ Nat.add_lt_of_lt_sub a_1
    have : l≤ m-a := by exact Nat.le_sub_of_add_le' h
    have hjm : j<m-a := by exact Fin.val_lt_of_le j this
    exact hjmja hjm
    ⟩
    A i k


-- Proves that q*[A B] = [q*A q*B] where q is row vector and A and B are matrices or column vectors
@[simp]
theorem distrib_ofBlocks {n m p : ℕ}
(q : Mat 1 n)
(A : Mat n m)
(B : Mat n p)
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
(q : Mat 1 n)
(A : Mat n m)
(a l : ℕ) (h: a + l ≤ m)
: q * (getBlock A a l h) = getBlock (q*A) a l h := by
  ext i j
  rcases i
  rcases j
  rename_i i hi j ji
  unfold getBlock
  simp[Matrix.mul_apply]
