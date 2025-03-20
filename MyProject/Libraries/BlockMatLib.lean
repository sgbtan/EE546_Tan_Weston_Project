import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs


-- Create n x m+p matrix out of n x m and n x p matrices
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


def getCol {n m : ℕ}
(A : Mat n m)
(a : ℕ)
(h: a < m)
: Mat n 1 :=
  λ i j =>
    let k : Fin m := ⟨a, by exact h⟩
    A i k


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

-- Gets a-b columns of n x m matrix
@[simp]
def getBlockOld {n m : ℕ}
(A : Mat n m)
(a b: ℕ)
(h: a < b ∧ b ≤ m := by decide)
: Mat n (b-a) :=
  λ i j =>
    let k : Fin m := ⟨ j.val+a, by
    obtain ⟨ h1, h2 ⟩ := h
    have ha : a < m := by exact Nat.lt_of_lt_of_le h1 h2
    have hj : j < b-a := by exact j.isLt
    have hjb : j + a < b := by exact Nat.add_lt_of_lt_sub hj
    exact Nat.lt_of_lt_of_le hjb h2
    ⟩
    A i k





def myMat : Mat 1 4 := !![0,1,2,3]
#eval getBlock myMat 2 2 (by decide)


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

-- getBlock (ofBlocks A B) i j = B
-- Prove that a + b - b = a
theorem add_sub_self
(m p : ℕ)
(hm : m > 0)
: m + p - 1 - (m - 1) = p := by
  cases m with
  | zero =>
    contradiction
  | succ m =>
    simp


-- def undoHelper
-- (A : Mat n m)
-- (B : Mat n p)
-- (h : m-1 ≤ m+p-1 ∧ m+p-1 < m+p := by decide)
-- (hm : m > 0)
-- : Prop :=
--   let AB := ofBlocks A B
--   let Bnew : Mat n p := cast (by rw[add_sub_self m p hm]) (getBlock AB (m-1) (m+p-1) h)
--   B = Bnew

-- def hm (m:ℕ): Prop := m<0

-- theorem undoBlock {n m p: ℕ}
-- (A : Mat n m)
-- (B : Mat n p)
-- (h : m-1 ≤ m+p-1 ∧ m+p-1 < m+p := by decide)
-- (hm : m > 0)
-- : undoHelper A B h hm:= by
--   unfold undoHelper
--   intro x y

--   sorry



-- ∀ A B i j : A = B → getBlock A i j = getBlock B i j
