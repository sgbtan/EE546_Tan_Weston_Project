import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs
import MyProject.Libraries.BlockMatLib


-- Takes in a matrix A and vector B and constructs  the contralability matrix
noncomputable
def ctrbMat {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
: Mat n n :=
  Matrix.of (λ i j => (A^j.val*B) i 0)

theorem ctrb_first_col {n : ℕ}
(hn : n > 1)
(A : Mat n n)
(B : Mat n 1)
: getBlock (ctrbMat A B) 0 1 ⟨ by decide, by exact Nat.one_le_of_lt hn ⟩ = B := by
  ext i j
  simp[getBlock,ctrbMat]
  have hj : j = 0 := by
    exact eq_zero_of_zero_eq_one rfl j
  rw[hj]


instance inst_coe {j:ℕ} : Coe (Fin 1) (Fin (j + 1 - j)) :=
  ⟨ λ x => by
  have : j + 1 - j = 1 := by exact Nat.add_sub_self_left j 1
  rw[this]
  exact x
  ⟩

instance inst_coe_sort {n j:ℕ} : CoeSort (Mat n (j+1-j)) (Mat n 1) :=
  ⟨ λ M => λ i j => M i j ⟩

def hThing {j:ℕ}: j + 1 - j = 1 := by simp

@[simp]
theorem ctrb_cols
{n m: ℕ}
(hn : n > 0)
(hm : m < n)
(A : Mat n n)
(B : Mat n 1)
: (getBlock (ctrbMat A B) m (m+1) ⟨ by simp, by exact hm ⟩) = ↑(A^m)*B := by
  ext i j
  rcases i
  rcases j
  rename_i i hi j hj
  simp[getBlock,ctrbMat]
  have : j = 0 := by exact Nat.lt_one_iff.mp hj
  simp[this]
  have : (↑(cast (Eq.symm (inst_coe.proof_2 inst_coe.proof_1) : Fin 1 = Fin (m + 1 - m))  0) + m) = m := by
    refine Nat.add_left_eq_self.mpr ?_

    sorry
  simp[this]

  sorry



@[simp]
theorem ctrb_cols2
{n m: ℕ}
(hn : n > 0)
(hm : m < n)
(A : Mat n n)
(B : Mat n 1)
: (getBlock (ctrbMat A B) m (m+1) ⟨ by simp, by exact hm ⟩ : Mat n 1)
= ((A^m)*B : Mat n 1) := by
  induction m with
  | zero =>
    ext i j
    -- Get the concrete values from the Fin types
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    -- Since j is a Fin (m+1-m) = Fin 1, j must be 0
    have hj_zero : j = 0 := by exact Nat.lt_one_iff.mp hj
    simp [getBlock, ctrbMat, hj_zero]

  | succ n' ih =>
    ext i j
      -- Get the concrete values from the Fin types
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    -- Since j is a Fin (m+1-m) = Fin 1, j must be 0
    have hj_zero : j = 0 := by exact Nat.lt_one_iff.mp hj
    simp [getBlock, ctrbMat, hj_zero]
    have : Fin 1 = Fin (n' + 1 + 1 - (n' + 1)) := by sorry

    sorry







-- Constructs the matrix [(A-λI) B]
def ABe {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(e : α) :=
  ofBlocks (A-e•(1 : Mat n n)) B
