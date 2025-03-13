import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs
import MyProject.Libraries.BlockMatLib


-- Takes in a matrix A and vector B and constructs  the contralability matrix
def ctrbMat {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
: Matrix (Fin n) (Fin n) ℚ :=
  λ i j => (A^j.val*B) i 0

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


instance {j:ℕ} : Coe (Fin 1) (Fin (j + 1 - j)) :=
  ⟨ λ x => by
  have : j + 1 - j = 1 := by exact Nat.add_sub_self_left j 1
  rw[this]
  exact x
  ⟩

instance {n j:ℕ} : CoeSort (Matrix (Fin n) (Fin (j + 1 - j)) ℚ) (Matrix (Fin n) (Fin 1) ℚ) :=
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
  have : ↑(cast (Eq.symm (instCoeFinOfNatNatHSubHAdd_myProject.proof_2 instCoeFinOfNatNatHSubHAdd_myProject.proof_1) : Fin 1 = Fin (m + 1 - m)) 0) + m = m := by

    sorry
  rw[this]



-- Constructs
-- def find_eqb {n : ℕ}
-- (e : α)
-- (q : (Mat 1 n))
-- (B : (Mat n 1))
-- (i : ℕ := n)
-- : List (Mat 1 1) :=
--   if i-1 = 0
--     then [q*B]
--   else
--     (find_eqb e q B (i-1)) ++ [e^(i-1)•q*B]

-- def eqbMat {n : ℕ}
-- (e : α)
-- (q : (Mat 1 n))
-- (B : (Mat n 1)) :=
--   listToMat (find_eqb e q B)


-- Constructs the matrix [(A-λI) B]
def ABe {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(e : α) :=
  ofBlocks (A-e•(1 : Mat n n)) B
