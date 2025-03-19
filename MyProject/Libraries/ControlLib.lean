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

-- @[simp]
-- theorem ctrb_cols
-- {n m: ℕ}
-- (hn : n > 0)
-- (hm : m < n)
-- (A : Mat n n)
-- (B : Mat n 1)
-- : (getBlock (ctrbMat A B) m (m+1) ⟨ by simp, by exact hm ⟩) = ↑(A^m)*B := by
--   ext i j
--   rcases i
--   rcases j
--   rename_i i hi j hj
--   simp[getBlock,ctrbMat]
--   have : j = 0 := by exact Nat.lt_one_iff.mp hj
--   simp[this]

--   sorry

@[simp]
theorem ctrb_cols
{n m: ℕ}
(hn : n > 0)
(hm : m < n)
(A : Mat n n)
(B : Mat n 1)
: (getBlock (ctrbMat A B) m (m+1) ⟨ by simp, by exact hm ⟩) = ↑(A^m)*B := by
  ext i j
  -- Get the concrete values from the Fin types
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  -- Since j is a Fin (m+1-m) = Fin 1, j must be 0
  have hj_zero : j = 0 := by exact Nat.lt_one_iff.mp hj
  simp [getBlock, ctrbMat, hj_zero]

  -- Now we need to work out the indexing
  -- When we call getBlock with (m, m+1), we extract column m
  -- In the definition of getBlock, we convert j+a to an index for A
  -- In our case, j=0 and a=m, so we're getting index 0+m = m
  have index_eq : j + m = m := by simp [hj_zero]
  rw [index_eq]

  -- Now the goal should be something like (A^m * B) i 0 = (A^m * B) i 0
  -- Which is true by reflexivity
  rfl



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
