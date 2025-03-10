import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs
import MyProject.Libraries.BlockMatLib

-- Converts a list of column vectors to a matrix
def listToMat {n: ℕ} (B : List (Mat n 1)):
Mat n B.length :=
  λ (i:Fin n) (j:Fin B.length) => B[j] i 0

-- Constructs a list of the column vectors of the contralability matrix
def find_ctrb (A : (Mat n n)) (B : (Mat n 1)) (ctrb : List (Mat n 1) := List.nil) (i : ℕ := n):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(A^(i-1))*B]

-- Calls find_ctrb and converts the result into the contralability matrix
def ctrbMat (A : (Mat n n)) (B : (Mat n 1)) :=
  listToMat (find_ctrb A B)

-- Constructs the matrix [(A-λI) B]
def ABe (A : Mat n n) (B : Mat n 1) (e : α) :=
  ofBlocks (A-e•(1 : Mat n n)) B
