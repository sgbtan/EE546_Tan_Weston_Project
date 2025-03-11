import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs
import MyProject.Libraries.BlockMatLib


-- Converts a list of column vectors to a matrix
def listToMat {n: ℕ}
(B : List (Mat n 1))
: Mat n B.length :=
  λ (i:Fin n) (j:Fin B.length) => B[j] i 0


-- Constructs a list of the column vectors of the contralability matrix
def find_ctrb {n : ℕ}
(A : (Mat n n))
(B : (Mat n 1))
(i : ℕ := n)
: List (Mat n 1) :=
  if i-1 = 0
    then [B]
  else
    (find_ctrb A B (i-1)) ++ [(A^(i-1))*B]


-- Calls find_ctrb and converts the result into the contralability matrix
def ctrbMat {n : ℕ}
(A : (Mat n n))
(B : (Mat n 1)) :=
  listToMat (find_ctrb A B)


def find_eqb {n : ℕ}
(e : α)
(q : (Mat 1 n))
(B : (Mat n 1))
(i : ℕ := n)
: List (Mat 1 1) :=
  if i-1 = 0
    then [q*B]
  else
    (find_eqb e q B (i-1)) ++ [e^(i-1)•q*B]

def eqbMat {n : ℕ}
(e : α)
(q : (Mat 1 n))
(B : (Mat n 1)) :=
  listToMat (find_eqb e q B)


-- Constructs the matrix [(A-λI) B]
def ABe {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(e : α) :=
  ofBlocks (A-e•(1 : Mat n n)) B
