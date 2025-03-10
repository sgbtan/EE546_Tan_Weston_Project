import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs
import MyProject.Libraries.BlockMatLib


def find_ctrb {n m: ℕ}
(A : Mat n n)
(B : Mat n 1)
(ctrb : Mat n m := !![]):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(A^(i-1))*B]

def ctrb_mat (A : (Mat n n)) (B : (Mat n 1)) :=
  toMat (find_ctrb A B) n


def ABe (A : Mat n n) (B : Mat n 1) (e : α) :=
  join_col (A-e•(1 : n_mat n)) B
