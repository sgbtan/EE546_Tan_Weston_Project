import Mathlib.Tactic



def find_ctrb (A : (n_mat n)) (B : (n_vec n)) (ctrb : List ( n_vec n) := List.nil) (i : ℕ := n):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(A^(i-1))*B]

def ctrb_mat (A : (n_mat n)) (B : (n_vec n)) :=
  toMat (find_ctrb A B) n


def ABe (A : n_mat n) (B : n_vec n) (e : ℚ) :=
  join_col (A-e•(1 : n_mat n)) B
