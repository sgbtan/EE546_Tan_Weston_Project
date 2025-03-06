import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

open Matrix

abbrev n_mat (n:ℕ) := Matrix (Fin n) (Fin n) ℚ
abbrev n_vec (n:ℕ) := Matrix (Fin n) (Fin 1) ℚ
abbrev n_r_vec (n:ℕ) := Matrix (Fin 1) (Fin n) ℚ


example : (p ↔ q) ↔ (¬q ↔ ¬p) := by
  constructor
  . intro ⟨hpq, hqp⟩
    constructor
    . intro hnq hp
      exact hnq (hpq hp)
    . intro hnp hq
      exact hnp (hqp hq)
  . intro ⟨hnqp, hnpq⟩
    constructor
    . intro hp
      by_contra hnq
      exact (hnqp hnq) hp
    . intro hq
      by_contra hnp
      exact (hnpq hnp) hq



-- Define a matrix
def myMat : n_mat 2 :=
  !![1, 2,;
     4, 5]

def myVec : n_vec 2 :=
  !![5; 6]

def q : n_r_vec 2 :=
  !![5, 6]


def myMatVec : (n_mat 2) × (n_vec 2) := (myMat, myVec)

#eval myMatVec.1 * myMatVec.2

def TupMul (q : n_r_vec n) (MatVec : (n_mat n) × (n_vec n)) : (n_r_vec n) × (n_vec 1) :=
  (q*MatVec.1, q*MatVec.2)

def TupToMat (MatVec : (n_mat n) × (n_vec n)) : Matrix (Fin n) (Fin (n+1)) ℚ :=
  Matrix.of (λ (i : Fin n) (j : Fin (n+1)) =>
    if h: (j.val < n) then
      let k : Fin n := ⟨j.val, h⟩
      MatVec.1 i k
    else MatVec.2 i 0)

#check q * (TupToMat myMatVec)

example: ∀ (q : n_r_vec n) (MatVec : (n_mat n) × (n_vec n)),
 q * (TupToMat MatVec) = TupToMat (TupMul q MatVec) := by

  sorry

def my_lst : List ℕ := [0,1,2]

#eval my_lst[0]

#eval TupMul q myMatVec
#eval TupToMat myMatVec


def ListMul (q : n_r_vec n) (ListVec : List (n_vec n))
(out_list : List (n_vec 1) := List.nil) (i : ℕ := (ListVec.length-1)): (List (n_vec 1)) :=
  if i = 0 then out_list ++ [(q*ListVec[i]!)]
  else  ListMul q ListVec out_list (i-1) ++ [(q*ListVec[i]!)]

def ListToMat {n: ℕ} (B : List (n_vec n)) (m : ℕ := B.length):
Matrix (Fin n) (Fin m) ℚ :=
  Matrix.of (λ (i:Fin n) (j:Fin m) => B[j]! i 0)

def my_vec_lst : List (n_vec 3) := [!![1;2;3],!![1;2;4]]

def my_q : n_r_vec 3 := !![0, 1, 2]

#eval ListToMat (ListMul my_q my_vec_lst)


example: ∀ (q : n_r_vec n) (A : List (n_vec n)),
 q * (ListToMat A) = ListToMat (ListMul q A) := by

  sorry
