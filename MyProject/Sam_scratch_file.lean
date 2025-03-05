import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic


-- structure state_space (n : ℕ) where
--   A : Matrix (Fin n) (Fin n) ℝ
--   B : Matrix (Fin n) (Fin 1) ℝ
--   C : Matrix (Fin 1) (Fin n) ℝ
open Matrix

def join_col (M : Matrix (Fin n) (Fin n) α) (V : Matrix (Fin n) (Fin 1) α) : Matrix (Fin n) (Fin (n+1)) α:=
  Matrix.of (λ i j =>
    if h: (j.val < n) then
      let k : Fin n := ⟨j.val, h⟩
      M i k
    else V i 0)


def my_mat : Matrix (Fin 2) (Fin 2) ℕ := !![0, 1; 3, 4]
def my_vec : Matrix (Fin 2) (Fin 1) ℕ := !![2; 5]
def my_result : Matrix (Fin 2) (Fin 3) ℕ := !![0, 1, 2; 3, 4, 5]

#check (join_col my_mat my_vec)

example : join_col my_mat my_vec = my_result := by
  simp[my_mat,my_vec,my_result]
  unfold join_col
  funext i j
  fin_cases i <;> fin_cases j <;> simp

example : ∀ (m : Matrix (Fin n) (Fin n) α) (v : Matrix (Fin n) (Fin 1) α), ∃ (r : (Matrix (Fin n) (Fin (n+1)) α)), join_col m v = r := by
  intro mat vec
  obtain r : (Matrix (Fin n) (Fin (n+1)) α) := join_col mat vec
  use r

example : ∀ (r : (Matrix (Fin n) (Fin (n+1)) α)), ∃ (m : Matrix (Fin n) (Fin n) α) (v : Matrix (Fin n) (Fin 1) α),  join_col m v = r := by
  intro r

  sorry





def is_eig_val (A : Matrix (Fin n) (Fin n) ℚ) (eig: ℚ): Prop :=
  ∃ v : Matrix (Fin n) (Fin 1) ℚ, A*v = eig•v

def is_eig_vec (A : Matrix (Fin n) (Fin n) ℚ) (v: Matrix (Fin n) (Fin 1) ℚ): Prop :=
  ∃ eig : ℚ, A*v = eig•v

def is_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ∀ q : (Matrix (Fin 1) (Fin n) ℚ), q ≠ 0 → q * mat ≠ 0

def not_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ¬is_full_rank mat



def I : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]
def e_val_I : ℚ := 1
def e_vec_I : Matrix (Fin 2) (Fin 1) ℚ := !![1;1]

example : is_eig_val I e_val_I := by
  unfold is_eig_val
  use e_vec_I
  simp[e_vec_I, I, e_val_I]

example : is_eig_vec I e_vec_I := by
  unfold is_eig_vec
  use e_val_I
  simp[e_vec_I, I, e_val_I]



--(M: Matrix (Fin n) (Fin n) ℚ) (V: Matrix (Fin n) (Fin 1) ℝ)

structure block_matrix  (B : Matrix (Fin n) (Fin (n+1)) α) where
  M : Matrix (Fin n) (Fin (n)) α
  V : Matrix (Fin n) (Fin (1)) α
  R : Matrix (Fin n) (Fin (n+1)) α
  h : R = join_col M V



-- variable ( my_block_mat : block_matrix my_mat my_vec )
def my_block_mat : block_matrix my_result := ⟨my_mat, my_vec, join_col my_mat my_vec, by decide⟩

#eval my_block_mat.R

def my_fin : Fin 6 := ⟨5, by decide⟩
--def new_block_mat : block_matrix









def v : Matrix (Fin 3) (Fin 1) ℚ := !![1;2;3]
def mat : Matrix (Fin 3) (Fin 3) ℚ := ![![1, 1, 1], ![2 ,2 ,2], ![ 3, 3, 3]]

def toMat {n: ℕ} (B : List (Matrix (Fin n) (Fin 1) ℚ)) (m : ℕ):
Matrix (Fin n) (Fin m) ℚ :=
  Matrix.of (λ (i:Fin n) (j:Fin m) => B[j]! i 0)

def my_v_list := List.cons v (List.cons v (List.cons v List.nil))

def v_mat := toMat my_v_list 3

set_option diagnostics true

#check mat
#check v_mat

#eval mat
#eval v_mat

#eval mat*mat
#eval v_mat*v_mat

#eval mat^3

def r : Matrix (Fin 1) (Fin 3) ℚ := !![-2, 1, 0]

example : ∃ q : Matrix (Fin 1) (Fin 3) ℚ, q ≠ 0 ∧ q * v_mat = 0 := sorry

example : not_full_rank v_mat := by
  unfold not_full_rank is_full_rank
  push_neg
  let r : Matrix (Fin 1) (Fin 3) ℚ := !![-2, 1, 0]
  use r
  constructor
  .
    trivial
  .
    simp[r,v_mat,my_v_list,v,toMat,Matrix.of]
    funext i j
    fin_cases i <;> fin_cases j <;> dsimp <;> sorry

#eval List.cons v (List.cons v List.nil)

def exp_mat  (A : (Matrix (Fin n) (Fin n) ℚ)) (i : ℕ) : (Matrix (Fin n) (Fin n) ℚ) :=
  if i = 0 then 1 else if i = 1 then A else A * exp_mat A (i-1)

def find_ctrb (A : (Matrix (Fin n) (Fin n) ℚ)) (B : (Matrix (Fin n) (Fin 1) ℚ)) (ctrb : List ( Matrix (Fin n) (Fin 1) ℚ) := List.nil) (i : ℕ := n):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(exp_mat A (i-1))*B]


def my_A : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -6, -5]
def my_B : Matrix (Fin 2) (Fin 1) ℚ := !![0; 1]

#eval toMat (find_ctrb my_A my_B) 2

abbrev MyMatType (n:ℕ) := Matrix (Fin n) (Fin n) ℚ

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

example : (p → q) ↔ (¬q → ¬p) := by
  constructor
  . intro hpq hnq hp
    exact hnq (hpq hp)
  . intro hnqp hp
    by_contra hq
    exact (hnqp hq) hp
