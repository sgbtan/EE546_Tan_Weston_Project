import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

open Matrix
-- structure state_space (n : ℕ) where
--   A : Matrix (Fin n) (Fin n) ℝ
--   B : Matrix (Fin n) (Fin 1) ℝ
--   C : Matrix (Fin 1) (Fin n) ℝ



def join_col (M : Matrix (Fin n) (Fin n) α) (V : Matrix (Fin n) (Fin 1) α) : Matrix (Fin n) (Fin (n+1)) α:=
  λ i j =>
    if h: (j.val < n) then
      let k : Fin n := ⟨j.val, h⟩
      M i k
    else V i 0


def my_mat : Matrix (Fin 2) (Fin 2) ℕ := !![0, 1; 2, 3]
def my_vec : Matrix (Fin 2) (Fin 1) ℕ := !![4; 5]
def my_result : Matrix (Fin 2) (Fin 3) ℕ := !![0, 1, 4; 2, 3, 5]

#eval (join_col my_mat my_vec)

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





def is_eig_val (A : Matrix (Fin n) (Fin n) ℂ) (eig: ℂ): Prop :=
  ∃ v : Matrix (Fin n) (Fin 1) ℂ, A*v = eig•v

def is_eig_vec (A : Matrix (Fin n) (Fin n) ℂ) (v: Matrix (Fin n) (Fin 1) ℂ): Prop :=
  ∃ eig : ℂ, A*v = eig•v

def is_full_rank (mat : Matrix (Fin n) (Fin m) ℂ): Prop :=
  ∀ q : (Matrix (Fin 1) (Fin n) ℂ), q ≠ 0 → q * mat ≠ 0

def not_full_rank (mat : Matrix (Fin n) (Fin m) ℂ): Prop :=
  ¬is_full_rank mat



def I : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def eig_I : ℂ := 1
def evec_I : Matrix (Fin 2) (Fin 1) ℂ := !![1;1]

example : is_eig_val I eig_I := by
  unfold is_eig_val
  use evec_I
  simp[evec_I, I, eig_I]

example : is_eig_vec I evec_I := by
  unfold is_eig_vec
  use eig_I
  simp[evec_I, I, eig_I]



--(M: Matrix (Fin n) (Fin n) ℂ) (V: Matrix (Fin n) (Fin 1) ℝ)

structure block_matrix  (B : Matrix (Fin n) (Fin (n+1)) α) where
  M : Matrix (Fin n) (Fin (n)) α
  V : Matrix (Fin n) (Fin (1)) α
  R : Matrix (Fin n) (Fin (n+1)) α
  h : R = join_col M V

-- variable ( my_block_mat : block_matrix my_mat my_vec )
def my_block_mat : block_matrix my_result := ⟨my_mat, my_vec, join_col my_mat my_vec, by decide⟩

#eval my_block_mat

def my_fin : Fin 6 := ⟨ 5, by decide⟩
def new_block_mat : block_matrix
