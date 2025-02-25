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



def join_col (M : Matrix (Fin n) (Fin n) ℕ) (V : Matrix (Fin n) (Fin 1) ℕ) : Matrix (Fin n) (Fin (n+1)) ℕ:=
  λ i j =>
    if h: j.val < n then
      let k : Fin n := ⟨j.val, h⟩
      M i k
    else V i 0



def M : Matrix (Fin 2) (Fin 2) ℕ := !![0, 1; 2, 3]
def V : Matrix (Fin 2) (Fin 1) ℕ := !![4; 5]
def result : Matrix (Fin 2) (Fin 3) ℕ := !![0, 1, 4; 2, 3, 5]

#eval join_col M V

example : join_col M V = result := by
  simp[M,V,result]
  unfold join_col
  funext i j
  fin_cases i <;> fin_cases j <;> simp



-- example : ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) ℝ) (y : Matrix (Fin n) (Fin 1) ℝ), join_col x y :  (Matrix (Fin n) (Fin (n+1)) ℝ) := sorry



def is_eig_val (A : Matrix (Fin n) (Fin n) ℂ) (eig: ℂ): Prop :=
  ∃ v : Matrix (Fin n) (Fin 1) ℂ, A*v = eig•v

def is_eig_vec (A : Matrix (Fin n) (Fin n) ℂ) (v: Matrix (Fin n) (Fin 1) ℂ): Prop :=
  ∃ eig : ℂ, A*v = eig•v

def is_full_rank (mat : Matrix (Fin n) (Fin m) ℂ): Prop :=
  ∀ q : (Matrix (Fin 1) (Fin n) ℂ), q ≠ 0 → q * mat ≠ 0

def not_full_rank (mat : Matrix (Fin n) (Fin m) ℂ): Prop :=
  ¬is_full_rank mat
