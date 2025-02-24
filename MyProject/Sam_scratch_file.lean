import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix
structure state_space (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℕ
  B : Matrix (Fin n) (Fin 1) ℕ
  C : Matrix (Fin 1) (Fin n) ℕ
  eig_A : ℂ

--variable(n:ℕ)
def join_col (M : Matrix (Fin n) (Fin n) ℕ) (V : Matrix (Fin n) (Fin 1) ℕ) : Matrix (Fin n) (Fin (n+1)) ℕ:=
  λ i j =>
    if h: j.val < n then
      let k : Fin n := Fin.mk j.val h
      M i k
    else V i 0

def M : Matrix (Fin 2) (Fin 2) ℕ := !![0, 1; 2, 3]
def V : Matrix (Fin 2) (Fin 1) ℕ := !![4; 5]
def result : Matrix (Fin 2) (Fin 3) ℕ := !![0, 1, 4; 2, 3, 5]
def scalar : ℕ := 5

#eval join_col M V
#eval scalar•V

example : join_col M V = result := by
  simp[M,V,result]
  unfold join_col
  funext i j
  fin_cases i <;> fin_cases j <;> simp


def is_eig_val (A : Matrix (Fin n) (Fin n) ℂ) (eig: ℂ): Prop :=
  ∃ v : Matrix (Fin n) (Fin 1) ℂ, A*v = eig•v
