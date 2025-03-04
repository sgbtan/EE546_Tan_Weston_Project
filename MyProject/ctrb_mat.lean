import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

def join_col (M : Matrix (Fin n) (Fin n) α) (V : Matrix (Fin n) (Fin 1) α) : Matrix (Fin n) (Fin (n+1)) α:=
  Matrix.of (λ i j =>
    if h: (j.val < n) then
      let k : Fin n := ⟨j.val, h⟩
      M i k
    else V i 0)

def is_eig_val (A : Matrix (Fin n) (Fin n) ℚ) (eig: ℚ): Prop :=
  ∃ v : Matrix (Fin n) (Fin 1) ℚ, A*v = eig•v

def is_eig_vec (A : Matrix (Fin n) (Fin n) ℚ) (v: Matrix (Fin n) (Fin 1) ℚ): Prop :=
  ∃ eig : ℚ, A*v = eig•v

def is_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ∀ q : (Matrix (Fin 1) (Fin n) ℚ), q ≠ 0 → q * mat ≠ 0

def not_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ¬is_full_rank mat



def toMat {n: ℕ} (B : List (Matrix (Fin n) (Fin 1) ℚ)) (m : ℕ):
Matrix (Fin n) (Fin m) ℚ :=
  Matrix.of (λ (i:Fin n) (j:Fin m) => B[j]! i 0)


def exp_mat  (A : (Matrix (Fin n) (Fin n) ℚ)) (i : ℕ) : (Matrix (Fin n) (Fin n) ℚ) :=
  if i = 0 then 1 else if i = 1 then A else A * exp_mat A (i-1)


def find_ctrb (A : (Matrix (Fin n) (Fin n) ℚ)) (B : (Matrix (Fin n) (Fin 1) ℚ)) (ctrb : List ( Matrix (Fin n) (Fin 1) ℚ) := List.nil) (i : ℕ := n):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(exp_mat A (i-1))*B]


def my_A : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -6, -5]
def my_B : Matrix (Fin 2) (Fin 1) ℚ := !![0; 1]

#eval toMat (find_ctrb my_A my_B) 2

def idMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => if i = j then 1 else 0)


theorem three_to_four : ∀ (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin 1) ℚ), is_full_rank (toMat (find_ctrb A B) n) → ∀ eig : ℚ, ∃ q : Matrix (Fin 1) (Fin n) ℚ, q ≠ 0 → is_eig_val A eig → q*(join_col (A-eig•(idMat n)) B) = 0 := sorry
