/- Here's a comment -/


import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

/- Now we open a namespace -/

open Matrix

abbrev n_mat (n:ℕ) := Matrix (Fin n) (Fin n) ℚ
abbrev n_vec (n:ℕ) := Matrix (Fin n) (Fin 1) ℚ


def is_eig_val (A : n_mat n) (eig: ℚ): Prop :=
  ∃ v : n_vec n, A*v = eig•v

def is_eig_vec (A : n_mat n) (v: n_vec n): Prop :=
  ∃ eig : ℚ, A*v = eig•v

def is_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ∀ q : (Matrix (Fin 1) (Fin n) ℚ), q ≠ 0 → q * mat ≠ 0

def not_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ¬is_full_rank mat

def toMat {n: ℕ} (B : List (n_vec n)) (m : ℕ):
Matrix (Fin n) (Fin m) ℚ :=
  Matrix.of (λ (i:Fin n) (j:Fin m) => B[j]! i 0)

def join_col (M : Matrix (Fin n) (Fin n) α) (V : Matrix (Fin n) (Fin 1) α) : Matrix (Fin n) (Fin (n+1)) α:=
  Matrix.of (λ i j =>
    if h: (j.val < n) then
      let k : Fin n := ⟨j.val, h⟩
      M i k
    else V i 0)

def exp_mat  (A : (n_mat n)) (i : ℕ) : (n_mat n) :=
  if i = 0 then 1 else if i = 1 then A else A * exp_mat A (i-1)

def idMat (n : ℕ) : n_mat n :=
  Matrix.of (fun i j => if i = j then 1 else 0)

def find_ctrb (A : (n_mat n)) (B : (n_vec n)) (ctrb : List ( n_vec n) := List.nil) (i : ℕ := n):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(exp_mat A (i-1))*B]

def is_similar_mat (A : n_mat n) (A' : n_mat n) : Prop :=
  ∃ (P: n_mat n), P.det ≠ 0 ∧ A' = P*A*P⁻¹

def is_similar_vec (B : n_vec n) (B' : n_vec n) : Prop :=
  ∃ (P: n_mat n), P.det ≠ 0 ∧ B = P * B'

def ABe (A : n_mat n) (B : n_vec n) (e : ℚ) :=
  join_col (A-e•(idMat n)) B

def six_two (A : n_mat n) (B : n_vec n) : Prop :=
  ∀ (e : ℚ) (e' : ℚ) (A' : n_mat n) (B' : n_vec n),
  (is_eig_val A e ∧ is_eig_val A' e' ∧ is_similar_mat A A' ∧ is_similar_vec B B') →
  (not_full_rank (toMat (find_ctrb A' B') (n+1)) → not_full_rank (toMat (find_ctrb A B) (n+1)))


theorem three_to_four : ∀ (A : n_mat n) (B : n_vec n), is_full_rank (toMat (find_ctrb A B) n) → ∀ e : ℚ, is_eig_val A e → is_full_rank (join_col (A-e•(idMat n)) B) := by
  intro ha hb hfr heig
  unfold is_full_rank at hfr
  intro




  sorry
