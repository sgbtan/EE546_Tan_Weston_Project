/-
HW 8 presentation
Assuming $C$ has full row rank, matrix $[A - \lambda I \quad B]$ has full row rank at every eigenvalue, $\lambda$, of $A$.

If matrix $[A - \lambda I \quad B]$ does not have full row rank at every eigenvalue, $\lambda$, of $A$, then $\exists \lambda_1$ and a $1 \times n$ vector $q \neq 0$ such that

$$
q [A - \lambda_1 I \quad B] = 0
$$

which implies $qA = \lambda_1q$ and $qB = 0$. Thus $q$ is a left eigenvector of $A$. We compute

$$
qA^2 = (qA)A = (\lambda_1q)A = \lambda_1^2q
$$

Proceeding forward, we have $qA^k = \lambda_1^kq$. Thus we have

$$
q [B \quad AB \quad ... \quad A^{n-1}B] = [qB \quad \lambda_1qB \quad ... \quad \lambda_1^{n-1}qB] = 0
$$

which contradicts the assumption that $C$ has full row rank.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

open Matrix



-- Type abbreviations
abbrev n_mat (n:ℕ) := Matrix (Fin n) (Fin n) ℚ
abbrev n_vec (n:ℕ) := Matrix (Fin n) (Fin 1) ℚ
abbrev n_r_vec (n:ℕ) := Matrix (Fin 1) (Fin n) ℚ

def is_eig_val (A : n_mat n) (eig: ℚ) : Prop :=
  ∃ v : n_r_vec n, v*A = eig•v
def is_eig_vec (A : n_mat n) (v: n_r_vec n) : Prop :=
  ∃ eig : ℚ, v*A = eig•v
def is_eig_vec_of_val (A : n_mat n) (eig : ℚ) (v: n_r_vec n): Prop :=
  v*A = eig•v
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











-- Functions to recursively construct the controllability matrix

def find_ctrb (A : (n_mat n)) (B : (n_vec n)) (ctrb : List ( n_vec n) := List.nil) (i : ℕ := n):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(A^(i-1))*B]

def ctrb_mat (A : (n_mat n)) (B : (n_vec n)) :=
  toMat (find_ctrb A B) n

def my_A : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -6, -5]
def my_B : Matrix (Fin 2) (Fin 1) ℚ := !![0; 1]

#eval ctrb_mat my_A my_B



-- Function to construct the ABe matrix

def ABe (A : n_mat n) (B : n_vec n) (e : ℚ) :=
  join_col (A-e•(1 : n_mat n)) B















-- Proof for 3 → 4

theorem three_to_four : ∀ (A : n_mat n) (B : n_vec n) (e : ℚ),
(is_eig_val A e) → ((is_full_rank (ctrb_mat A B) ↔ is_full_rank (ABe A B e))) := by
  intro A B e h_eig
  constructor
  . intro h_ctrb
    by_contra nfr_ABe
    unfold is_full_rank at nfr_ABe
    push_neg at nfr_ABe
    obtain ⟨q, hq, h⟩ := nfr_ABe
    have eig_q : is_eig_vec_of_val A e q:= by
      unfold is_eig_vec_of_val
      unfold ABe join_col at h
      dsimp at h
      sorry
    have qb_0 : q*B = 0 :=
      sorry
    sorry
  . sorry
