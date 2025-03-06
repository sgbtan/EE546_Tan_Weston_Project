/- Proof of step3 -> 4 for controllability, assuming single input -/


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
abbrev n_r_vec (n:ℕ) := Matrix (Fin 1) (Fin n) ℚ


-- Might be able to just use left eig val and vec

def is_eig_val (A : n_mat n) (eig: ℚ): Prop :=
  ∃ v : n_r_vec n, v*A = eig•v

def is_eig_vec (A : n_mat n) (v: n_r_vec n): Prop :=
  ∃ eig : ℚ, v*A = eig•v

--def is_left_eig_vec


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


def find_ctrb (A : (n_mat n)) (B : (n_vec n)) (ctrb : List ( n_vec n) := List.nil) (i : ℕ := n):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(A^(i-1))*B]

def ctrb_mat (A : (n_mat n)) (B : (n_vec n)) :=
  toMat (find_ctrb A B) n


def is_similar_mat (A : n_mat n) (A' : n_mat n) : Prop :=
  ∃ (P: n_mat n), P.det ≠ 0 ∧ A' = P*A*P⁻¹

def is_similar_vec (B : n_vec n) (B' : n_vec n) : Prop :=
  ∃ (P: n_mat n), P.det ≠ 0 ∧ B = P * B'


def ABe (A : n_mat n) (B : n_vec n) (e : ℚ) :=
  join_col (A-e•(1 : n_mat n)) B

def dist_prop (q_eig : n_r_vec n) (M : Matrix (Fin n) (Fin (n+1)) ℚ) :




def six_two (A : n_mat n) (B : n_vec n) : Prop :=
  ∀ (e : ℚ) (e' : ℚ) (A' : n_mat n) (B' : n_vec n),
  (is_eig_val A e ∧ is_eig_val A' e' ∧ is_similar_mat A A' ∧ is_similar_vec B B') →
  (not_full_rank (ctrb_mat A' B') → not_full_rank (ctrb_mat A B))


def six_six (A : n_mat n) (B : n_vec n): Prop :=
  ∀ (m : ℤ), (m ≥ 1 ∧ (ctrb_mat A B).rank < n-m) → ∃ (P : n_mat n), sorry


-- try with n_mat 3 or n_mat 2



theorem three_to_four_old : ∀ (A : n_mat n) (B : n_vec n) (e : ℚ),
(is_eig_val A e) → ((is_full_rank (ctrb_mat A B) ↔ is_full_rank (ABe A B e))) := by
  intro A B e h_eig
  constructor
  . intro h_ctrb
    by_contra nfr_ABe
    --have nfr_ctrb : ¬is_full_rank (ctrb_mat A B) → False := λ a => a h_ctrb
    unfold is_full_rank at nfr_ABe
    push_neg at nfr_ABe
    --unfold ABe join_col at nfr_ABe

    obtain ⟨q, hq, h⟩ := nfr_ABe
    have eig_q : is_eig_vec A q :=

      sorry
    have qb_0 : q*B = 0 :=

      sorry
    unfold is_full_rank at h_ctrb






    sorry
  . sorry






theorem FOL_helper : (¬p ↔ ¬q) → (p ↔ q) := by
  . intro ⟨hnpq, hnqp⟩
    constructor
    . intro hp
      by_contra hnq
      exact (hnqp hnq) hp
    . intro hq
      by_contra hnp
      exact (hnpq hnp) hq

def three_iff_four (A : n_mat n) (B : n_vec n) (e : ℚ): Prop :=
  is_full_rank (ctrb_mat A B) ↔ is_full_rank (ABe A B e)

def nthree_iff_nfour (A : n_mat n) (B : n_vec n) (e : ℚ): Prop :=
  ¬is_full_rank (ctrb_mat A B) ↔ ¬is_full_rank (ABe A B e)

theorem nthree_to_nfour :  ∀ (A : n_mat n) (B : n_vec n) (e : ℚ),
(is_eig_val A e) → nthree_iff_nfour A B e := by
  unfold nthree_iff_nfour is_full_rank
  push_neg
  intro A B e h_eig
  constructor
  .

    sorry


  .

    sorry


theorem three_to_four : ∀ (A : n_mat n) (B : n_vec n) (e : ℚ),
(is_eig_val A e) → ((is_full_rank (ctrb_mat A B) ↔ is_full_rank (ABe A B e))) := by
  intro A B e h_eig

  have reverse : nthree_iff_nfour A B e → three_iff_four A B e := by apply FOL_helper
  apply nthree_to_nfour A B e at reverse


  sorry
