import Mathlib.Tactic

-- Abbreviations for common matrix and vector types
abbrev n_mat (n:ℕ) := Matrix (Fin n) (Fin n) ℚ
abbrev n_m_vec (n m:ℕ) := Matrix (Fin n) (Fin m) ℚ
abbrev n_vec (n:ℕ) := Matrix (Fin n) (Fin 1) ℚ
abbrev n_r_vec (n:ℕ) := Matrix (Fin 1) (Fin n) ℚ


-- Eigenvalues and eigenvectors
def is_eig_val (A : n_mat n) (eig: ℚ): Prop :=
  ∃ v : n_r_vec n, v*A = eig•v
def is_eig_vec (A : n_mat n) (v: n_r_vec n): Prop :=
  ∃ eig : ℚ, v*A = eig•v


-- Full rank
def is_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ∀ q : (Matrix (Fin 1) (Fin n) ℚ), q ≠ 0 → q * mat ≠ 0
def not_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ¬is_full_rank mat


-- Similarity
def is_similar_mat (A : n_mat n) (A' : n_mat n) : Prop :=
  ∃ (P: n_mat n), P.det ≠ 0 ∧ A' = P*A*P⁻¹
def is_similar_vec (B : n_vec n) (B' : n_vec n) : Prop :=
  ∃ (P: n_mat n), P.det ≠ 0 ∧ B = P * B'
