import Mathlib.Tactic

-- Set type of elements in matrices
abbrev α : Type := ℚ

-- Abbreviations for common matrix and vector types
abbrev Mat (n m:ℕ) := Matrix (Fin n) (Fin m) α

-- Eigenvalues and eigenvectors
def is_eig_val {n : ℕ}
(A : Mat n n)
(eig: α)
: Prop :=
  ∃ v : Mat 1 n, v*A = eig•v

def is_eig_vec {n : ℕ}
(A : Mat n n)
(v: Mat 1 n)
: Prop :=
  ∃ eig : α, v*A = eig•v


-- Full rank
def is_full_rank {n m: ℕ}
(mat : Mat n m)
: Prop :=
  ∀ q : (Mat 1 n), q ≠ 0 → q * mat ≠ 0

def not_full_rank {n m: ℕ}
(mat : Mat n m)
: Prop :=
  ¬is_full_rank mat


-- Similarity
def is_similar_mat {n : ℕ}
(A : Mat n n)
(A' : Mat n n)
: Prop :=
  ∃ (P: Mat n n), P.det ≠ 0 ∧ A' = P*A*P⁻¹

def is_similar_vec {n : ℕ}
(B : Mat n n)
(B' : Mat n n)
: Prop :=
  ∃ (P: Mat n n), P.det ≠ 0 ∧ B = P * B'
