import Mathlib.Tactic

-- Set type of elements in matrices
abbrev α : Type := ℂ

-- Abbreviations for common matrix and vector types
abbrev Mat (n m:ℕ) := Matrix (Fin n) (Fin m) α

-- Definitions for left eigenvalues and left eigenvectors
@[simp]
def is_eig_val {n : ℕ}
(A : Mat n n)
(eig: α)
: Prop :=
  ∃ v : Mat 1 n, v*A = eig•v

@[simp]
def is_eig_vec {n : ℕ}
(A : Mat n n)
(v: Mat 1 n)
: Prop :=
  ∃ eig : α, v*A = eig•v


-- Definitions for full rank and not full rank
@[simp]
def is_full_rank {n m: ℕ}
(mat : Mat n m)
: Prop :=
  ∀ q : (Mat 1 n), q ≠ 0 → q * mat ≠ 0

@[simp]
def not_full_rank {n m: ℕ}
(mat : Mat n m)
: Prop :=
  ¬is_full_rank mat


-- Definition for matrix similarity
@[simp]
def is_similar_mat {n : ℕ}
(A : Mat n n)
(A' : Mat n n)
: Prop :=
  ∃ (P: Mat n n), P.det ≠ 0 ∧ A' = P*A*P⁻¹

-- Definition for vector similarity
@[simp]
def is_similar_vec {n : ℕ}
(B : Mat n n)
(B' : Mat n n)
: Prop :=
  ∃ (P: Mat n n), P.det ≠ 0 ∧ B = P * B'

-- Defnition for matrix associativity
-- This definition uses the existing defnition in mathlib but adds it to the simplifier in a format that is convenient
@[simp]
theorem assocMat {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
: q*(A*B) = (q*A)*B := by
  exact Eq.symm (Matrix.mul_assoc q A B)
