 Here's a comment 
```hs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
```
 Now we open a namespace 
```hs
open Matrix

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

def join_col (M : Matrix (Fin n) (Fin n) α) (V : Matrix (Fin n) (Fin 1) α) : Matrix (Fin n) (Fin (n+1)) α:=
  Matrix.of (λ i j =>
    if h: (j.val < n) then
      let k : Fin n := ⟨j.val, h⟩
      M i k
    else V i 0)

def exp_mat  (A : (Matrix (Fin n) (Fin n) ℚ)) (i : ℕ) : (Matrix (Fin n) (Fin n) ℚ) :=
  if i = 0 then 1 else if i = 1 then A else A * exp_mat A (i-1)

def idMat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => if i = j then 1 else 0)

def find_ctrb (A : (Matrix (Fin n) (Fin n) ℚ)) (B : (Matrix (Fin n) (Fin 1) ℚ)) (ctrb : List ( Matrix (Fin n) (Fin 1) ℚ) := List.nil) (i : ℕ := n):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(exp_mat A (i-1))*B]

def is_similar (A : Matrix (Fin n) (Fin n) ℚ) (A' : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∃ (P: Matrix (Fin n) (Fin n) ℚ), P.det ≠ 0 ∧ A = P⁻¹ * A' * P

def ABe (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin 1) ℚ) (e : ℚ) :=
  join_col (A-e•(idMat n)) B

def 6_2 (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin 1) ℚ) : Prop :=
  ∀ (e : ℚ) (e' : ℚ) (A' : Matrix (Fin n) (Fin n) ℚ) (B' : Matrix (Fin n) (Fin 1) ℚ),
  ((is_eig_val A e ∧ is_eig_val A' e') ∧ (is_similar A A' ∧ is_similar B B')) → (not_full_rank (ABe A' B' e) → not_full_rank (ABe A B e))


theorem three_to_four : ∀ (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin 1) ℚ), is_full_rank (toMat (find_ctrb A B) n) → ∀ e : ℚ, is_eig_val A e → is_full_rank (join_col (A-e•(idMat n)) B) := by
  intro ha hb hfr heig
  unfold is_full_rank at hfr
  intro




  sorry
```
