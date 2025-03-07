import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Field.Basic


open Matrix

abbrev n_mat (n:ℕ) := Matrix (Fin n) (Fin n) ℚ
abbrev n_vec (n:ℕ) := Matrix (Fin n) (Fin 1) ℚ
abbrev n_r_vec (n:ℕ) := Matrix (Fin 1) (Fin n) ℚ


def TupMul (q : n_r_vec n) (MatVec : (n_mat n) × (n_vec n)) : (n_r_vec n) × (n_vec 1) :=
  (q*MatVec.1, q*MatVec.2)

def TupToMat (MatVec : (Matrix (Fin n) (Fin m) ℚ) × (n_vec n)) : Matrix (Fin n) (Fin (m+1)) ℚ :=
  Matrix.of (λ (i : Fin n) (j : Fin (m+1)) =>
    if h: (j.val < m) then
      let k : Fin m := ⟨j.val, h⟩
      MatVec.1 i k
    else MatVec.2 i 0)



-- Given that f is the identity function
theorem f_is_identity {α : Type} [Mul α] [OfNat α 3] (f : α → α) (h : ∀ x, f x = x) (x : α) :
  3 * f x = f (3 * x) := by
  -- Substitute f(x) = x using the hypothesis h
  rw [h x, h (3 * x)]



-- Define f(x) = 5x + 6x
def f {α : Type} [Mul α] [Add α] [OfNat α 5] [OfNat α 6] (x : α) : α := 5 * x + 6 * x

-- Simplify f(x) to 11x
theorem f_simplified {α : Type} [Semiring α] (x : α) : f x = 11 * x := by
  simp [f, mul_add, add_mul, ← mul_assoc, ← add_assoc]
  norm_num

  sorry

-- Prove 3 * f(x) = f(3x)
theorem three_f_eq_f_three_x {α : Type} [Semiring α] (x : α) : 3 * f x = f (3 * x) := by
  -- Simplify f(x) to 11x
  rw [f_simplified, f_simplified]
  -- Compute both sides
  calc
    3 * (11 * x) = 33 * x := by sorry
    _ = 11 * (3 * x) := by sorry
    _ = f (3 * x) := by rw [f_simplified]


example: ∀ (q : n_r_vec n) (MatVec : (n_mat n) × (n_vec n)),
 TupToMat (TupMul q MatVec) = (q * (TupToMat MatVec)) := by
  intro q mv
  let ttm : Matrix (Fin 1) (Fin (n+1)) ℚ := TupToMat (TupMul q mv)
  let qttm : Matrix (Fin 1) (Fin (n+1)) ℚ := q * TupToMat mv




  sorry












example: ∀ (q : n_r_vec 3) (MatVec : (n_mat 3) × (n_vec 3)),
 TupToMat (TupMul q MatVec) = 0 → (q * (TupToMat MatVec)) = 0 := by
  intro q mv htm



  sorry


def ListMul (q : n_r_vec n) (ListVec : List (n_vec n))
(out_list : List (n_vec 1) := List.nil) (i : ℕ := (ListVec.length-1)): (List (n_vec 1)) :=
  if i = 0 then out_list ++ [(q*ListVec[i]!)]
  else  ListMul q ListVec out_list (i-1) ++ [(q*ListVec[i]!)]

def ListToMat {n: ℕ} (B : List (n_vec n)) (m : ℕ := B.length):
Matrix (Fin n) (Fin m) ℚ :=
  Matrix.of (λ (i:Fin n) (j:Fin m) => B[j]! i 0)

def my_vec_lst : List (n_vec 3) := [!![1;2;3],!![1;2;4]]

def my_q : n_r_vec 3 := !![0, 1, 2]

#eval ListToMat (ListMul my_q my_vec_lst)


example: ∀ (q : n_r_vec n) (A : List (n_vec n)),
 q * (ListToMat A) = ListToMat (ListMul q A) := by

  sorry
