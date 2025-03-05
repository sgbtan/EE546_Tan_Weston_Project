import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

example : (p ↔ q) ↔ (¬q ↔ ¬p) := by
  constructor
  . intro ⟨hpq, hqp⟩
    constructor
    . intro hnq hp
      exact hnq (hpq hp)
    . intro hnp hq
      exact hnp (hqp hq)
  . intro ⟨hnqp, hnpq⟩
    constructor
    . intro hp
      by_contra hnq
      exact (hnqp hnq) hp
    . intro hq
      by_contra hnp
      exact (hnpq hnp) hq



-- Define a matrix
def myMatrix : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 2, 3;
     4, 5, 6]

-- Compute the rank of the matrix
#check myMatrix.rank = 2

example : myMatrix.rank = 2 := by
  unfold Matrix.rank
  sorry
