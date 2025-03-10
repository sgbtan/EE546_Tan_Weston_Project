import Mathlib.Tactic

def ofBlocks {n m p : ℕ}
(A : Matrix (Fin n) (Fin m) ℚ)
(B : Matrix (Fin n) (Fin p) ℚ)
: Matrix (Fin n) (Fin (m+p)) ℚ :=

λ i j => if h : j.val < m then
let k : Fin m := ⟨ j.val, h ⟩
A i k
else
have : j-m < p := by sorry
let k : Fin p := ⟨ j.val - m, this ⟩
B i k


def getBlock {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
(a b: ℕ) (h: a < b ∧ b < n)
: Matrix (Fin n) (Fin (b-a)) ℚ := sorry

namespace Temp

variable (A : Matrix (Fin 4) (Fin 4) ℚ)
(B : Matrix (Fin 4) (Fin 1) ℚ)
(q : Matrix (Fin 1) (Fin 4) ℚ)

#check getBlock (q*(ofBlocks A B)) 0 4 sorry
#check getBlock (q*(ofBlocks A B)) 4 5 sorry

end Temp

theorem asd {n m p : ℕ}
(q : Matrix (Fin 1) (Fin n) ℚ)
(A : Matrix (Fin n) (Fin m) ℚ)
(B : Matrix (Fin n) (Fin p) ℚ)
: q * (ofBlocks A B) = ofBlocks (q*A) (q*B) := by

ext i j
unfold ofBlocks
rcases i
rcases j
rename_i i hi j ji
by_cases hj: j < m
<;>
simp[Matrix.mul_apply]
