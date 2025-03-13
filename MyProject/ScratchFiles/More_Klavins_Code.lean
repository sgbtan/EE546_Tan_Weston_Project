import Mathlib.Tactic
import MyProject


def ctrb {n : ℕ}
(A : Matrix (Fin n) (Fin n) ℚ)
(B : Matrix (Fin n) (Fin 1) ℚ)
: Matrix (Fin n) (Fin n) ℚ :=
  λ i j => (A^j.val*B) i 0




example {n : ℕ}
(hn : n > 1)
(A : Matrix (Fin n) (Fin n) ℚ)
(B : Matrix (Fin n) (Fin 1) ℚ)
: getBlock (ctrb A B) 0 1 ⟨ by decide, by exact hn ⟩ = B := by
  ext i j
  simp[getBlock,ctrb]
  have hj : j = 0 := by
    exact eq_zero_of_zero_eq_one rfl j
  rw[hj]

theorem asd {j : ℕ} : Fin (j + 1 - j) = Fin 1 := by
  simp

instance {j:ℕ} : Coe (Fin 1) (Fin (j + 1 - j)) :=
  ⟨ λ x => by
  have : j + 1 - j = 1 := by exact Nat.add_sub_self_left j 1
  rw[this]
  exact x
  ⟩

instance {n j:ℕ} : CoeSort (Matrix (Fin n) (Fin (j + 1 - j)) ℚ) (Matrix (Fin n) (Fin 1) ℚ) :=
  ⟨ λ M => λ i j => M i j ⟩

@[simp]
theorem column_meaning
{n m: ℕ}
(hn : n > 1)
(hm : m + 1 < n)
(A : Matrix (Fin n) (Fin n) ℚ)
(B : Matrix (Fin n) (Fin 1) ℚ)
: getBlock (ctrb A B) m (m+1) ⟨ by simp, hm ⟩ = ↑(A^m)*B := by
  ext i j
  rcases i
  rcases j
  rename_i i hi j hj
  unfold getBlock
  simp[ctrb]
  apply?

  sorry
