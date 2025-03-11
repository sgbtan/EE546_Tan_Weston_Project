import Mathlib.Tactic
import MyProject


theorem three_to_four :
∀ (A : Mat n n) (B : Mat n 1),
is_full_rank (ctrbMat A B) →
∀ (e : α), is_eig_val A e →
is_full_rank (ABe A B e) := by
  unfold is_full_rank
  intro A B hq e hev q qnz
  have ctrbFR := hq q qnz
  unfold ctrbMat listToMat at ctrbFR
  unfold ABe
  by_contra ABeFR
  have qBz : q*B=0 := by
    sorry
  have qAe : q*A=e•q := by
    --apply distrib_ofBlocks q A B
    sorry
  have qAek : q*(A^n)=(e^n)•q := by
    sorry









  sorry



theorem three_iff_four :
∀ (A : Mat n n) (B : Mat n 1) (e : ℚ),
(is_eig_val A e) →
((is_full_rank (ctrbMat A B) ↔ is_full_rank (ABe A B e))) := by
  intro A B e he
  constructor
  .
    sorry
  . sorry
