import Mathlib.Tactic
import MyProject
import MyProject.Proofs.three_to_four_lemmas

theorem three_to_four :
∀ (A : Mat n n) (B : Mat n 1),
is_full_rank (ctrbMat A B) →
∀ (e : α), is_eig_val A e →
is_full_rank (ABe A B e) := by
  unfold is_full_rank
  intro A B hq e _ q qNZ
  have ctrbFR := hq q qNZ
  by_contra ABeNFR

  have qBZ : q*B=0 := by exact (ABeRightZero A B q e) ABeNFR
  have qAe : q*A=e•q := by simp [(ABeLeftZero A B q e) ABeNFR]

  have qAek : ∀ (k : ℕ), q*(A^k)=(e^k)•q := by exact hqAek A q e qAe

  obtain ctrbNFR : q*ctrbMat A B = 0 := by exact hctrbNFR A B q e qBZ qAek

  exact ctrbFR ctrbNFR

theorem four_to_three :
∀ (A : Mat n n) (B : Mat n 1) (e : α),
is_eig_val A e →
is_full_rank (ABe A B e) →
is_full_rank (ctrbMat A B) := by
  sorry

theorem three_iff_four :
∀ (A : Mat n n) (B : Mat n 1) (e : ℚ),
(is_eig_val A e) →
((is_full_rank (ctrbMat A B) ↔ is_full_rank (ABe A B e))) := by
  intro A B e he
  constructor
  . sorry
  . sorry
