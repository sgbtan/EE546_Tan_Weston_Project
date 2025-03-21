import Mathlib.Tactic
import MyProject
import MyProject.Proofs.three_to_four_lemmas

-- Proof for the forward direction of steps 3 and 4 in theorem 6.1 of Linear System Theory and Design by Chen
theorem three_to_four :
∀ (A : Mat n n) (B : Mat n 1),
is_full_rank (ctrbMat A B) →
∀ (e : α), is_eig_val A e →
is_full_rank (ABe A B e) := by
  -- Setting up the proof by contradiction
  unfold is_full_rank
  intro A B hq e _ q qNZ
  have ctrbFR := hq q qNZ -- ctrbFR : q[B AB ... A^(n-1)B] ≠ 0
  by_contra ABeNFR        -- ABeNFR : q[A-λI B] = 0

  -- Prove that qB=0 and qA=λq
  have qBZ : q*B=0 := by exact (ABeRightZero A B q e) ABeNFR
  have qAe : q*A=e•q := by simp [(ABeLeftZero A B q e) ABeNFR]

  -- Prove that q(A^k)=(λ^k)•q and q[B AB ... A^(n-1)B] = 0
  have qAek : ∀ (k : ℕ), q*(A^k)=(e^k)•q := by exact hqAek A q e qAe
  have ctrbNFR : q*ctrbMat A B = 0 := by exact hctrbNFR A B q e qBZ qAek

  -- Use the contradiction between ctrbFR and ctrbNFR to prove False
  exact ctrbFR ctrbNFR


-- Proof for the backwards direction of steps 3 and 4 in theorem 6.1 of Linear System Theory and Design by Chen
theorem four_to_three :
∀ (A : Mat n n) (B : Mat n 1) (e : α),
is_eig_val A e →
is_full_rank (ABe A B e) →
is_full_rank (ctrbMat A B) := by
  sorry


-- Proof for the equivalence of steps 3 and 4 in theorem 6.1 of Linear System Theory and Design by Chen
theorem three_iff_four :
∀ (A : Mat n n) (B : Mat n 1) (e : ℚ),
(is_eig_val A e) →
((is_full_rank (ctrbMat A B) ↔ is_full_rank (ABe A B e))) := by
  intro A B e he
  constructor
  . sorry
  . sorry
