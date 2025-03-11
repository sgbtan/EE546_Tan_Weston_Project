import Mathlib.Tactic
import MyProject
import Mathlib.Data.Matrix.Basic


theorem three_to_four :
∀ (A : Mat n n) (B : Mat n 1),
is_full_rank (ctrbMat A B) →
∀ (e : α), is_eig_val A e →
is_full_rank (ABe A B e) := by
  unfold is_full_rank
  intro A B hq e hev q qNZ
  have ctrbFR := hq q qNZ
  --unfold ctrbMat listToMat at ctrbFR
  unfold ABe
  by_contra ABeFR
  have qBZ : q*B=0 := by
    sorry
  have qAe : q*A=e•q := by
    --apply distrib_ofBlocks q A B
    sorry
  have qAek : ∀ (k : ℕ), q*(A^k)=(e^k)•q := by
    intro k
    induction k with
    | zero => simp
    | succ k' ih =>
      sorry
  obtain ctrbNFR : q*ctrbMat A B = 0 := by
    -- unfold ctrbMat listToMat
    -- ext i j
    -- rcases i
    -- rcases j
    -- rename_i i hi j ji
    induction n with
    | zero => unfold ctrbMat listToMat; sorry
    | succ n' ih =>
      sorry
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
