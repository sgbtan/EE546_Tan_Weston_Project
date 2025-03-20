import Mathlib.Tactic
import MyProject



theorem three_to_four :
∀ (A : Mat n n) (B : Mat n 1),
is_full_rank (ctrbMat A B) →
∀ (e : α), is_eig_val A e →
is_full_rank (ABe A B e) := by
  unfold is_full_rank
  intro A B hq e hev q qNZ
  have ctrbFR := hq q qNZ
  by_contra ABeNFR
  have qBZ : q*B=0 := by exact (ABeRightZero A B q e) ABeNFR
  have qAe : q*A=e•q := by simp [(ABeLeftZero A B q e) ABeNFR]
  have qAek : ∀ (k : ℕ), q*(A^k)=(e^k)•q := by
    intro k
    induction k with
    | zero => simp
    | succ k' ih =>
      calc q*A^(k'+1)
        _ = q*(A^k'*A) := by exact rfl
        _ = q*A^k'*A   := by exact Eq.symm (Matrix.mul_assoc q (A ^ k') A)
        _ = (e^k'•q)*A := by simp[ih]
        _ = e^k'•(q*A) := by exact Matrix.smul_mul (e^k') q A
        _ = e^k'•(e•q) := by exact congrArg (HSMul.hSMul (e ^ k')) qAe
        _ = (e^k'*e)•q := by exact smul_smul (e ^ k') e q
        _ = e^(k'+1)•q := by ring_nf
  obtain ctrbEq : q*ctrbMat A B = qCtrbMat A B q := by exact rfl
  obtain ctrbNFR : q*ctrbMat A B = 0 := by
    rw [ctrbEq]
    ext i j
    have := qAek j
    unfold qCtrbMat
    simp
    calc (q*A^j.val*B) i 0
      _ = (q*(A^j.val)*B) i 0 := by exact rfl
      _ = ((q*(A^j.val))*B) i 0 := by exact rfl
      _ = ((e^j.val•q)*B) i 0 := by rw[this]
      _ = 0 := by simp[qBZ]

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
