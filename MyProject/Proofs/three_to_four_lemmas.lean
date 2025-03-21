import Mathlib.Tactic
import MyProject

theorem hqAek {n : ℕ}
(A : Mat n n)
(q : Mat 1 n)
(e : α)
(qAe : q*A=e•q)
(k : ℕ)
: q*(A^k)=(e^k)•q := by
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

theorem hctrbNFR
{n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
(e : α)
(qBZ : q*B=0 )
(qAek : ∀ (k : ℕ), q*(A^k)=(e^k)•q)
: q*ctrbMat A B = 0 := by
    obtain ctrbEq : q*ctrbMat A B = qCtrbMat A B q := by rfl
    rw [ctrbEq]
    ext i j
    have := qAek j
    unfold qCtrbMat
    simp
    calc (q*A^j.val*B) i 0
      _ = ((e^j.val•q)*B) i 0 := by rw[this]
      _ = 0 := by simp[qBZ]
