import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs
import MyProject.Libraries.BlockMatLib


-- Takes in a matrix A and vector B and constructs the contralability matrix
@[simp]
noncomputable
def ctrbMat {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
: Mat n n :=
  λ i j => (A^j.val*B) i 0

@[simp]
noncomputable
def qCtrbMat {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
: Mat 1 n :=
  λ i j => (q*(A^j.val*B)) i 0

@[simp]
theorem ctrbMatEq {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
: q*(ctrbMat A B) = qCtrbMat A B q := by
  exact rfl


@[simp]
theorem ctrb_cols
{n m: ℕ}
(hm : m < n)
(A : Mat n n)
(B : Mat n 1)
: (getBlock (ctrbMat A B) m 1 (by exact hm)) = (A^m)*B := by
  ext i j
  rcases i
  rcases j
  rename_i i hi j hj
  rw[getBlock,ctrbMat]
  have : j = 0 := by exact Nat.lt_one_iff.mp hj
  simp[this]


-- Constructs the matrix [(A-λI) B]
@[simp]
def ABe {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(e : α) :=
  ofBlocks (A-e•(1 : Mat n n)) B

@[simp]
theorem ABeLeft {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(e : α)
: getBlock (ABe A B e) 0 n (by simp) = A-e•(1 : Mat n n) := by
  ext i j
  simp[getBlock,ABe,ofBlocks]

@[simp]
theorem ABeRight {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(e : α)
: getBlock (ABe A B e) n 1 (by simp) = B := by
  ext i j
  have : j = 0 := by exact Fin.fin_one_eq_zero j
  simp[getBlock,ABe,ofBlocks,this]

@[simp]
theorem getBlockEquiv {n : ℕ}
(A : Mat n m)
(B : Mat n m)
(a l: ℕ)
(h: a + l ≤ m)
: A = B → getBlock A a l h = getBlock B a l h := by
  intro hAB
  exact congrFun (congrFun (congrFun (congrArg getBlock hAB) a) l) h

@[simp]
theorem getBlockZero {n : ℕ}
(A : Mat n m)
(a l: ℕ)
(h: a + l ≤ m)
: A = 0 → getBlock A a l h = 0 := by
  intro hA
  unfold getBlock
  ext i j
  simp [hA]


@[simp]
theorem ABeRightZero {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
(e : α)
: q * (ABe A B e) = 0 → q*B = 0 := by
  intro hq
  have fig : getBlock (q*(ABe A B e)) n 1 (by simp) = 0 := by
    exact getBlockEquiv (q * ABe A B e) 0 n 1 (le_refl (n + 1)) hq
  have mocha : getBlock (q*(ABe A B e)) n 1 (by simp) = q * getBlock (ABe A B e) n 1 (by simp) := by rfl
  rw [mocha] at fig
  rw [ABeRight] at fig
  exact fig


@[simp]
theorem ABeLeftZero {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
(e : α)
: q * (ABe A B e) = 0 → q*A = q*e•(1 : Mat n n) := by
  intro hq
  have fig : getBlock (q*(ABe A B e)) 0 n (by simp) = 0 := by
    exact getBlockEquiv (q * ABe A B e) 0 0 n (by simp) hq
  have mocha : getBlock (q*(ABe A B e)) 0 n (by simp) = q * getBlock (ABe A B e) 0 n (by simp) := by rfl
  rw [mocha] at fig
  rw [ABeLeft] at fig
  obtain puggle : q * (A - e • 1) = q*A - q*e•(1 : Mat n n) := by
    exact Matrix.mul_sub q A (e • 1)

  rw [puggle] at fig
  obtain thing : q*A - q*e•(1 : Mat n n) + q*e•(1 : Mat n n) = 0 + q*e•(1 : Mat n n):= by
    exact congrFun (congrArg HAdd.hAdd fig) (q * e • 1)
  simp at thing
  simp
  exact thing

@[simp]
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

@[simp]
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
