import Mathlib.Tactic
import MyProject.Libraries.LinAlgDefs
import MyProject.Libraries.BlockMatLib


-- Constructs the controllability matrix
-- [B AB (A^2)B ... A^(n-1)B]
@[simp]
noncomputable
def ctrbMat {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
: Mat n n :=
  λ i j => (A^j.val*B) i 0

-- Constructs the controllability matrix with a row vector q inside
-- [qB qAB q(A^2)B ... qA^(n-1)B]
@[simp]
noncomputable
def qCtrbMat {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
: Mat 1 n :=
  λ i j => (q*(A^j.val*B)) i 0

-- Proves the distributive property multiplying q by the controllability matrix
-- q*[B AB (A^2)B ... A^(n-1)B] = [qB qAB q(A^2)B ... qA^(n-1)B]
@[simp]
theorem ctrbMatEq {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
: q*(ctrbMat A B) = qCtrbMat A B q := by
  exact rfl

-- Constructs the matrix [(A-λI) B]
@[simp]
def ABe {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(e : α) :=
  ofBlocks (A-e•(1 : Mat n n)) B

-- Proves that the first n columns of [(A-λI) B] are equivalent to A-λI
@[simp]
theorem ABeLeft {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(e : α)
: getBlock (ABe A B e) 0 n (by simp) = A-e•(1 : Mat n n) := by
  ext i j
  simp[getBlock,ABe,ofBlocks]

-- Proves that the last column of [(A-λI) B] is equivalent to B
@[simp]
theorem ABeRight {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(e : α)
: getBlock (ABe A B e) n 1 (by simp) = B := by
  ext i j
  have : j = 0 := by exact Fin.fin_one_eq_zero j
  simp[getBlock,ABe,ofBlocks,this]

--
@[simp]
theorem getBlockEquiv {n : ℕ}
(A : Mat n m)
(B : Mat n m)
(a l: ℕ)
(h: a + l ≤ m)
: A = B → getBlock A a l h = getBlock B a l h := by
  intro hAB
  exact congrFun (congrFun (congrFun (congrArg getBlock hAB) a) l) h

-- Proves that any matrix constructed from consecutive
-- columns of a zero matrix will also be a zero matrix
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

-- Proves that q[(A-λI) B] = 0 implies that qb = 0
@[simp]
theorem ABeRightZero {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
(e : α)
: q * (ABe A B e) = 0 → q*B = 0 := by
  intro hq
  -- Prove that the last column of q[(A-λI) B] is equal to 0
  have hqb : getBlock (q*(ABe A B e)) n 1 (by simp) = 0 := by
    exact getBlockEquiv (q * ABe A B e) 0 n 1 (le_refl (n + 1)) hq
  -- Prove that q can be moved to the inside so that the last column
  -- of q[(A-λI) B] is equal to the last column of [q(a-λI) qb]
  have hgb : getBlock (q*(ABe A B e)) n 1 (by simp) = q * getBlock (ABe A B e) n 1 (by simp) := by rfl
  rw [hgb] at hqb
  rw [ABeRight] at hqb
  exact hqb

-- Proves that q[(A-λI) B] = 0 implies that qA = qλI
@[simp]
theorem ABeLeftZero {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
(q : Mat 1 n)
(e : α)
: q * (ABe A B e) = 0 → q*A = q*e•(1 : Mat n n) := by
  intro hq
  have hqA : getBlock (q*(ABe A B e)) 0 n (by simp) = 0 := by
    exact getBlockEquiv (q * ABe A B e) 0 0 n (by simp) hq
  have hgb : getBlock (q*(ABe A B e)) 0 n (by simp) = q * getBlock (ABe A B e) 0 n (by simp) := by rfl
  rw [hgb] at hqA
  rw [ABeLeft] at hqA
  obtain hqAe : q * (A - e • 1) = q*A - q*e•(1 : Mat n n) := by
    exact Matrix.mul_sub q A (e • 1)
  rw [hqAe] at hqA
  obtain thing : q*A - q*e•(1 : Mat n n) + q*e•(1 : Mat n n) = 0 + q*e•(1 : Mat n n):= by
    exact congrFun (congrArg HAdd.hAdd hqA) (q * e • 1)
  simp at thing
  simp
  exact thing
