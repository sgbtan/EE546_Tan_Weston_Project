import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-
Project: Proving controllability rank condition

Textbook: Linear Systems Theory and Design, Chen, Chi-Tsong

Goals:
  - Encode the meaning of controllability in  lean:
  Definition 6.1
    The pair (A, B) is said to be controllable
    if for any initial state x(O) = Xo and any final state Xl, there exists an input
    that transfers Xo to Xl in a finite time. Otherwise (6.1) or (A,B) is said to be
    uncontrollable.
  - Get from the definition of controllability to the controllability matrix, C = [B A*B A^2*B ... A^(n-1)*B]
    -Go between each of the equivilent statements in theorem 6.1 of the textbook
      -Will require going between linear algebra and differential equations

  - Steps:
    - Understand linear algebra in lean
      - In particular for eigenvalue, do we need the definition or will we need to encode computation of it
    - Understand Differential equations in lean, to what extent are they already implemented
    - Encode each of the statements in theorem 6.1
    - Prove that the steps are equivilent

    For next week
    - First pass at encoding Definition 6.1 in lean
    - Attempt to encode the definition of the contrallability matrix in lean
    - Gain better understanding of existing linear algebra, calculus and differential equations in lean

-/

/-
The following statements are equivalent.
1. The n-dimensional pair (A,B) is controllable.

2. The n x n matrix

          W_c(t) = \[ \int_{t}^{τ=0} e^(Aτ)BB' e^(A'τ) \,dτ \]
                  = \[ \int_{t}^{τ=0} e^(A(t-τ))BB' e^(A'(t-τ)) \,dτ \]

    is nonsingular for any t > O.

3. The n x np controllability matrix

          C = [B AB A^2B ... A^(n-1)B]

    has rank n (full row rank).

4. The n x (n +p) matrix [A - λI B] has full row rank at every eigenvalue, λ, of A.

5. If, in addition, all eigenvalues of A have negative real parts, then the unique solution of

          AW_c+W_cA'=-BB'

is positive definite. The solution is called the controllability Gramian and can be expressed as

          W_c(t) = \[ \int_{∞}^{0} e^(Aτ)BB' e^(A'τ) \,dτ \]
-/

/-
We want to show that (3) ↔ (4).

Proof:

Assuming C has full row rank, then the matrix [A - λI B] has full row rank at every eigenvalue of A. If not, there exists an eigenvalue λ₁ and a (1 x n) vector
q ≠ 0 such that

          q[A-λ₁I B]=O

which implies qA = λ₁q and qB = 0. Thus q is a left eigenvector of A. We compute

          qA^2 = q(A)A = (λ₁q)A = λ₁^2q

Proceeding forward, we have qA^k = λ₁^kq.

Applying Cayley-Hamilton Theorem and relating this to controllability matrix, C, we have

          q[B AB ... A^(n-1)B] = [qB λ₁qB ... λ₁^(n-1)qB] = 0

This contradicts the hypothesis that C has full row rank.

-/

def Vect (n:ℕ) := (Fin n) → ℂ

def Mat (m n: ℕ) := (Fin m) → (Fin n) → ℂ

def R22 := Mat 2 2

namespace R22

def zero : R22 := !![0,0;0,0]

def one : R22 := !![1,0;0,1]

-- def det (A : R22) : ℂ := (A 0 0)*(A 1 1)-(A 0 1)*(A 1 0)

def smul {m n: ℕ} (a:ℂ) (M: Mat m n) := λ i j => a * (M i j)

noncomputable
def mul {m n p:ℕ} (A : Mat m n) (B: Mat n p) : Mat m p :=
  λ i j => ∑ k : (Fin n), (A i k) * (B k j)

def A : Mat 2 2 := !![0,1;-6,-5]
def B: Mat 2 1 := !![0;1]

example : mul A B = !![1;-5] := by
  funext i j
  simp[mul]
  simp[A]
  simp[B]

open Matrix

def is_full_rank {m n : ℕ} (A: Matrix (Fin m) (Fin n) ℝ) : Prop := rank A = min m n

def C : Matrix (Fin 2) (Fin 2) Real  := !![0, 1; 1, -5]

def sq_full_rank_det {m : Nat} (A: Matrix (Fin m) (Fin m) Real) : Prop := A.det ≠ 0

#eval C.det

example : sq_full_rank_det C := by
  intro h



/-
Encode the meaning of controllability in  lean:
  Definition 6.1
    The pair (A, B) is said to be controllable
    if for any initial state x(O) = Xo and any final state Xl, there exists an input
    that transfers Xo to Xl in a finite time. Otherwise (6.1) or (A,B) is said to be
    uncontrollable.
-/

variable (n : Nat)
variable (k : Nat)
variable (A : Matrix (Fin n) (Fin n) ℝ)
variable (B : Matrix (Fin n) (Fin n) ℝ)
variable (x : ℕ → Matrix (Fin n) (Fin 1) ℝ)
variable (u : ℕ → Matrix (Fin n) (Fin 1) ℝ)

def dss := x (k+1) = A*(x k) + B*(u k)
def x0 : Matrix (Fin n) (Fin 1) ℝ := x 0
def xk : Matrix (Fin n) (Fin 1) ℝ := x k
def nvector : Type := Matrix (Fin n) (Fin 1) ℝ
def (dss_sol : x0 → dss → u → xk)

theorem definition_6_1 : ∀ x0, ∀ xk, ∃ u,
