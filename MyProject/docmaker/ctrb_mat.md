
<center><h1>Controllability Rank Condition</h1></center>
<center><h2>EE 546 : Knowledge Representation and Reasoning</h2></center>

<center>
Department of Mechanical Engineering<br />
Unviersity of Washington<br />
Sam Weston & Boon Seng Tan<br />
Winter 2025
</center>
<br />


 # Introduction

Consider the n-dimensional p-input state equation
$$
\dot{x}(t) = Ax(t) + Bu(t).
$$

where A and B are, respectively, $n \times n$ and $n \times p$ real constant matrices. $A$ represents the state matrix which describes how the current state of a system affects its future state, while $B$ represents the input matrix which defines how external inputs influence the state of the system.

The state equation or the pair ($A$, $B$) is said to be controllable if for any initial state $x(0) = x_0$ and any final state $x_1$ there exists an input that transfers $x_0$ to $x_1$ in a finite time. If not, ($A$, $B$) is said to be uncontrollable.

The following statements are equivalent:
- The $n$-dimensional pair (A,B) is controllable.
- The $n \times n$ matrix

$$
W_c(t) = \int_{0}^{t} e^{A\tau} B B' e^{A'\tau} \,d\tau = \int_{0}^{t} e^{A(t-\tau)} B B' e^{A'(t-\tau)} \,d\tau
$$

is nonsingular for any $t > 0$.
- The $n \times np$ controllability matrix

$$
C = \begin{bmatrix}
B & AB & A^2B & \cdots & A^{n-1}B
\end{bmatrix}
$$

has rank $n$ (full row rank).
- The $n \times (n+p)$ matrix $[A - \lambda I \quad B]$ has full row rank at every eigenvalue, $\lambda$, of $A$.
- If, in addition, all eigenvalues of A have negative real parts, then the unique solution of

$$
AW_c + W_cA' = -BB'
$$

is positive definite. The solution is called the controllability Gramian and can be expressed as

$$
W_c(t) = \int_{0}^{\infty} e^{A\tau} B B' e^{A'\tau} \,d\tau
$$

In this project, we aim to prove the equivalence of $3 \iff 4$. Chen describes the equivalence as follows.

Assuming $C$ has full row rank, matrix $[A - \lambda I \quad B]$ has full row rank at every eigenvalue, $\lambda$, of $A$.

If matrix $[A - \lambda I \quad B]$ does not have full row rank at every eigenvalue, $\lambda$, of $A$, then $\exists \lambda_1$ and a $1 \times n$ vector $q \neq 0$ such that

$$
q [A - \lambda_1 I \quad B] = 0
$$

which implies $qA = \lambda_1q$ and $qB = 0$. Thus $q$ is a left eigenvector of $A$. We compute

$$
qA^2 = (qA)A = (\lambda_1q)A = \lambda_1^2q
$$

Proceeding forward, we have $qA^k = \lambda_1^kq$. Thus we have

$$
q [B \quad AB \quad ... \quad A^{n-1}B] = [qB \quad \lambda_1qB \quad ... \quad \lambda_1^{n-1}qB] = 0
$$

which contradicts the assumption that $C$ has full row rank.


```hs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

open Matrix
```
 # Approach
```hs
abbrev n_mat (n:ℕ) := Matrix (Fin n) (Fin n) ℚ
abbrev n_vec (n:ℕ) := Matrix (Fin n) (Fin 1) ℚ
abbrev n_r_vec (n:ℕ) := Matrix (Fin 1) (Fin n) ℚ
```
 Might be able to just use left eig val and vec 
```hs
def is_eig_val (A : n_mat n) (eig: ℚ): Prop :=
  ∃ v : n_r_vec n, v*A = eig•v

def is_eig_vec (A : n_mat n) (v: n_r_vec n): Prop :=
  ∃ eig : ℚ, v*A = eig•v

--def is_left_eig_vec


def is_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ∀ q : (Matrix (Fin 1) (Fin n) ℚ), q ≠ 0 → q * mat ≠ 0

def not_full_rank (mat : Matrix (Fin n) (Fin m) ℚ): Prop :=
  ¬is_full_rank mat


def toMat {n: ℕ} (B : List (n_vec n)) (m : ℕ):
Matrix (Fin n) (Fin m) ℚ :=
  Matrix.of (λ (i:Fin n) (j:Fin m) => B[j]! i 0)


def join_col (M : Matrix (Fin n) (Fin n) α) (V : Matrix (Fin n) (Fin 1) α) : Matrix (Fin n) (Fin (n+1)) α:=
  Matrix.of (λ i j =>
    if h: (j.val < n) then
      let k : Fin n := ⟨j.val, h⟩
      M i k
    else V i 0)


def find_ctrb (A : (n_mat n)) (B : (n_vec n)) (ctrb : List ( n_vec n) := List.nil) (i : ℕ := n):=
  if i-1 = 0 then B :: ctrb else (find_ctrb A B ctrb (i-1)) ++ [(A^(i-1))*B]

def ctrb_mat (A : (n_mat n)) (B : (n_vec n)) :=
  toMat (find_ctrb A B) n


def is_similar_mat (A : n_mat n) (A' : n_mat n) : Prop :=
  ∃ (P: n_mat n), P.det ≠ 0 ∧ A' = P*A*P⁻¹

def is_similar_vec (B : n_vec n) (B' : n_vec n) : Prop :=
  ∃ (P: n_mat n), P.det ≠ 0 ∧ B = P * B'


def ABe (A : n_mat n) (B : n_vec n) (e : ℚ) :=
  join_col (A-e•(1 : n_mat n)) B


def six_two (A : n_mat n) (B : n_vec n) : Prop :=
  ∀ (e : ℚ) (e' : ℚ) (A' : n_mat n) (B' : n_vec n),
  (is_eig_val A e ∧ is_eig_val A' e' ∧ is_similar_mat A A' ∧ is_similar_vec B B') →
  (not_full_rank (ctrb_mat A' B') → not_full_rank (ctrb_mat A B))


def six_six (A : n_mat n) (B : n_vec n): Prop :=
  ∀ (m : ℤ), (m ≥ 1 ∧ (ctrb_mat A B).rank < n-m) → ∃ (P : n_mat n), sorry


-- try with n_mat 3 or n_mat 2



theorem three_to_four_old : ∀ (A : n_mat n) (B : n_vec n) (e : ℚ),
(is_eig_val A e) → ((is_full_rank (ctrb_mat A B) ↔ is_full_rank (ABe A B e))) := by
  intro A B e h_eig
  constructor
  . intro h_ctrb
    by_contra nfr_ABe
    --have nfr_ctrb : ¬is_full_rank (ctrb_mat A B) → False := λ a => a h_ctrb
    unfold is_full_rank at nfr_ABe
    push_neg at nfr_ABe
    --unfold ABe join_col at nfr_ABe

    obtain ⟨q, hq, h⟩ := nfr_ABe
    have eig_q : is_eig_vec A q := sorry
    have qb_0 : q*B = 0 := sorry
    unfold is_full_rank at h_ctrb





    sorry
  . sorry






theorem FOL_helper : (¬p ↔ ¬q) → (p ↔ q) := by
  . intro ⟨hnpq, hnqp⟩
    constructor
    . intro hp
      by_contra hnq
      exact (hnqp hnq) hp
    . intro hq
      by_contra hnp
      exact (hnpq hnp) hq

def three_iff_four (A : n_mat n) (B : n_vec n) (e : ℚ): Prop :=
  is_full_rank (ctrb_mat A B) ↔ is_full_rank (ABe A B e)

def nthree_iff_nfour (A : n_mat n) (B : n_vec n) (e : ℚ): Prop :=
  ¬is_full_rank (ctrb_mat A B) ↔ ¬is_full_rank (ABe A B e)

theorem nthree_to_nfour :  ∀ (A : n_mat n) (B : n_vec n) (e : ℚ),
(is_eig_val A e) → nthree_iff_nfour A B e := by
  unfold nthree_iff_nfour is_full_rank
  push_neg
  intro A B e h_eig
  constructor
  .

    sorry


  .

    sorry


theorem three_to_four : ∀ (A : n_mat n) (B : n_vec n) (e : ℚ),
(is_eig_val A e) → ((is_full_rank (ctrb_mat A B) ↔ is_full_rank (ABe A B e))) := by
  intro A B e h_eig

  have reverse : nthree_iff_nfour A B e → three_iff_four A B e := by apply FOL_helper
  apply nthree_to_nfour A B e at reverse


  sorry
```
