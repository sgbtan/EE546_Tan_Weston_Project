

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

Consider the $n$-dimensional $p$-input state equation
$$
\dot{x}(t) = Ax(t) + Bu(t).
$$

where A and B are, respectively, $n \times n$ and $n \times p$ real constant matrices. $A$ represents the state matrix which describes how the current state of a system affects its future state, while $B$ represents the input matrix which defines how external inputs influence the state of the system.

The state equation can be used to derive the controllability matrix by performing repeated back-substitution as the state progresses from $x(0)$ at initial time to $x(n)$. This results in a linear combination of the columns of $B$, $AB$, . . . , $A^{n-1}B$, i.e, the controllability matrix, $C$.

$$
x_n = C \cdot \begin{bmatrix}
u_{n-1} \\ u_{n-2} \\ \vdots \\ u_0
\end{bmatrix}
$$

The state equation or the pair ($A$, $B$) is said to be controllable if for any initial state $x(0) = x_0$ and any final state $x_1$ there exists an input that transfers $x_0$ to $x_1$ in a finite time. If not, ($A$, $B$) is said to be uncontrollable.

In this project, we aim show the equivalence of the following in Lean 4:

- The $n \times np$ controllability matrix $C$ has rank $n$ (full row rank)

$$
C = \begin{bmatrix}
B & AB & A^2B & \cdots & A^{n-1}B
\end{bmatrix}
$$

- The $n \times (n+p)$ matrix $[A - \lambda I \quad B]$ has full row rank at every eigenvalue, $\lambda$, of $A$.

To acheive this, we created three libraries:
- LinAlgDefs which predicate linear algebra definitions.
- BlockMatLib which contain methods of creating and decomposing matrices out of smaller matrices and helpers for basic operations.
- ControlLib which contains methods of constructing the controllability matrix as well as the $[A - \lambda I \quad B]$ matrix above.

For simplicity, we are assuming only one control input meaning that $B$ will be an $n \times 1$ vector, controllability matrix $C$ will be an $n \times n$ matrix, and $[A - \lambda I \quad B]$ will be $n \times n$.


## Resources

The theorems and proofs used in throughout this project are drawn from Chapter 6 of Linear System Theory and Design by Chi-Tsong Chen.


# Proving equivalence

Proof of equivalence in the forward direction as described in the text is as follows.

Assuming $C$ has full row rank, matrix $[A - \lambda I \quad B]$ has full row rank at every eigenvalue, $\lambda$, of $A$.

If matrix $[A - \lambda I \quad B]$ does not have full row rank at every eigenvalue, $\lambda$, of $A$, then $\exists \lambda_1$ and a $1 \times n$ vector $q \neq 0$ such that

$$
q [A - \lambda_1 I \quad B] = 0
$$

which implies $qA = \lambda_1q$ and $qB = 0$.

Thus $q$ is a left eigenvector of $A$. We compute

$$
qA^2 = (qA)A = (\lambda_1q)A = \lambda_1^2q
$$

Proceeding forward, we have $qA^k = \lambda_1^kq$. Thus we have

$$
q [B \quad AB \quad ... \quad A^{n-1}B] = [qB \quad \lambda_1qB \quad ... \quad \lambda_1^{n-1}qB] = 0
$$

which contradicts the assumption that $C$ has full row rank.

## In Lean 4

Assuming $C$ has full row rank, matrix $[A - \lambda I \quad B]$ has full row rank at every eigenvalue, $\lambda$, of $A$.

```hs
theorem three_to_four : ∀ (A : Mat n n) (B : Mat n 1), is_full_rank (ctrbMat A B) → ∀ (e : α), is_eig_val A e → is_full_rank (ABe A B e) := by
  sorry
```

We will require the libraries we created to define `Mat`, `is_full_rank`, and `is_eig_val`.

 ### LinAlgDefs

We work mainly with matrices. Fortunately, the Matrix type is already defined in Mathlib in the Mathlib.Data.Matrix library. We use it by calling it as such.

```hs
Matrix (Fin n) (Fin m) ℚ
```
However, since we repeatedly call this definition, to simplify this syntax we abbreviate this as

```hs
abbrev α : Type := ℚ

abbrev Mat (n m:ℕ) := Matrix (Fin n) (Fin m) α
```
so when we create a matrix, we do so by calling `Mat n m` where `n` and `m` define the size of the matrix. 

### `is_eig_val` and `is_eig_vec`
We first needed some way to declare given a matrix and a scalar, whether that scalar is an eigenvalue of the matrix. Similarly given a matrix and a vector, whether that vector is an eigenvector of the matrix. `is_eig_val` and `is_eig_vec` helps us achieve this.

```hs
def is_eig_val {n : ℕ} (A : Mat n n) (eig: α) : Prop :=
  ∃ v : Mat 1 n, v*A = eig•v

def is_eig_vec {n : ℕ} (A : Mat n n) (v: Mat 1 n) : Prop :=
  ∃ eig : α, v*A = eig•v
```

### Example
```hs
def I : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]
def e_val_I : ℚ := 1

example : is_eig_val I e_val_I := by
  simp[is_eig_val, e_val_I]
  use e_vec_I
  simp[e_vec_I, I]

example : is_eig_vec I e_vec_I := by
  simp[is_eig_vec, e_vec_I]
  use e_val_I
  simp[e_val_I, I]
```

### `is_full_rank` & `not_full_rank`
We also needed to be able to declare if a matrix is full rank or not.

```hs
def is_full_rank {n m: ℕ} (mat : Mat n m) : Prop :=
  ∀ q : (Mat 1 n), q ≠ 0 → q * mat ≠ 0

def not_full_rank {n m: ℕ} (mat : Mat n m) : Prop :=
  ¬is_full_rank mat
```
### Example
```hs
def mat : Matrix (Fin 3) (Fin 3) ℚ := ![![1, 1, 1], ![2 ,2 ,2], ![ 3, 3, 3]]

open Matrix
example : not_full_rank mat := by
  unfold not_full_rank is_full_rank
  push_neg
  let r : Matrix (Fin 1) (Fin 3) ℚ := !![-2, 1, 0]
  use r
  constructor
  . trivial
  . funext i j
    simp[r, vecMul, mat]
    fin_cases i <;> fin_cases j <;> dsimp <;> simp
```
<br>
If matrix $[A - \lambda I \quad B]$ does not have full row rank at every eigenvalue, $\lambda$, of $A$, then $\exists \lambda_1$ and a $1 \times n$ vector $q \neq 0$ such that

$$
q [A - \lambda_1 I \quad B] = 0
$$

which implies $qA = \lambda_1q$ and $qB = 0$.


### BlockMatLib

### `ofBlocks` and ` getBlocks`
Next we needed to be able to form a new matrix out of smaller matrices and a way to slice a matrix by columns to form a new matrix out of those columns.

Since we could not find existing methods within Matlib to do this, we created `ofBlocks` and ` getBlocks`. This allows us to form two proofs:
- Proof that $q \cdot [A \quad B] = [q \cdot A \quad q \cdot B]$ where $q$ is row vector and $A$ and $B$ are matrices or column vectors.

```hs
theorem distrib_ofBlocks {n m p : ℕ} (q : Mat 1 n) (A : Mat n m) (B : Mat n p) : 
q * (ofBlocks A B) = ofBlocks (q*A) (q*B) := by
  ext i j
  rcases i
  rcases j
  rename_i i hi j ji
  unfold ofBlocks
  by_cases hj: j < m 
  <;>
  simp[Matrix.mul_apply]
```
- Proof that block $B$ of $q \cdot [A \quad B \quad C]$ is equal to $q \cdot B$.

```hs
theorem distrib_getBlock {n m: ℕ} (q : Mat 1 n) (A : Mat n m) (a b : ℕ) (h: a ≤ b ∧ b < m) : q * (getBlock A a b h) = getBlock (q*A) a b h := by
  ext i j
  rcases i
  rcases j
  rename_i i hi j ji
  unfold getBlock
  simp[Matrix.mul_apply]
```
### ControlLib

We define the method of constructing the controllability matrix, $C$, which takes the $A$ and $B$ matrices as inputs.

```hs
def ctrbMat {n : ℕ}
(A : Mat n n)
(B : Mat n 1)
: Matrix (Fin n) (Fin n) ℚ :=
  λ i j => (A^j.val*B) i 0
```
### Example

Applying `ctrbMat` with $A$ and $B$ matrices will give us a matrix $[B \quad AB]$.
```hs
def A_mat : Mat 2 2 := !![1, 2; 3, 4]
def B_vec : Mat 2 1 := !![1; 1]

#eval ctrbMat A_mat B_vec
```
We also define the method of constructing the $[A- \lambda I \quad B]$ matrix, which takes in a matrices $A$ and $B$ and a scalar (eigenvalue) as inputs using the `ofBlocks` function defined in `BlockMatLib`.

```hs
def ABe {n : ℕ} (A : Mat n n) (B : Mat n 1) (e : α) :=
  ofBlocks (A-e•(1 : Mat n n)) B
```



 # Conclusion

TODO: Re-describe your aim, what you achieved, and what is left to be done if anything. Also describe your current understanding of how well Lean and Mathlib support the area of mathematics you chose to explore, and what would be needed to fully support it.