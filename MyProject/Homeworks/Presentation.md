

<center><h1>Proving Controllability Rank Condition</h1></center>
<center><h2>EE 546 : Knowledge Representation and Reasoning</h2></center>

<center>
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

where 
- $A$ is an $n \times n$ state matrix which describes how the current state of a system affects its future state. 
- $B$ is an $n \times p$ input matrix which defines how external inputs influence the state of the system.
- $x$ is an $n \times 1$ state vector which represents internal state of the system.
- $u$ is an $p \times 1$ input vector which represents the external inputs applied to the system.

The state equation or the pair ($A$, $B$) is said to be controllable if for any initial state $x(0) = x_0$ and any final state $x_1$ there exists an input that transfers $x_0$ to $x_1$ in a finite time. If not, ($A$, $B$) is said to be uncontrollable.

The state equation can be used to derive the **controllability matrix** by performing repeated back-substitution as the state progresses from $x(0)$ at initial time to $x(n)$. This results in a linear combination of the columns of $B$, $AB$, . . . , $A^{n-1}B$, i.e, the controllability matrix, $C$.

$$
x_n = C \cdot \begin{bmatrix}
u_{n-1} \\ u_{n-2} \\ \vdots \\ u_0
\end{bmatrix}
$$

Chapter 6 of Linear System Theory and Design by Chi-Tsong Chen contains mathematical proofs of the equivalence of the five statements below in **Theorem 6.1**:

   1. The n-dimensional pair (A,B) is controllable.

   2. The $n \times n$ matrix $W_c(t)$ is nonsingular for any t > 0.
  
   $$
   W_c(t) = \int_{0}^{t} e^{A\tau}BB'e{A'\tau} \,d\tau = \int_{0}^{t} e^{A(t-\tau)}BB'e{A'(t-\tau)} \,d\tau
   $$
   
   3. The $n \times np$ controllability matrix has rank $n$ (full row rank).

   $$
   C = \begin{bmatrix}
   B \quad AB \quad A^2B \cdots A^{n-1}B 
   \end{bmatrix}
   
   $$
   4. The $n \times (n+p)$ matrix $[A-\lambda I \quad B]$ has full row rank at every eigenvalue, $\lambda$, of $A$.

   5. If, in addition, all eigenvalues of A have negative real parts, then the unique solution of

   $$
   AW_c + W_cA' = -BB'
   $$
   
   &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; is positive definite. The solution is called the controllability Gramian and can be expressed as

   $$
   W_c(t) = \int_{0}^{t} e^{A\tau}BB'e{A'\tau} \,d\tau
   $$

<br>

In this project, we aim encode proof of the equivalence all the above, However, to simplify this task, we are first focusing on proving equivalance between statements $3$ and $4$ above in Lean 4. As shown below, this involves working with purly matrix operations in Lean 4. In order to simplify the problem even further, we **assume a single control input** is applied to the system. **This simplifies $u$ into a scalar, and $B$ into a $n \times 1$ vector**. 


# Proving Equivalence between $3$ and $4$

The strategy of proving equivalence between $3$ and $4$ in the forward direction as described by Chen is as follows.

Assuming first that if the **controllability matrix**, **$C$** has full row rank, then matrix $[A - \lambda I \quad B]$ has full row rank at every eigenvalue, $\lambda$, of $A$.

If matrix $[A - \lambda I \quad B]$ **does not** have full row rank at every eigenvalue, $\lambda$, of $A$, then there exists an eigenvalue $\lambda_1$, and a $1 \times n$ vector $q \neq 0$ such that

$$
q [A - \lambda_1 I \quad B] = 0
$$

which implies $qA = \lambda_1q$ and $qB = 0$.

Thus $q$ is a left eigenvector of $A$.

From here, the controllability matrix can be constructed using $qA = \lambda_1q$

$$
qA^2 = (qA)A = (\lambda_1q)A = \lambda_1^2q
$$

Proceeding forward, we have $qA^k = \lambda_1^kq$. Thus we have

$$
q [B \quad AB \cdots A^{n-1}B] = [qB \quad \lambda_1qB \cdots \lambda_1^{n-1}qB] = 0
$$

where $[B \quad AB \cdots A^{n-1}B]$ is the **controllability matrix**, **$C$**, which contradicts the initial assumption that $C$ has full row rank.

In summary, the above proves equivalence between $3$ and $4$ by contradition by showing if $[A - \lambda_1 I \quad B]$ does not have full row rank at every eigenvalue of $A$, then the **controllability matrix**, $C$ does not have full row rank as well.

## Encoding this proof in Lean 4

```hs
theorem three_to_four : ∀ (A : Mat n n) (B : Mat n 1), is_full_rank (ctrbMat A B) → ∀ (e : α), is_eig_val A e → is_full_rank (ABe A B e) := by

  unfold is_full_rank
  intro A B hq e _ q qNZ
  have ctrbFR := hq q qNZ
  by_contra ABeNFR

  have qBZ : q*B=0 := by exact (ABeRightZero A B q e) ABeNFR
  have qAe : q*A=e•q := by simp [(ABeLeftZero A B q e) ABeNFR]
  
  have qAek : ∀ (k : ℕ), q*(A^k)=(e^k)•q := by exact hqAek A q e qAe
  obtain ctrbNFR : q*ctrbMat A B = 0 := by exact hctrbNFR A B q e qBZ qAek
  exact ctrbFR ctrbNFR
```

Theorem `three_to_four` restates that for all $n \times n$ matrices $A$, and $n \times 1$ vectors $B$, if the controllability matrix constructed out of $A$ and $B$ has full (row) rank, then for all eigenvalues of $A$, matrix $[A - \lambda I \quad B]$ has full (row) rank.

The definition `is_full_rank` is used to construct `ctrbFR` : $q[B \quad AB \cdots A^{n-1}B] \neq 0$ which is the initial assemption that the controllability matrix has full row rank. `by_contra ABeNFR` begins the proof by contradiction, creating $q [A - \lambda_1 I \quad B] = 0$ which needs to be shown is false, as with the proof described by Chen.

Next, in order to distribute $q$ into matrix $[A-\lambda_1 I \quad B]$, theorems `ABeRightZero` and `ABeLeftZero` are applied to create `qBZ` and `qAe`. `ABeRightZero` and `ABeLeftZero` are proofs that $q[(A-\lambda I) \quad B] = 0$ implies that $qB = 0$ and $qA = qλI$ respectively.

Following this, we prove that $qA^k = \lambda_1^k q$ by lemma `hqAek` and that $
q [B \quad AB \cdots A^{n-1}B] = 0$ by lemma `hctrbNFR`.

Finally, applying our assumption that the controllability matrix, $C$ has full row rank, `ctrbFR` : $q[B \quad AB \cdots A^{n-1}B] \neq 0$ proves the contradiction.


# Required Definitions and Theorems
In order to express theorem `three_to_four` above, we created and proved our own definitions and theorems. These definitions and theorems can be found in libraries we created: `LinAlgDefs`, `BlockMatLib`, and `ControlLib`. Lemmas used to help prove theorem `three_to_four` are found in `three_to_four_lemmas`. The main definitions and theorems created are:

- `Mat (n m : ℕ)`
- `is_full_rank`
- `is_eig_val`
- `ctrbMat`
- `ABeRightZero`
- `ABeLeftZero`
- `hqAek`
- `hctrbNFR`

However, some of these depend on several lower-level definitions which we also had to create. 

## `Mat (n m : ℕ)` <span style="font-size: 12px;">LinAlgDefs</span>
`Mat (n m : ℕ)` is an abbreviation of the definition of a Matrix as defined in `mathlib`, `Matrix (Fin n) (Fin m) α`.

```hs
abbrev α : Type := ℂ

abbrev Mat (n m:ℕ) := Matrix (Fin n) (Fin m) α
```

## `is_full_rank` <span style="font-size: 12px;">LinAlgDefs</span>
Given a matrix, `is_full_rank` allows us to declare that a matrix is full rank.

``` hs
def is_full_rank {n m: ℕ} (mat : Mat n m) : 
Prop :=
  ∀ q : (Mat 1 n), q ≠ 0 → q * mat ≠ 0
```

## `is_eig_val` <span style="font-size: 12px;">LinAlgDefs</span>
Given a matrix and a scalar, `is_eig_val` allows us to declare that scalar is an eigenvalue of the matrix.

```hs
def is_eig_val {n : ℕ} (A : Mat n n) (eig: α) : 
Prop :=
  ∃ v : Mat 1 n, v*A = eig•v
```
## `ctrbMat` <span style="font-size: 12px;">ControlLib</span>
Given a matrix $A$ and a vector $B$, `ctrbMat` allows us to construct the controllability matrix, $C = [B \quad AB \quad A^2B \cdots A^{n-1}B]$.

```hs
noncomputable
def ctrbMat {n : ℕ} (A : Mat n n) (B : Mat n 1) : 
Mat n n :=
  λ i j => (A^j.val*B) i 0
```

## `ABeRightZero` <span style="font-size: 12px;">ControlLib</span>
Theorem `ABeRightZero` proves that $q[(A-λI) \quad B] = 0$ implies that $qB = 0$. Its proof uses the `getBlock` and `getBlockEquiv` definitions.

    ABeLeftZero
      |_getBlock
      |_getBlockEquiv
          |_getBlock

```hs
theorem ABeRightZero {n : ℕ} (A : Mat n n) (B : Mat n 1) (q : Mat 1 n) (e : α) : 
q * (ABe A B e) = 0 → q*B = 0 := by
  sorry*
```
`sorry*` indicates that the full proof is available in the `ControlLib` library.

## `ABeLeftZero` <span style="font-size: 12px;">ControlLib</span>
Theorem `ABeLeftZero` proves that $q[(A-λI) \quad B] = 0$ implies that $qA = qλI$. Similarly, its proof uses the `getBlock` and `getBlockEquiv` definitions.

    ABeLeftZero
      |_getBlock
      |_getBlockEquiv
          |_getBlock

```hs
theorem ABeLeftZero {n : ℕ} (A : Mat n n) (B : Mat n 1) (q : Mat 1 n) (e : α) : 
q * (ABe A B e) = 0 → q*A = q*e•(1 : Mat n n) := by
  sorry*
```
`sorry*` indicates that the full proof is available in the `ControlLib` library.

## `hqAek` <span style="font-size: 12px;">three_to_four_lemmas</span>

Theorem `hqAek` proves that $qA^k = \lambda^kq$.

```hs
theorem hqAek {n : ℕ} (A : Mat n n) (q : Mat 1 n) (e : α) (qAe : q*A=e•q) (k : ℕ) : 
q*(A^k)=(e^k)•q := by
  sorry*
```
`sorry*` indicates that the full proof is available in the `three_to_four_lemmas` library.

## `hctrbNFR` <span style="font-size: 12px;">three_to_four_lemmas</span>

Theorem `hqAek` proves that if $qB = 0$, $q[B \quad AB \quad A^2B \cdots A^{n-1}B] = 0$. 

```hs
theorem hctrbNFR {n : ℕ} (A : Mat n n) (B : Mat n 1) (q : Mat 1 n) (e : α) (qBZ : q*B=0 ) (qAek : ∀ (k : ℕ), q*(A^k)=(e^k)•q): 
q*ctrbMat A B = 0 := by
  sorry*
```
`sorry*` indicates that the full proof is available in the `three_to_four_lemmas` library.

 <!-- ### LinAlgDefs

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

Here we require a way to construct a matrix from other matrices. 

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
``` -->


# Conclusion

Our goal with this project is to prove in lean that the contrallability matrix has full row rank if the matrix $[A-\lambda I \quad B]$ has full row rank. We were successful with encoding this proof and while doing so, have built a significant amount of the machinery required. We have encoded the necessary linear algebra definitions, built functions to construct and destruct matrices from and to blocks, and used those functions to build other functions to construct the contrallability matrix and the matrix $[A-\lambda I \quad B]$. 

To complete the proof of equivalance of statements ($3$) and ($4$), we will need to encode the proof that if the controllability does not have full row rank, then there exists some eigenvalue, $\lambda_1$ of $A$ such that the matrix $[(A-λI) \quad B]$ does not have full row rank. This would be the goal for future work. To do so, we would require 2 additional theorems:

1. Controllability is invariant under any equivalence transfomation.
2. If $C$ does not have full rank or $\rho(C) = n - m$ for some integer $m \geq 1$, then there exists a nonsingular matrix $P$ such that

$$
\bar{A} = PAP^{-1} , \quad \bar{B} = PB
$$


# References

Chen, Chi-Tsong. (2013). Linear Systems Theory and Design. Oxford University Press, 184-187