
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


 # Approach

imports


```hs
