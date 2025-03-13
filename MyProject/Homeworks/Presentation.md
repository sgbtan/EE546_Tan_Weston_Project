

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
- BlockMatLib which contain methods of recursively creating and decomposing blocks of matrices and helpers for basic operations.
- ControlLib which contains methods of constructing the controllability matrix as well as the $[A - \lambda I \quad B]$ matrix above.

For simplicity, we are assuming only one control input meaning that $B$ will be an $n \times 1$ vector, controllability matrix $C$ will be an $n \times n$ matrix, and $[A - \lambda I \quad B]$ will be $n \times n$.


## Resources

The theorems and proofs used in throughout this project are drawn from Chapter 6 of Linear System Theory and Design by Chi-Tsong Chen.

 # LinAlgDefs

## `is_eig_val` and `is_eig_vec`
We first needed some way to declare given a matrix and a scalar, whether that scalar is an eigenvalue of the matrix. Similarly given a matrix and a vector, whether that vector is an eigenvector of the matrix. `is_eig_val` and `is_eig_vec` helps us achieve this.

```hs
def is_eig_val {n : ℕ}
(A : Mat n n)
(eig: α)
: Prop :=
  ∃ v : Mat 1 n, v*A = eig•v

def is_eig_vec {n : ℕ}
(A : Mat n n)
(v: Mat 1 n)
: Prop :=
  ∃ eig : α, v*A = eig•v
```

## Example
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

## `is_full_rank` & `not_full_rank`
We also needed to be able to declare if a matrix is full rank or not.



```hs
#check SL2.mk !![1,1;0,1] rfl
#check SL2.mk !![1,1;0,1]
```
 Or we can use curly braces and the `:` operator to inform Lean what type we are building. 
```hs
#check ({val:=!![1,1;0,1], det1 := rfl} : SL2)
#check ({val:=!![1,1;0,1]} : SL2)
```
  We can also use angle brackets: 
```hs
#check (⟨!![1,1;0,1], rfl⟩ : SL2)
```
 If we do not supply an integer matrix or a determinant 1 matrix, the construction fails. 
```hs
#check_failure SL2.mk !![(a:ℝ),1;1,0]
#check_failure SL2.mk !![1,1;1,1]
```
 ## Distinguished Elements

Two distinguished elements in SL2 are the following matrices:

  $$
  T = \begin{pmatrix}
  1 & 1\\
  1 & 0
  \end{pmatrix} {  } \mathrm{and} {  }
  W = \begin{pmatrix}
  0 & -1\\
  1 & 0
  \end{pmatrix}.
  $$

These elements are said to *generate* SL2, because every element of SL2 can be formed from a combination of $T$, $S$ and their inverses (as, hopefully, show below).  
```hs
def T := SL2.mk !![1,1;0,1]
def S := SL2.mk !![0, -1; 1, 0]
```
 ## Coercion

Elements in SL2 can be coerced to matrices so that one does not need to write, for example, $S.val$.   
```hs
#check S*T
#check S 0 0
```
 ## Operations on Elements of SL2

Elements in SL2 hav all the same properties as invertible 2x2 matrices, including multiplication, inverses, and a distinguished identity element.  
```hs
#check S*T
#eval S*T
#check T⁻¹
#check T * 1
```
 ### Example Calculation

All of the instances required to prove `SL2` is a Group are defined in Lib/SL2.lean. Thus, we can use Mathlib's built in simplification rules for groups either directly, or by just calling the `group` tactic. 
```hs
example (A B : SL2): (A⁻¹*B*A)⁻¹ = A⁻¹*B⁻¹*A :=
  calc (A⁻¹*B*A)⁻¹
  _  = A⁻¹ * (A⁻¹*B)⁻¹   := by rw[DivisionMonoid.mul_inv_rev]
  _  = A⁻¹ * (B⁻¹*A⁻¹⁻¹) := by rw[DivisionMonoid.mul_inv_rev]
  _  = A⁻¹ * (B⁻¹*A)     := by rw[DivisionMonoid.inv_inv]
  _  = A⁻¹ * B⁻¹ * A     := by rw[Semigroup.mul_assoc]

example (A B : SL2): (A⁻¹*B*A)⁻¹ = A⁻¹*B⁻¹*A := by group
```
 ## Examples

Here are some examples that use the definitions and theorems for SL2.  
```hs
example : ¬ ∀ A B : SL2, A*B = B*A := by
  intro h
  have h1 := h S T
  have h2 : (S*T).val 0 0 = (T*S).val 0 0 := by simp[h1]
  simp[S,T] at h2

example : ∀ A B : SL2, (A*B)⁻¹ = B⁻¹ * A⁻¹ := by
  intro A B
  group

example : ∀ A : SL2, A⁻¹*A = 1 := by
  intro A
  group

example : S*T ≠ T*S := by
  intro h
  have h2 : (S*T).val 0 0 = (T*S).val 0 0 := by simp[h]
  simp[S,T] at h2

example (A B C : SL2) : A * (B * C) * (A * C)⁻¹ * (A * B * A⁻¹)⁻¹ = 1 := by
  group
```
 # Fractional Linear Transformations

As described above, a fractional linear transformation has the form

   $$
    z \mapsto \frac{az+b}{cz+d}.
   $$

In general, $a$, $b$, $c$ and $d$ can come from any ring, and the only requirement is that $ad+bc \ne 0$. Here, we additionally require that $a$, $b$, $c$ and $d$ are integers and $ad+bc = 1$. To keep track of the data, we pack everything into a structure and, with an abuse of naming, call it an`FLT`:  
```hs
namespace Temp

@[ext]
structure FLT where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  det1 : a*d - b*c = 1 := by decide

end Temp
```
 The main accomplishment of this section is to define the map assocated with an FLT, which we call fl_map. 
```hs
#check fl_map      -- fl_map (f : FLT) (z : UHP) : UHP
```
 Specifically, we needed to show that the map so defined produces an element of `UHP` when given an element of `UHP`. We used the proof of this fact from [these](https://public.websites.umich.edu/~hlm/nzm/modgp.pdf) lecture notes, which explains the result as follows. Letting $z = x + yi$, with y > 0, we get

$$
w \triangleq \frac{az+b}{cz+d} = \frac{az+b}{cz+d} \frac{c\bar{z}+d}{c\bar{z}+d}
$$

$$
= \frac{ac(x^2+y^2)+(bc+ad)x+bd}{(cx+d)^2+(cy)^2} +
 i\frac{(ad-bc)y}{(cx+d)^2+(cy)^2}.
$$

Since $ad+bc = 1$, we conclude that $(cx+d)^2+(cy)^2>0$ and $(ad+bc)y>0$. The proof of this is contained in Lib/FLT.lean, is 60 lines long, and uses about 14 helper lemmas defined several hundred lines of code. Clearly, there is room for improvement.

 ## USING FLTs

In Lib/FLT.lean, we instantiate all the classes needed to show that the FLT structure is a group, as well as coerce it appropriately. Thus, all the following examples work. 
```hs
example (f: FLT) (z : UHP) : f z = f z := rfl

example (f: FLT) : f * f⁻¹ = 1 := by group

example (f g h : FLT) : f * (g * h) * (f * h)⁻¹ * (f * g * f⁻¹)⁻¹ = 1 := by group
```
 # SHOWING SL2 ≅ FLT

Given the similarity between the definitions of SL2 and FLT in terms of $a$, $b$, $c$, and $d$ and the determinant condition, it should come as no surprise that the two groups we instantiated above are essentially the same.

Mathematically, we say they isomorphic, which means: There exists a function φ from the elemtns of `SL2` to the elements of `FLT` that is *bijective* and for all $A$ and $B$ in `SL2`,

  $$
    \phi(A) \circ \phi(B) = \phi(AB)
  $$

In Lib/FLT.lean, we define to maps: `fl_to_sl2` and `sl2_to_fl` that serve as witnesses to this fact. And we prove two theorems, which simply show that we are doing our book-keeping with $a$, $b$, $c$, and $d$ correctly: 
```hs
#check sl2_map_map   -- sl2_to_fl ∘ fl_to_sl2 = id
#check fl_map_map    -- fl_to_sl2 ∘ sl2_to_fl = id
```


***ISSUE*** This isn't quite right. The transformations $z \mapsto \frac{az+b}{cz+d}$ and $z \mapsto \frac{-az-b}{-cz-d}$ do the same thing, but corresponding matrices are different. So we need to really take the quotient by the equivalence $I=-I$.

## Bijective

Either one of these facts is enough to show a function is a bijection. Lean provides the necessary definitions and theorems in the Prelude.  
```hs
theorem li : Function.LeftInverse fl_to_sl2 sl2_to_fl  := by
  intro x
  simp[fl_to_sl2,sl2_to_fl,SL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem ri : Function.RightInverse fl_to_sl2 sl2_to_fl := by exact congrFun rfl

theorem bijective_sl2_to_fl : Function.Bijective sl2_to_fl := by
  apply And.intro
  . apply Function.LeftInverse.injective li
  . apply Function.RightInverse.surjective ri
```
 ## FLT and SL2 are Isomorphic

To show the precise form of the fact that group operation is preserved by the bijection, we use a theorem we proved in Lib/FLT.lean.  
```hs
theorem flt_sl2_group_iso (f g : FLT) : fl_to_sl2 f * fl_to_sl2 g = fl_to_sl2 (f*g) := by
  apply Eq.symm
  rw[←fl_comp_sl2_iff]
```
 # Group Generators

TODO: Show that $T$ and $S$ generate SL2. Progress can be found [here](./ModGroup/Lib/Generators.lean).


 # Conclusion

TODO: Re-describe your aim, what you achieved, and what is left to be done if anything. Also describe your current understanding of how well Lean and Mathlib support the area of mathematics you chose to explore, and what would be needed to fully support it.