import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

structure BlockCat (n m p : ℕ) where
A : Matrix (Fin n) (Fin m) ℂ
B : Matrix (Fin n) (Fin p) ℂ

def BlockCat.toMat {n m p : ℕ} (M : BlockCat n m p)
: Matrix (Fin n) (Fin (m+p)) ℂ :=
λ i j =>
if h : j < m
then M.A i (Fin.mk j h)
else M.B i (Fin.mk (j-m) (by
have h1 : j ≥ m := by exact Nat.le_of_not_lt h
have h2 := Fin.is_lt j
exact Nat.sub_lt_left_of_lt_add h1 h2
))

instance BlockCat.block_cat_to_mat {n m p : ℕ}
: CoeSort (BlockCat n m p) (Matrix (Fin n) (Fin (m+p)) ℂ) :=
⟨ toMat ⟩

def A : Matrix (Fin 2) (Fin 3) ℂ := !![1,0,2;0,1,2]
def B := BlockCat.mk !![1,0;0,1] !![2;2]

-- coercion to matrix works
#check A = B

instance mod_group_coe_fun {n m p : ℕ}
: CoeFun (BlockCat n m p) (λ _ => (Fin n) → (Fin (m+p)) → ℂ) :=
⟨ λ M => (λ i j => M.toMat i j) ⟩

-- coercion to function works
#check B 0 1


#check Matrix.transpose B.toMat
#check Matrix.transpose (B: Matrix (Fin 2) (Fin 3) ℂ)

#check_failure Matrix.transpose B -- I think Lean can't figure out base type ℂ
-- so does not know what to cast to.

def BlockCat.tr {n m p : ℕ} (B : BlockCat n m p) := B.toMat.transpose

#check B.tr

def C := (BlockCat.mk A (BlockCat.mk A A).toMat)

universe u
inductive Bl (a: Type u) where
| base (v : a) : Bl a
| cons (B : a) (b : Bl a) : Bl a

def v : Matrix (Fin 3) (Fin 1) ℤ := !![1;2;3]

#check Bl.cons v (Bl.cons v (Bl.base v))

def Bl.toMat {α : Type*} {n: ℕ} (m:ℕ) (B : Bl (Matrix (Fin n) (Fin 1) α))
: Matrix (Fin n) (Fin m) α :=
match B with
| Bl.base v => λ i j => v i 0
| Bl.cons v B' => λ i j =>
if j.val = 0
then v i 0
else (Bl.toMat sorry B') i

#check Bl.toMat 3 (Bl.cons v (Bl.cons v (Bl.base v)))

def toMat {n : ℕ} (B : List (Matrix (Fin n) (Fin 1) ℤ)) :=
λ (i:Fin n) (j:Fin B.length) => B[j] i 0

#check (List.cons v (List.cons v List.nil))[0] 1 0

#check toMat (List.cons v (List.cons v List.nil))

example : ∃ q : Matrix (Fin 1) (Fin 3) ℤ, q ≠ 0 ∧ q * (toMat (List.cons v (List.cons v List.nil))) = 0 := sorry
