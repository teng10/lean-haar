import LeanHaar.TensorPower
import LeanHaar.Permutation
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix representation of permutation operators

This file defines the matrix representation of the permutation operators `W_π` on `𝓗⊗[d, k]`.
The representation is given with respect to the standard basis `basis d k`.

## Main definitions

* `HilbertTensorPower.basis` — the standard basis of `𝓗⊗[d, k]`.
* `HilbertTensorPower.indexPerm` — the permutation on basis indices induced by `π`.
* `HilbertTensorPower.W_matrix` — the matrix representation of `W_π`.
* `HilbertTensorPower.PermutationRepresentation` — a structure bundling the representation.
* `HilbertTensorPower.ConcretePermutation` — a structure for computable (evaluable) matrices.

## Main results

* `HilbertTensorPower.toMatrix_W` — proves that `W_matrix π` is the correct matrix
  representation of the linear map `W π`.
* `HilbertTensorPower.ConcretePermutation.toComplex_eq_W` — proves that the computable
  integer matrix, when cast to complex, matches `W_matrix`.

## Implementation notes

The representation is defined by permuting the multi-indices `Fin k → d` of the standard basis.
We provide both a noncomputable complex matrix representation (for theory) and a computable
integer matrix representation (for evaluation and testing).
-/

open Module

namespace LeanHaar

namespace HilbertTensorPower

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-! ## The standard basis and index permutation -/

/-- The standard basis of `𝓗⊗[d, k]`, indexed by `Fin k → d`. -/
noncomputable def basis (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    Basis (Fin k → d) ℂ (𝓗⊗[d, k]) :=
  (Basis.piTensorProduct fun _ : Fin k => (FiniteHilbertSpace.basisFun d).toBasis).map
    linearEquivTensorPower.symm

/-- The permutation induced on the basis indices `Fin k → d` by a permutation `π` of `Fin k`.
The convention matches `W_π (ψ₁ ⊗ ⋯ ⊗ ψ_k) = ψ_{π⁻¹ 1} ⊗ ⋯ ⊗ ψ_{π⁻¹ k}`. -/
def indexPerm (π : Equiv.Perm (Fin k)) : Equiv.Perm (Fin k → d) where
  toFun f := f ∘ π.symm
  invFun f := f ∘ π
  left_inv f := by ext; simp
  right_inv f := by ext; simp

/-! ## Matrix representation of `W_π` -/

/-- The matrix representation of the permutation operator `W_π` with respect to the
  standard basis. -/
noncomputable def W_matrix (π : Equiv.Perm (Fin k)) : Matrix (Fin k → d) (Fin k → d) ℂ :=
  Equiv.Perm.permMatrix ℂ (indexPerm π).symm

/-- `basis d k f` is exactly the pure tensor of the corresponding basis vectors. -/
lemma basis_eq_tprod (f : Fin k → d) :
    basis d k f = tprod (fun i => FiniteHilbertSpace.basisFun d (f i)) := by
  simp [basis, tprod, FiniteHilbertSpace.basisFun]

/-- `W π` acts on the standard basis by permuting the indices via `indexPerm π`. -/
lemma W_basis (π : Equiv.Perm (Fin k)) (f : Fin k → d) :
    W π (basis d k f) = basis d k (indexPerm π f) := by
  rw [basis_eq_tprod, W_tprod, basis_eq_tprod]
  simp [indexPerm, Function.comp_def]

/-- The matrix `W_matrix π` represents the linear map `W π`. -/
lemma toMatrix_W (π : Equiv.Perm (Fin k)) :
    LinearMap.toMatrix (basis d k) (basis d k) (W π) = W_matrix π := by
  ext i j
  simp [W_matrix, Equiv.Perm.permMatrix, LinearMap.toMatrix_apply, W_basis, Finsupp.single_apply]
  -- LHS: if (indexPerm π) j = i then 1 else 0
  -- RHS: if (indexPerm π).symm i = j then 1 else 0
  apply ite_congr
  · rw [Equiv.symm_apply_eq]
    apply propext
    exact eq_comm
  · intro; rfl
  · intro; rfl

/-! ## The `PermutationRepresentation` structure -/

/-- A data structure representing the matrix representation of the permutation operators. -/
structure PermutationRepresentation (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) where
  /-- The matrix corresponding to a permutation `π`. -/
  toMatrix : Equiv.Perm (Fin k) → Matrix (Fin k → d) (Fin k → d) ℂ
  /-- The matrix correctly represents the permutation operator `W_π`. -/
  represents_W : ∀ π, LinearMap.toMatrix (basis d k) (basis d k) (W π) = toMatrix π

/-- The canonical permutation representation of `S_k` on `(ℂᵈ)⊗ᵏ`. -/
noncomputable def standardRepresentation (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    PermutationRepresentation d k where
  toMatrix := W_matrix
  represents_W := toMatrix_W

/-! ## Computable (concrete) representations for evaluation -/

/-- A structure bundling a permutation with its computable integer matrix representation. -/
structure ConcretePermutation (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) where
  π : Equiv.Perm (Fin k)
  /-- The matrix representation with integer entries, making it computable. -/
  matrixInt : Matrix (Fin k → d) (Fin k → d) Int
  /-- Proof that this matrix indeed represents the permutation. -/
  is_permutation : matrixInt = Equiv.Perm.permMatrix Int (indexPerm π).symm

namespace ConcretePermutation

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-- Convert the concrete integer matrix to a complex matrix for use in calculations. -/
def toComplex (cp : ConcretePermutation d k) : Matrix (Fin k → d) (Fin k → d) ℂ :=
  cp.matrixInt.map (↑)

/-- The complex version matches the standard `W_matrix`. -/
lemma toComplex_eq_W (cp : ConcretePermutation d k) :
    cp.toComplex = W_matrix cp.π := by
  simp [toComplex, cp.is_permutation, W_matrix, Equiv.Perm.permMatrix]
  exact PEquiv.map_toMatrix (Int.castRingHom ℂ) _

end ConcretePermutation

/-- Method to get a concrete (computable) representation of `W_π`. -/
def getConcrete {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ} (π : Equiv.Perm (Fin k)) :
    ConcretePermutation d k :=
  { π := π,
    matrixInt := Equiv.Perm.permMatrix Int (indexPerm π).symm,
    is_permutation := rfl }

/-! ## General matrix evaluation support -/

/-- A general `Repr` instance for matrices indexed by finite types, enabling `#eval`. -/
noncomputable instance {m n α : Type*} [Fintype m] [Fintype n] [Repr α] : Repr (Matrix m n α) where
  reprPrec M _ :=
    let rows := (Finset.univ : Finset m).toList.map fun i =>
      let cols := (Finset.univ : Finset n).toList.map fun j => repr (M i j)
      f!"![{Std.Format.joinSep cols ", "}]"
    f!"![{Std.Format.joinSep rows ", "}]"

end HilbertTensorPower

end LeanHaar
