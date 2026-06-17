import LeanHaar.TensorPower
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The permutation operator `W_π`

This file defines the permutation operator `W_π` on `𝓗⊗[d, k]`, which permutes the tensor
factors according to a permutation `π : Equiv.Perm (Fin k)`. It also defines the inner product
on `𝓗⊗[d, k]`, which is a prerequisite for defining unitarity of `W_π`.

## Main definitions

* `HilbertTensorPower.linearEquivEuclidean` — the linear equivalence to `EuclideanSpace`.
* `HilbertTensorPower.W` — the permutation operator `W_π`.
* `HilbertTensorPower.W_equiv` — the permutation operator as a linear equivalence.

## Main results

* `HilbertTensorPower.W_tprod` — action of `W_π` on pure tensors.
* `HilbertTensorPower.W_mul` — proves that `π ↦ W_π` is a group homomorphism.
* `HilbertTensorPower.W_map_tprod_comm` — the commutation relation between `W_π` and tensor
  products of operators.

## Implementation notes

The Hilbert space structure (norm and inner product) is induced from `EuclideanSpace` via a
canonical basis. This is necessary because `PiTensorProduct` does not carry a native
Hilbert space structure in Mathlib.
-/

namespace LeanHaar

open scoped TensorProduct

namespace HilbertTensorPower

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-! ## The Hilbert space structure on `𝓗⊗[d, k]` -/

/-- The linear equivalence between `𝓗⊗[d, k]` and `EuclideanSpace ℂ (Fin k → d)`
  induced by the standard orthonormal basis on each factor. -/
noncomputable def linearEquivEuclidean : 𝓗⊗[d, k] ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k → d) :=
  linearEquivTensorPower.trans
    ((Basis.piTensorProduct fun _ : Fin k => (FiniteHilbertSpace.basisFun d).toBasis).equivFun.trans
      (WithLp.linearEquiv 2 ℂ ((Fin k → d) → ℂ)).symm)

/-- The normed group structure is induced from `EuclideanSpace ℂ (Fin k → d)`
  along `linearEquivEuclidean`. -/
noncomputable instance : NormedAddCommGroup (𝓗⊗[d, k]) :=
  NormedAddCommGroup.induced _ _ linearEquivEuclidean.toLinearMap linearEquivEuclidean.injective

/-- The norm on `𝓗⊗[d, k]` is the same as the norm on the corresponding `EuclideanSpace`. -/
@[simp]
lemma norm_eq_val (x : 𝓗⊗[d, k]) : ‖x‖ = ‖linearEquivEuclidean x‖ := rfl

/-- The inner product space structure is induced from `EuclideanSpace ℂ (Fin k → d)`
  along `linearEquivEuclidean`. -/
noncomputable instance : InnerProductSpace ℂ (𝓗⊗[d, k]) :=
  InnerProductSpace.induced linearEquivEuclidean.toLinearMap

/-- The inner product on `𝓗⊗[d, k]` is the same as the inner product on the
  corresponding `EuclideanSpace`. -/
@[simp]
lemma inner_eq_val (x y : 𝓗⊗[d, k]) : inner ℂ x y = inner ℂ (linearEquivEuclidean x) (linearEquivEuclidean y) := rfl

/-- Being finite dimensional, `𝓗⊗[d, k]` is automatically a complete inner product space. -/
instance : CompleteSpace (𝓗⊗[d, k]) := FiniteDimensional.complete ℂ _

/-- The equivalence between `𝓗⊗[d, k]` and `EuclideanSpace ℂ (Fin k → d)`
  as a linear isometry equivalence, upgrading `linearEquivEuclidean`. -/
noncomputable def isometryEquivEuclidean : 𝓗⊗[d, k] ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin k → d) where
  toLinearEquiv := linearEquivEuclidean
  norm_map' _ := rfl

/-! ## The permutation operator `W_π` -/

/-- The permutation operator `W_π` on `𝓗⊗[d, k]`, which permutes the tensor factors according
to a permutation `π : Equiv.Perm (Fin k)`.

It is defined by conjugating `PiTensorProduct.reindex` with `linearEquivTensorPower`.
The convention is chosen such that `π ↦ W_π` is a group homomorphism.
NOTE: W_π as a linear equivalence, so the invertible structure follows.
-/
noncomputable def W_equiv (π : Equiv.Perm (Fin k)) : 𝓗⊗[d, k] ≃ₗ[ℂ] 𝓗⊗[d, k] :=
  ((linearEquivTensorPower.trans (PiTensorProduct.reindex ℂ (fun _ => 𝓗[d]) π)).trans
    linearEquivTensorPower.symm)

@[inherit_doc W_equiv]
noncomputable def W (π : Equiv.Perm (Fin k)) : 𝓗⊗[d, k] →ₗ[ℂ] 𝓗⊗[d, k] := (W_equiv π).toLinearMap

@[inherit_doc W]
scoped notation "W_" π:1024 => W π

/-- The action of `W_π` on an element `x` is given by `reindex π` on the underlying tensor. -/
@[simp]
lemma val_W (π : Equiv.Perm (Fin k)) (x : 𝓗⊗[d, k]) :
    (W π x).val = PiTensorProduct.reindex ℂ (fun _ => 𝓗[d]) π x.val := rfl

/-- The action of `W_π` on a pure tensor `ψ₁ ⊗ ⋯ ⊗ ψ_k` permutes the factors. -/
@[simp]
lemma W_tprod (π : Equiv.Perm (Fin k)) (ψ : Fin k → FiniteHilbertSpace d) :
    W π (tprod ψ) = tprod (ψ ∘ π.symm) := by
  ext; simp [val_W, PiTensorProduct.reindex_tprod]
  rfl

/-- `W_id` is the identity operator. -/
@[simp]
lemma W_one : (W (1 : Equiv.Perm (Fin k)) : 𝓗⊗[d, k] →ₗ[ℂ] 𝓗⊗[d, k]) = LinearMap.id := by
  ext x; simp [val_W, Equiv.Perm.one_def, PiTensorProduct.reindex_refl]

/-- `π ↦ W_π` is a group homomorphism. -/
@[simp]
lemma W_mul (π σ : Equiv.Perm (Fin k)) :
    (W (π * σ) : 𝓗⊗[d, k] →ₗ[ℂ] 𝓗⊗[d, k]) = W π ∘ₗ W σ := by
  apply HilbertTensorPower.hom_ext
  intro ψ
  simp [W_tprod, Equiv.Perm.mul_def]
  rfl

/-- The inverse of `W_π` is `W_{π⁻¹}`. -/
@[simp]
lemma W_inv (π : Equiv.Perm (Fin k)) :
    ((W_equiv (d := d) (k := k) π).symm : 𝓗⊗[d, k] ≃ₗ[ℂ] 𝓗⊗[d, k]) = W_equiv π⁻¹ := by
  ext x
  simp [W_equiv, PiTensorProduct.reindex_symm]
  rfl

/-- The commutation relation between `W_π` and a tensor product of operators. -/
theorem W_map_tprod_comm (π : Equiv.Perm (Fin k))
    (f : Fin k → (FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d)) :
    W π ∘ₗ map_tprod f = map_tprod (f ∘ π.symm) ∘ₗ W π := by
  apply hom_ext
  intro ψ
  simp [W_tprod, Function.comp_apply]
  rfl

end HilbertTensorPower

end LeanHaar
