import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Algebra.Group.Pi.Basic

import LeanHaar.ForMathlib.TensorV2

/-!
# Commutation of permutation and diagonal actions

This file proves that the permutation action `W_σ` commutes with the diagonal action `g^{⊗k}`.
This is a fundamental fact underlying Schur-Weyl duality: the images of the symmetric group
and the general linear group in `End(V^{⊗k})` mutually commute.

## Main results

* `SchurWeyl.permAction_diagAction_comm` - `W_σ ∘ g^{⊗k} = g^{⊗k} ∘ W_σ`
* `SchurWeyl.permImage_subset_centralizer_diagImage` - `permImage ⊆ centralizer(diagImage)`
* `SchurWeyl.diagImage_subset_centralizer_permImage` - `diagImage ⊆ centralizer(permImage)`
-/

noncomputable section

open scoped TensorProduct

namespace ForMathlib.Tensor

variable {d k : ℕ}

/-- The permutation action commutes with the diagonal action on elementary tensors. -/
theorem permAction_diagAction_tprod (σ : Equiv.Perm (Fin k))
    (g : Module.End ℂ (Fin d → ℂ)) (v : Fin k → (Fin d → ℂ)) :
    (permAction d σ) (diagAction d k g (PiTensorProduct.tprod ℂ v)) =
    diagAction d k g ((permAction d σ) (PiTensorProduct.tprod ℂ v)) := by
  simp [permAction_tprod, diagAction_tprod]

/--
The permutation action commutes with the diagonal action:
`W_σ ∘ g^{⊗k} = g^{⊗k} ∘ W_σ` as linear maps on `V^{⊗k}`.
-/
theorem permAction_diagAction_comm (σ : Equiv.Perm (Fin k))
    (g : Module.End ℂ (Fin d → ℂ)) :
    (permAction d σ).toLinearMap ∘ₗ diagAction d k g =
    diagAction d k g ∘ₗ (permAction d σ).toLinearMap := by
  ext x
  exact permAction_diagAction_tprod σ g x

/-- Every permutation operator lies in the centralizer of the diagonal image. -/
theorem permImage_subset_centralizer_diagImage :
    permImage d k ⊆ (diagImage d k).centralizer := by
  intro x hx
  obtain ⟨σ, rfl⟩ := hx
  intro y hy
  obtain ⟨g, rfl⟩ := hy
  exact (permAction_diagAction_comm σ g).symm

/-- Every diagonal operator lies in the centralizer of the permutation image. -/
theorem diagImage_subset_centralizer_permImage :
    diagImage d k ⊆ (permImage d k).centralizer := by
  intro x hx
  obtain ⟨g, rfl⟩ := hx
  intro y hy
  obtain ⟨σ, rfl⟩ := hy
  exact permAction_diagAction_comm σ g

end ForMathlib.Tensor

end
