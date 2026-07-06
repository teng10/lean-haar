/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic

import LeanHaar.ForMathlib.TensorV2

/-!
# Matrix representation of tensor power operators

This file defines the standard computational basis for the tensor power space `TensV d k`,
the matrix representation of endomorphisms on this space, and proves properties about the
matrices representing the permutation and diagonal actions.
-/

noncomputable section

open scoped TensorProduct
open SchurWeyl

namespace ForMathlib.Tensor

variable {d k : ℕ}

/-- The standard basis of `V^{⊗k}`. -/
def tensorBasis (d k : ℕ) :
    Module.Basis ((i : Fin k) → Fin d) ℂ (TensV d k) :=
  Basis.piTensorProduct (fun (_ : Fin k) => Pi.basisFun ℂ (Fin d))

/-- Matrix representation of endomorphisms. -/
def toEndMatrix (d k : ℕ) :
    Module.End ℂ (TensV d k) ≃ₗ[ℂ]
    Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
  LinearMap.toMatrix (tensorBasis d k) (tensorBasis d k)

/-- `W_σ(e_I) = e_{I ∘ σ⁻¹}`. -/
theorem permAction_tensorBasis (σ : Equiv.Perm (Fin k)) (I : Fin k → Fin d) :
    (permAction d σ) (tensorBasis d k I) = tensorBasis d k (I ∘ σ.symm) := by
  unfold permAction; simp +decide [tensorBasis]

/-- Matrix of `W_σ`. -/
theorem toEndMatrix_permAction (σ : Equiv.Perm (Fin k)) (I J : Fin k → Fin d) :
    toEndMatrix d k ((permAction d σ).toLinearMap) I J =
    if I = J ∘ σ.symm then 1 else 0 := by
  convert LinearMap.toMatrix_apply (tensorBasis d k) (tensorBasis d k)
    ((permAction d σ).toLinearMap) I J using 1
  erw [permAction_tensorBasis]
  aesop

/-- Matrix of `g^{⊗k}`. -/
theorem toEndMatrix_diagAction (g : Module.End ℂ (Fin d → ℂ)) (I J : Fin k → Fin d) :
    toEndMatrix d k (diagAction d k g) I J =
    ∏ m : Fin k,
      LinearMap.toMatrix (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d)) g (I m) (J m) := by
  unfold toEndMatrix
  rw [LinearMap.toMatrix_apply]
  unfold diagAction tensorBasis
  simp +decide [PiTensorProduct.map_tprod, Basis.piTensorProduct_apply]

/-
For a diagonal `g` with entries `f`, `g^{⊗k}` is diagonal with entries `∏ f(I(m))`.
-/
theorem diagAction_diagonal (f : Fin d → ℂ) (I J : Fin k → Fin d) :
    toEndMatrix d k (diagAction d k (LinearMap.pi (fun i => f i • LinearMap.proj i))) I J =
    if I = J then ∏ m : Fin k, f (I m) else 0 := by
  rw [ toEndMatrix_diagAction ];
  split_ifs <;> simp_all +decide [ Finset.prod_eq_zero_iff, Pi.single_apply ];
  grind

end ForMathlib.Tensor
