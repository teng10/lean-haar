/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic

import LeanHaar.ForMathlib.TensorPower

/-!
# Matrix coordinates for tensor-power operators

The standard tensor basis `tensorBasis` is indexed by functions `Fin k → Fin d`.
The linear equivalence `toEndMatrix` identifies endomorphisms of the tensor power
with matrices in this basis, with rows indexing output coefficients and columns
indexing input basis vectors.

The computation rules describe permutation operators, tensor powers of arbitrary
endomorphisms, and tensor powers of diagonal endomorphisms. This coordinate API is
shared by the centralizer proofs, Haar integration, and Weingarten vectorization.
It does not depend on Schur–Weyl duality or the double-centralizer theorem.
-/

noncomputable section

open scoped TensorProduct

namespace SchurWeyl

variable {d k : ℕ}

/-- The standard tensor basis, indexed by `I : Fin k → Fin d`. Its vector at `I` is
the elementary tensor whose factor at `m` is the standard basis vector at `I m`. -/
def tensorBasis (d k : ℕ) :
    Module.Basis ((i : Fin k) → Fin d) ℂ (TensV d k) :=
  Basis.piTensorProduct (fun (_ : Fin k) => Pi.basisFun ℂ (Fin d))

/-- The tensor power is finite-dimensional, witnessed by its standard tensor basis. -/
instance tensV_module_finite (d k : ℕ) : Module.Finite ℂ (TensV d k) :=
  Module.Finite.of_basis (tensorBasis d k)

/-- Matrix coordinates in `tensorBasis`. Entry `(I, J)` is the coefficient of the
basis vector at `I` in the image of the basis vector at `J`. The inverse converts
a matrix back to an endomorphism with these coordinates. -/
def toEndMatrix (d k : ℕ) :
    Module.End ℂ (TensV d k) ≃ₗ[ℂ]
    Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
  LinearMap.toMatrix (tensorBasis d k) (tensorBasis d k)

/-- `W_σ(e_I) = e_{I ∘ σ⁻¹}`. -/
theorem permAction_tensorBasis (σ : Equiv.Perm (Fin k)) (I : Fin k → Fin d) :
    (permAction d k σ) (tensorBasis d k I) = tensorBasis d k (I ∘ σ.symm) := by
  unfold permAction; simp +decide [tensorBasis]

/-- Matrix of `W_σ`. -/
theorem toEndMatrix_permAction (σ : Equiv.Perm (Fin k)) (I J : Fin k → Fin d) :
    toEndMatrix d k ((permAction d k σ).toLinearMap) I J =
    if I = J ∘ σ.symm then 1 else 0 := by
  convert LinearMap.toMatrix_apply (tensorBasis d k) (tensorBasis d k)
    ((permAction d k σ).toLinearMap) I J using 1
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

/-- For a diagonal `g` with entries `f`, `g^{⊗k}` is diagonal with entries `∏ f(I(m))`. -/
theorem diagAction_diagonal (f : Fin d → ℂ) (I J : Fin k → Fin d) :
    toEndMatrix d k (diagAction d k (LinearMap.pi (fun i => f i • LinearMap.proj i))) I J =
    if I = J then ∏ m : Fin k, f (I m) else 0 := by
  rw [ toEndMatrix_diagAction ];
  split_ifs <;> simp_all +decide [ Finset.prod_eq_zero_iff, Pi.single_apply ];
  grind

end SchurWeyl

end
