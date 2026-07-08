/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aesop
import Mathlib.Tactic

import LeanHaar.ForMathlib.Defs
import LeanHaar.ForMathlib.Commutation
import LeanHaar.ForMathlib.SmallDim

/-!
# Hard direction of Schur-Weyl duality

We prove: if `X ∈ End(V^{⊗k})` commutes with all `g^{⊗k}`, then `X ∈ Span{W_σ}`.

The proof is uniform in `d` and `k`: it goes through the First Fundamental Theorem
(`centralizer_permImage_le_span_diagImage`) together with the Double Commutant Theorem
(`double_centralizer_permImage`), both established in `SmallDim.lean` and `DCT.lean`.
This file also collects the standard-basis matrix descriptions of the permutation and
diagonal operators that the downstream Haar/Weingarten development relies on.
-/

noncomputable section

open scoped TensorProduct

namespace SchurWeyl

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

/-- For a diagonal `g` with entries `f`, `g^{⊗k}` is diagonal with entries `∏ f(I(m))`. -/
theorem diagAction_diagonal (f : Fin d → ℂ) (I J : Fin k → Fin d) :
    toEndMatrix d k (diagAction d k (LinearMap.pi (fun i => f i • LinearMap.proj i))) I J =
    if I = J then ∏ m : Fin k, f (I m) else 0 := by
  rw [ toEndMatrix_diagAction ];
  split_ifs <;> simp_all +decide [ Finset.prod_eq_zero_iff, Pi.single_apply ];
  grind

/-! ### Hard direction -/

/-- **Hard direction of Schur-Weyl**: `centralizer(diagImage) ⊆ Span(permImage)`.

This holds for all `d` and `k`. The proof is the Double Commutant argument: by the
First Fundamental Theorem every operator commuting with all `W_σ` lies in
`Span(diagImage)`, and the Double Commutant Theorem then identifies the double
centralizer of `Span(permImage)` with `Span(permImage)` itself. -/
theorem centralizer_diagImage_le_span_permImage :
    (diagImage d k).centralizer ⊆
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) :=
  centralizer_diagImage_le_span_permImage_small

end SchurWeyl

end
