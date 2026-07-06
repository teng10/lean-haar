/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.GroupTheory.Perm.Basic


/-!
# Schur-Weyl Duality: Definitions

This file sets up the basic definitions for the Schur-Weyl duality theorem
using the double commutant approach.

## Main definitions

* `SchurWeyl.permAction` - The permutation action of `S_k` on `V^{⊗k}`
* `SchurWeyl.diagAction` - The diagonal action of `End(V)` on `V^{⊗k}`
* `SchurWeyl.permImage` - The set of permutation operators in `End(V^{⊗k})`
* `SchurWeyl.diagImage` - The set of diagonal operators in `End(V^{⊗k})`

## References

* [J. Watrous, *The Theory of Quantum Information*][watrous2018]
-/

noncomputable section

open scoped TensorProduct

variable {d : ℕ} {k : ℕ}

namespace ForMathlib.Tensor

namespace SchurWeyl

/-- The `k`-fold tensor power of `ℂ^d`, defined as `⨂[ℂ] (i : Fin k), (Fin d → ℂ)`. -/
abbrev TensV (d k : ℕ) : Type :=
  PiTensorProduct ℂ (fun (_ : Fin k) => (Fin d → ℂ))

/-- The permutation operator `W_σ` on the tensor power `V^{⊗k}`.
Given `σ : Equiv.Perm (Fin k)`, this acts by permuting the tensor factors:
`W_σ (v₁ ⊗ ⋯ ⊗ vₖ) = v_{σ⁻¹(1)} ⊗ ⋯ ⊗ v_{σ⁻¹(k)}`. -/
def permAction (d : ℕ) {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    TensV d k ≃ₗ[ℂ] TensV d k :=
  PiTensorProduct.reindex ℂ (fun (_ : Fin k) => (Fin d → ℂ)) σ

/-- The diagonal action `g^{⊗k}` on the tensor power `V^{⊗k}`.
Given `g : End(V)`, this acts as `g` on each tensor factor:
`g^{⊗k} (v₁ ⊗ ⋯ ⊗ vₖ) = g(v₁) ⊗ ⋯ ⊗ g(vₖ)`. -/
def diagAction (d k : ℕ) (g : Module.End ℂ (Fin d → ℂ)) :
    Module.End ℂ (TensV d k) :=
  PiTensorProduct.map (fun (_ : Fin k) => g)

/-- The set of permutation operators in `End(V^{⊗k})`. -/
def permImage (d k : ℕ) : Set (Module.End ℂ (TensV d k)) :=
  Set.range (fun σ : Equiv.Perm (Fin k) => (permAction d σ).toLinearMap)

/-- The set of diagonal operators `{g^{⊗k} | g ∈ End(V)}` in `End(V^{⊗k})`. -/
def diagImage (d k : ℕ) : Set (Module.End ℂ (TensV d k)) :=
  Set.range (fun g : Module.End ℂ (Fin d → ℂ) => diagAction d k g)

/-- Behavior of `permAction` on elementary tensors. -/
theorem permAction_tprod (σ : Equiv.Perm (Fin k)) (v : Fin k → (Fin d → ℂ)) :
    permAction d σ (PiTensorProduct.tprod ℂ v) =
    PiTensorProduct.tprod ℂ (fun i => v (σ.symm i)) :=
  PiTensorProduct.reindex_tprod σ v

/-- Behavior of `diagAction` on elementary tensors. -/
theorem diagAction_tprod (g : Module.End ℂ (Fin d → ℂ)) (v : Fin k → (Fin d → ℂ)) :
    diagAction d k g (PiTensorProduct.tprod ℂ v) =
    PiTensorProduct.tprod ℂ (fun i => g (v i)) :=
  PiTensorProduct.map_tprod _ v

end SchurWeyl

end ForMathlib.Tensor

end
