/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TraceNotation

/-!
# The isotropic (depolarizing) channel and its inverse

This file studies the isotropic channel `X ↦ (Tr(X) I + X)/(δ + 1)` on the endomorphisms of a
module over an arbitrary field, and inverts it explicitly. It is the algebraic content of
Observation 59 of `classical_shadows.tex`; the identification of `δ` with the dimension `d`
and of the channel with the measurement channel of the Haar-random classical-shadow protocol
is carried out in `LeanHaar.ForMathlib.Examples.ClassicalShadows.SimplifiedMeasChannel`.

## Main definitions

* `ClassicalShadows.depolarizingChannel`: the isotropic channel `X ↦ (Tr(X) I + X)/(δ + 1)`.
* `ClassicalShadows.depolarizingChannelInv`: the candidate inverse `X ↦ (δ + 1) X - Tr(X) I`.
* `ClassicalShadows.depolarizingChannelEquiv`: the channel as a linear equivalence.

## Main results

* `ClassicalShadows.depolarizingChannelInv_comp`,
  `ClassicalShadows.depolarizingChannel_comp_inv`: the two inversion identities, whose only
  dimension-dependent input is `Tr(I) = δ`.
-/

noncomputable section

namespace ClassicalShadows

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

variable (δ : 𝕜)

/-- The isotropic measurement channel `X ↦ (Tr(X) I + X)/(δ + 1)`. -/
def depolarizingChannel : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V :=
  (δ + 1)⁻¹ • ((LinearMap.trace 𝕜 V).smulRight LinearMap.id) + (δ + 1)⁻¹ • LinearMap.id

@[simp]
theorem depolarizingChannel_apply (X : Module.End 𝕜 V) :
    depolarizingChannel (V := V) δ X = (δ + 1)⁻¹ • (Tr[X] • LinearMap.id + X) := by
  simp only [depolarizingChannel, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.id_apply, smul_add]

/-- The candidate inverse `X ↦ (δ + 1) X - Tr(X) I` of the isotropic channel. -/
def depolarizingChannelInv : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V :=
  (δ + 1) • LinearMap.id - (LinearMap.trace 𝕜 V).smulRight LinearMap.id

@[simp]
theorem depolarizingChannelInv_apply (X : Module.End 𝕜 V) :
    depolarizingChannelInv (V := V) δ X = (δ + 1) • X - Tr[X] • LinearMap.id := rfl

variable (hδ : Tr[(LinearMap.id : Module.End 𝕜 V)] = δ) (hδ1 : δ + 1 ≠ 0)

include hδ hδ1

/-- `X ↦ (δ + 1) X - Tr(X) I` is a left inverse of the isotropic channel. The only
dimension-dependent input is `Tr(I) = δ`. -/
theorem depolarizingChannelInv_comp :
    depolarizingChannelInv (V := V) δ ∘ₗ depolarizingChannel (V := V) δ = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  simp only [LinearMap.comp_apply, depolarizingChannel_apply, depolarizingChannelInv_apply,
    map_smul, map_add, hδ, LinearMap.id_apply]
  match_scalars
  · ring
  · rw [mul_one, inv_mul_cancel₀ hδ1]

/-- `X ↦ (δ + 1) X - Tr(X) I` is a right inverse of the isotropic channel. -/
theorem depolarizingChannel_comp_inv :
    depolarizingChannel (V := V) δ ∘ₗ depolarizingChannelInv (V := V) δ = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  simp only [LinearMap.comp_apply, depolarizingChannel_apply, depolarizingChannelInv_apply,
    map_sub, map_smul, hδ, LinearMap.id_apply]
  match_scalars
  · ring
  · rw [mul_one, mul_inv_cancel₀ hδ1]

/-- The isotropic measurement channel as a linear equivalence. -/
def depolarizingChannelEquiv : Module.End 𝕜 V ≃ₗ[𝕜] Module.End 𝕜 V :=
  LinearEquiv.ofLinear (depolarizingChannel (V := V) δ) (depolarizingChannelInv (V := V) δ)
    (depolarizingChannel_comp_inv δ hδ hδ1) (depolarizingChannelInv_comp δ hδ hδ1)

end ClassicalShadows
