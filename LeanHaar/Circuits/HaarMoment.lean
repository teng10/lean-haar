/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.SupportingDocs.VectorizedHaar
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Haar moments of unitary gates

`haarMoment d k` is the Haar average on the existing vectorized operator space.
`gateMoment J k` averages a local Haar gate placed by a continuous group
homomorphism `J`. Both APIs work for every copy number, without a stable-range
assumption or a choice of permutation basis.

Multiplication of moment operators means composition: `B * A` applies `A` first.
The adjoint is for the Hilbert–Schmidt inner product represented by `endVec`;
it is distinct from complete positivity of a quantum channel.
-/

noncomputable section

open MeasureTheory
open scoped Matrix

namespace SchurWeyl.Circuits

/-- Matrix entries of an operator on `k` copies, with the Hilbert–Schmidt norm. -/
abbrev MomentSpace (d k : ℕ) :=
  EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d))

/-- A continuous linear superoperator on the vectorized `k`-copy register. -/
abbrev MomentOperator (d k : ℕ) := MomentSpace d k →L[ℂ] MomentSpace d k

/-- The `k`-copy Haar twirl, as a composable continuous linear operator. -/
def haarMoment (d k : ℕ) : MomentOperator d k :=
  ∫ U, vecActOn (k := k) U ∂haarProb d

/-- Average a local Haar unitary placed in a larger register by `J`. -/
def gateMoment {d D : ℕ}
    (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ) (k : ℕ) :
    MomentOperator D k :=
  ∫ U, vecActOn (k := k) (J U) ∂haarProb d

variable {d D k : ℕ}

private theorem integral_comp_left {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → MomentOperator d k} {T : MomentOperator d k}
    (hf : Integrable f μ) : (∫ x, T * f x ∂μ) = T * ∫ x, f x ∂μ :=
  (ContinuousLinearMap.compL ℂ (MomentSpace d k) (MomentSpace d k)
    (MomentSpace d k) T).integral_comp_comm hf

private theorem integral_comp_right {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → MomentOperator d k} {T : MomentOperator d k}
    (hf : Integrable f μ) : (∫ x, f x * T ∂μ) = (∫ x, f x ∂μ) * T :=
  ((ContinuousLinearMap.compL ℂ (MomentSpace d k) (MomentSpace d k)
    (MomentSpace d k)).flip T).integral_comp_comm hf

/-- Placing a Haar gate by the identity homomorphism recovers the global moment. -/
@[simp] theorem gateMoment_id :
    gateMoment (ContinuousMonoidHom.id (Matrix.unitaryGroup (Fin d) ℂ)) k = haarMoment d k := rfl

/-- The bundled Haar moment agrees with the original tensor-power moment. -/
@[simp] theorem haarMoment_endVec (X : Module.End ℂ (TensV d k)) :
    haarMoment d k (endVec X) = endVec (momentOp X) :=
  integral_vecActOn_endVec X

/-- Placed Haar conjugations are Bochner integrable. -/
theorem integrable_gateAction (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ) :
    Integrable (fun U => vecActOn (k := k) (J U)) (haarProb d) :=
  (continuous_vecActOn.comp J.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Applying the local moment agrees with averaging the physical placed gate,
including on input operators entangled with the complement. -/
theorem gateMoment_endVec (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ)
    (X : Module.End ℂ (TensV D k)) :
    gateMoment J k (endVec X) =
      ∫ U, endVec (actOn X (J U)) ∂haarProb d := by
  rw [gateMoment, ContinuousLinearMap.integral_apply (integrable_gateAction (k := k) J)]
  simp only [vecActOn_endVec]

/-- A placed deterministic gate fixes the output of the corresponding local twirl. -/
@[simp] theorem vecActOn_mul_gateMoment
    (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    vecActOn (k := k) (J U) * gateMoment J k = gateMoment J k :=
  ((vecActOnHom D k).comp J).mul_integral_eq (haarProb d) U

/-- A local twirl absorbs a deterministic gate on the same placed subsystem. -/
@[simp] theorem gateMoment_mul_vecActOn
    (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    gateMoment J k * vecActOn (k := k) (J U) = gateMoment J k :=
  ((vecActOnHom D k).comp J).integral_mul_eq (haarProb d) U

/-- Every placed Haar twirl is idempotent. -/
@[simp] theorem gateMoment_mul_self
    (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ) :
    gateMoment J k * gateMoment J k = gateMoment J k :=
  ((vecActOnHom D k).comp J).integral_mul_self_eq (haarProb d)

/-- Every placed Haar twirl is self-adjoint. -/
@[simp] theorem gateMoment_adjoint
    (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ) :
    (gateMoment J k).adjoint = gateMoment J k := by
  rw [gateMoment, adjoint_integral_vecActOn (integrable_gateAction (k := k) J)]
  have hs (U : Matrix.unitaryGroup (Fin d) ℂ) : star (J U) = J (U⁻¹) := by
    rw [Unitary.star_eq_inv, map_inv]
  simp_rw [hs]
  exact integral_inv_eq_self (fun U => vecActOn (k := k) (J U)) (haarProb d)

/-- Every deterministic unitary conjugation fixes the output of the Haar twirl. -/
@[simp] theorem vecActOn_mul_haarMoment (U : Matrix.unitaryGroup (Fin d) ℂ) :
    vecActOn (k := k) U * haarMoment d k = haarMoment d k :=
  vecActOn_mul_gateMoment (ContinuousMonoidHom.id _) U

/-- Haar averaging absorbs a deterministic conjugation at its input. -/
@[simp] theorem haarMoment_mul_vecActOn (U : Matrix.unitaryGroup (Fin d) ℂ) :
    haarMoment d k * vecActOn (k := k) U = haarMoment d k :=
  gateMoment_mul_vecActOn (ContinuousMonoidHom.id _) U

/-- Haar averaging is idempotent. -/
@[simp] theorem haarMoment_mul_self : haarMoment d k * haarMoment d k = haarMoment d k :=
  gateMoment_mul_self (ContinuousMonoidHom.id _)

/-- Haar averaging is self-adjoint in the Hilbert–Schmidt inner product. -/
@[simp] theorem haarMoment_adjoint : (haarMoment d k).adjoint = haarMoment d k :=
  gateMoment_adjoint (ContinuousMonoidHom.id _)

/-- Global Haar averaging absorbs any local Haar twirl at its input. -/
@[simp] theorem haarMoment_mul_gateMoment
    (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ) :
    haarMoment D k * gateMoment J k = haarMoment D k := by
  unfold gateMoment
  rw [← integral_comp_left (integrable_gateAction (k := k) J)]
  simp

/-- A local Haar twirl fixes the output of global Haar averaging. -/
@[simp] theorem gateMoment_mul_haarMoment
    (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ) :
    gateMoment J k * haarMoment D k = haarMoment D k := by
  unfold gateMoment
  rw [← integral_comp_right (integrable_gateAction (k := k) J)]
  simp

end SchurWeyl.Circuits
