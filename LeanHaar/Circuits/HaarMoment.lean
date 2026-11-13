/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.WeingartenInverse
import LeanHaar.SupportingDocs.HaarInvariance
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Haar moments of unitary gates

`vecActOn` is the existing tensor-power conjugation on matrix entries, with its continuous
homomorphism `vecActOnHom`.
`operatorMap` converts these vectorized operators back to ordinary endomorphisms.

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
open scoped Matrix Kronecker

namespace SchurWeyl.Circuits

/-- Matrix entries of an operator on `k` copies, with the Hilbert–Schmidt norm. -/
abbrev MomentSpace (d k : ℕ) :=
  EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d))

/-- A continuous linear superoperator on the vectorized `k`-copy register. -/
abbrev MomentOperator (d k : ℕ) := MomentSpace d k →L[ℂ] MomentSpace d k

end SchurWeyl.Circuits

namespace SchurWeyl

open Circuits (MomentSpace MomentOperator)

variable {d k : ℕ}

/-- Conjugation by `U^{⊗k}`, acting on vectorized operators. -/
def vecActOn (U : Matrix.unitaryGroup (Fin d) ℂ) :
    MomentOperator d k :=
  (Matrix.toEuclideanLin (fun p q =>
    (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.1 c) (q.1 c)) *
      star (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.2 c) (q.2 c)))).toContinuousLinearMap

/-- The coordinate construction is exactly the existing tensor-power conjugation. -/
theorem vecActOn_endVec (U : Matrix.unitaryGroup (Fin d) ℂ)
    (X : Module.End ℂ (TensV d k)) :
    vecActOn U (endVec X) = endVec (actOn X U) := by
  let A : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
    fun I J => ∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (I c) (J c)
  have hU : toEndMatrix d k (diagAction d k (endOf (U : Matrix (Fin d) (Fin d) ℂ))) = A := by
    ext I J
    simp only [toEndMatrix_diagAction, endOf, LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin', A]
  have hstar : (toEndMatrix d k (diagAction d k
      (endOf (star (U : Matrix (Fin d) (Fin d) ℂ))))).transpose = A.map star := by
    ext I J
    simp only [Matrix.transpose_apply, toEndMatrix_diagAction, endOf,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.star_apply,
      Matrix.map_apply, A, star_prod]
  -- Mathlib vectorizes by (column, row), while endVec uses (row, column).
  apply (WithLp.equiv 2 _).injective
  change (A ⊗ₖ A.map star) *ᵥ (toEndMatrix d k X).transpose.vec =
    (toEndMatrix d k (actOn X U)).transpose.vec
  rw [Matrix.kronecker_mulVec_vec, actOn, toEndMatrix_comp, toEndMatrix_comp]
  simp only [Matrix.transpose_mul, hU, hstar, Matrix.mul_assoc]

/-- Multiplication of sampled gates becomes composition of their conjugation maps. -/
theorem vecActOn_mul (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    vecActOn (k := k) (U * V) = (vecActOn U).comp (vecActOn V) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨X, rfl⟩ := (endVecEquiv d k).surjective x
  change vecActOn (U * V) (endVec X) = vecActOn U (vecActOn V (endVec X))
  rw [vecActOn_endVec, vecActOn_endVec, vecActOn_endVec]
  exact congrArg endVec (conj_actOn X U V).symm

/-- The identity unitary acts as the identity superoperator. -/
@[simp] theorem vecActOn_one : vecActOn (d := d) (k := k) 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨X, rfl⟩ := (endVecEquiv d k).surjective x
  change vecActOn (d := d) (k := k) 1 (endVec X) = endVec X
  rw [vecActOn_endVec]
  have hid : diagAction d k LinearMap.id = LinearMap.id := map_one (diagAction d k)
  simp [actOn, endOf_one, hid]

/-- Adjoint conjugation is conjugation by the inverse unitary. -/
@[simp] theorem vecActOn_adjoint (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (vecActOn (k := k) U).adjoint = vecActOn (k := k) (star U) := by
  unfold vecActOn
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 2
  ext p q
  simp only [_root_.Unitary.coe_star, Matrix.star_apply, Matrix.conjTranspose_apply, star_mul, star_star, star_prod]
  ring

/-- Vectorized conjugation varies continuously with the sampled unitary. -/
theorem continuous_vecActOn : Continuous (vecActOn (d := d) (k := k)) := by
  let T := ((Matrix.toEuclideanLin (𝕜 := ℂ)
    (m := (Fin k → Fin d) × (Fin k → Fin d))
    (n := (Fin k → Fin d) × (Fin k → Fin d))).trans
      LinearMap.toContinuousLinearMap).toLinearMap
  change Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => T
    (fun p q => (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.1 c) (q.1 c)) *
      star (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.2 c) (q.2 c))))
  apply T.continuous_of_finiteDimensional.comp
  have hm : Continuous (fun U : Matrix (Fin d) (Fin d) ℂ =>
      fun p q : (Fin k → Fin d) × (Fin k → Fin d) =>
        (∏ c, U (p.1 c) (q.1 c)) * star (∏ c, U (p.2 c) (q.2 c))) :=
    continuous_pi fun _ => continuous_pi fun _ => by fun_prop
  exact hm.comp continuous_subtype_val

/-- Vectorized conjugation with its composition and continuity laws. -/
def vecActOnHom (d k : ℕ) : Matrix.unitaryGroup (Fin d) ℂ →ₜ*
    (MomentOperator d k) where
  toFun := vecActOn
  map_one' := vecActOn_one
  map_mul' := vecActOn_mul
  continuous_toFun := continuous_vecActOn

/-- The adjoint of an averaged conjugation averages the inverse conjugations. -/
theorem adjoint_integral_vecActOn {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {L : α → Matrix.unitaryGroup (Fin d) ℂ}
    (hi : Integrable (fun a => vecActOn (k := k) (L a)) μ) :
    (∫ a, vecActOn (k := k) (L a) ∂μ).adjoint =
      ∫ a, vecActOn (k := k) (star (L a)) ∂μ := by
  let A := (ContinuousLinearMap.adjoint (𝕜 := ℂ)
    (E := MomentSpace d k)
    (F := MomentSpace d k)).toContinuousLinearEquiv
      |>.toContinuousLinearMap
  have h := ContinuousLinearMap.integral_comp_commSL (by simp) A hi
  change (∫ a, (vecActOn (k := k) (L a)).adjoint ∂μ) =
    (∫ a, vecActOn (k := k) (L a) ∂μ).adjoint at h
  rw [← h]
  simp_rw [vecActOn_adjoint]

/-- A continuous operator-valued function on the compact unitary group is integrable. -/
theorem integrable_vecActOn : Integrable (vecActOn (d := d) (k := k)) (haarProb d) :=
  continuous_vecActOn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Averaging vectorized conjugation computes the existing Haar moment operator. -/
theorem integral_vecActOn_endVec (X : Module.End ℂ (TensV d k)) :
    (∫ U, vecActOn U ∂haarProb d) (endVec X) = endVec (momentOp X) := by
  ext p
  rw [ContinuousLinearMap.integral_apply integrable_vecActOn,
    eval_integral_piLp (fun i => (integrable_vecActOn.apply_continuousLinearMap _).eval_piLp i)]
  simp only [vecActOn_endVec]
  change (∫ U, toEndMatrix d k (actOn X U) p.1 p.2 ∂haarProb d) =
    toEndMatrix d k (momentOp X) p.1 p.2
  rw [toEndMatrix_momentOp]
  rfl

end SchurWeyl

namespace SchurWeyl.Circuits

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

/-- Express a vectorized superoperator as a linear map on ordinary operators. -/
def operatorMap {d k : ℕ} (T : MomentOperator d k) :
    Module.End ℂ (TensV d k) →ₗ[ℂ] Module.End ℂ (TensV d k) :=
  (endVecEquiv d k).symm.toLinearMap.comp
    (T.toLinearMap.comp (endVecEquiv d k).toLinearMap)

@[simp] theorem endVec_operatorMap {d k : ℕ} (T : MomentOperator d k)
    (X : Module.End ℂ (TensV d k)) :
    endVec (operatorMap T X) = T (endVec X) :=
  (endVecEquiv d k).apply_symm_apply _

set_option maxRecDepth 1024 in
/-- Matrix entries can be read directly from the vectorized result. -/
theorem toEndMatrix_operatorMap {d k : ℕ} (T : MomentOperator d k)
    (X : Module.End ℂ (TensV d k)) (i j : Fin k → Fin d) :
    toEndMatrix d k (operatorMap T X) i j = T (endVec X) (i, j) :=
  congrArg (fun v : MomentSpace d k => v (i, j)) (endVec_operatorMap T X)

@[simp] theorem operatorMap_haarMoment {d k : ℕ} (X : Module.End ℂ (TensV d k)) :
    operatorMap (haarMoment d k) X = momentOp X := by
  apply (endVecEquiv d k).injective
  exact (endVec_operatorMap _ _).trans (haarMoment_endVec X)

open InnerProductSpace ContinuousLinearMap in
/-- The Haar moment as a Weingarten sum of rank-one operators on permutation kets. -/
theorem haarMoment_eq_weingarten_sum {d k : ℕ} (h : k ≤ d) :
    haarMoment d k =
      ∑ σ : Equiv.Perm (Fin k), ∑ π : Equiv.Perm (Fin k),
        (weingartenGram d k)⁻¹ σ π •
          rankOne ℂ (endVec (permOp d σ)) (endVec (permOp d π)) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨X, rfl⟩ := (endVecEquiv d k).surjective x
  have hX : (endVecEquiv d k) X = endVec X := rfl
  rw [hX, haarMoment_endVec]
  obtain ⟨c, hmom, hsys⟩ := weingarten_moment_haar X
  have hc : c = (weingartenGram d k)⁻¹ *ᵥ weingartenVec d k X :=
    weingarten_solution_eq_inv h X c hsys
  have hlin : endVec (momentOp X) = ∑ σ : Equiv.Perm (Fin k), c σ • endVec (permOp d σ) := by
    rw [← endVecₗ_apply, hmom]
    simp only [map_sum, map_smul, endVecₗ_apply]
  rw [hlin, hc]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, rankOne_apply,
    smul_smul, inner_endVec_perm_eq_trace, Matrix.mulVec, dotProduct, weingartenVec,
    Finset.sum_smul]

end SchurWeyl.Circuits
