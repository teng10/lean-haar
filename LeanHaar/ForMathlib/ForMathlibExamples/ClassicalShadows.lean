/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

/-!
# Classical shadows

This file formalizes the algebraic content of Observations 58 and 59 in
`classical_shadows.tex`. The probability space is represented by a finite weighted family
of snapshots. This separates the classical-shadow argument from the particular ensemble
used to produce the snapshots; Haar integration supplies the relevant moment identities.

The statements are over an arbitrary field and finite free module whenever no specifically
complex or analytic input is required.
-/

noncomputable section

namespace ClassicalShadows

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Fintype ι] [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V]

/-- A finite weighted family of classical snapshots. Positivity and normalization of the
weights are irrelevant to the algebraic moment identities, so they are not imposed here. -/
structure SnapshotEnsemble where
  weight : ι → 𝕜
  snapshot : ι → Module.End 𝕜 V

namespace SnapshotEnsemble

variable (E : SnapshotEnsemble (𝕜 := 𝕜) (V := V) (ι := ι))

/-- Born weight of an outcome, including the prior weight of that outcome. -/
def outcomeWeight (ρ : Module.End 𝕜 V) (x : ι) : 𝕜 :=
  E.weight x * LinearMap.trace 𝕜 V (ρ ∘ₗ E.snapshot x)

/-- The measurement channel associated to a finite snapshot ensemble. -/
def measurementChannel : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V where
  toFun ρ := ∑ x, E.outcomeWeight ρ x • E.snapshot x
  map_add' ρ σ := by
    simp only [outcomeWeight, LinearMap.add_comp, map_add, mul_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' c ρ := by
    simp only [outcomeWeight, LinearMap.smul_comp, map_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [smul_smul, RingHom.id_apply]
    congr 1
    simp only [smul_eq_mul]
    ring

omit [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp]
theorem measurementChannel_apply (ρ : Module.End 𝕜 V) :
    E.measurementChannel ρ = ∑ x, E.outcomeWeight ρ x • E.snapshot x := rfl

/-- The scalar contraction of the third snapshot moment against three operators. -/
def thirdMoment (A B C : Module.End 𝕜 V) : 𝕜 :=
  ∑ x, E.weight x * LinearMap.trace 𝕜 V (A ∘ₗ E.snapshot x) *
    LinearMap.trace 𝕜 V (B ∘ₗ E.snapshot x) *
    LinearMap.trace 𝕜 V (C ∘ₗ E.snapshot x)

/-- The classical-shadow state estimator associated to an invertible measurement channel. -/
def stateEstimator (hM : Function.Bijective E.measurementChannel) (x : ι) : Module.End 𝕜 V :=
  (LinearEquiv.ofBijective E.measurementChannel hM).symm (E.snapshot x)

omit [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- The classical-shadow estimator is unbiased. -/
theorem mean_estimator (hM : Function.Bijective E.measurementChannel) (ρ : Module.End 𝕜 V) :
    ∑ x, E.outcomeWeight ρ x • E.stateEstimator hM x = ρ := by
  let e := LinearEquiv.ofBijective E.measurementChannel hM
  calc
    ∑ x, E.outcomeWeight ρ x • E.stateEstimator hM x =
        e.symm (∑ x, E.outcomeWeight ρ x • E.snapshot x) := by
          simp only [map_sum, map_smul, stateEstimator, e]
    _ = e.symm (E.measurementChannel ρ) := by rw [measurementChannel_apply]
    _ = ρ := e.symm_apply_apply ρ

/-- Observable evaluated on a classical-shadow state estimator. -/
def observableEstimator (hM : Function.Bijective E.measurementChannel)
    (O : Module.End 𝕜 V) (x : ι) : 𝕜 :=
  LinearMap.trace 𝕜 V (O ∘ₗ E.stateEstimator hM x)

omit [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- Observation 58: the second moment of the scalar estimator is a contraction of the
third snapshot moment. The displayed adjointness assumption is exactly the trace
self-adjointness of the inverse measurement channel used in the paper. -/
theorem estimator_secondMoment (hM : Function.Bijective E.measurementChannel)
    (hself : ∀ A B : Module.End 𝕜 V,
      LinearMap.trace 𝕜 V
          (A ∘ₗ (LinearEquiv.ofBijective E.measurementChannel hM).symm B) =
        LinearMap.trace 𝕜 V
          ((LinearEquiv.ofBijective E.measurementChannel hM).symm A ∘ₗ B))
    (ρ O : Module.End 𝕜 V) :
    ∑ x, E.outcomeWeight ρ x * (E.observableEstimator hM O x) ^ 2 =
      E.thirdMoment ρ
        ((LinearEquiv.ofBijective E.measurementChannel hM).symm O)
        ((LinearEquiv.ofBijective E.measurementChannel hM).symm O) := by
  simp only [outcomeWeight, observableEstimator, stateEstimator, thirdMoment]
  apply Finset.sum_congr rfl
  intro x _
  rw [hself O (E.snapshot x)]
  ring

end SnapshotEnsemble

section Isotropic

variable (δ : 𝕜)

/-- The isotropic measurement channel `X ↦ (Tr(X) I + X)/(δ+1)`. -/
def depolarizingChannel : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V :=
  (δ + 1)⁻¹ • ((LinearMap.trace 𝕜 V).smulRight LinearMap.id) +
    (δ + 1)⁻¹ • LinearMap.id

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp]
theorem depolarizingChannel_apply (X : Module.End 𝕜 V) :
    depolarizingChannel (V := V) δ X =
      (δ + 1)⁻¹ • (LinearMap.trace 𝕜 V X • LinearMap.id + X) := by
  simp only [depolarizingChannel, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.id_apply, smul_add]

/-- Candidate inverse to the isotropic measurement channel. -/
def depolarizingChannelInv : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V :=
  (δ + 1) • LinearMap.id - (LinearMap.trace 𝕜 V).smulRight LinearMap.id

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp]
theorem depolarizingChannelInv_apply (X : Module.End 𝕜 V) :
    depolarizingChannelInv (V := V) δ X =
      (δ + 1) • X - LinearMap.trace 𝕜 V X • LinearMap.id := by
  rfl

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- Observation 59: `X ↦ (δ+1)X-Tr(X)I` is a left inverse of the isotropic channel.
The only dimension-dependent input is `Tr(I)=δ`. -/
theorem depolarizingChannelInv_comp (hδ : LinearMap.trace 𝕜 V LinearMap.id = δ)
    (hδ1 : δ + 1 ≠ 0) :
    depolarizingChannelInv (V := V) δ ∘ₗ depolarizingChannel (V := V) δ = LinearMap.id := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, depolarizingChannel_apply, depolarizingChannelInv_apply,
    map_smul, map_add, hδ, LinearMap.id_apply]
  have hinv : (δ + 1)⁻¹ * (δ + 1) = 1 := inv_mul_cancel₀ hδ1
  have hinv' : (δ + 1) * (δ + 1)⁻¹ = 1 := mul_inv_cancel₀ hδ1
  have hcoeff : δ * (1 + δ)⁻¹ + (1 + δ)⁻¹ = 1 := by
    calc
      δ * (1 + δ)⁻¹ + (1 + δ)⁻¹ = (δ + 1) * (δ + 1)⁻¹ := by ring
      _ = 1 := hinv'
  match_scalars
  all_goals simp only [mul_one, hinv]
  all_goals field_simp [hδ1]; ring

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- The candidate is also a right inverse. -/
theorem depolarizingChannel_comp_inv (hδ : LinearMap.trace 𝕜 V LinearMap.id = δ)
    (hδ1 : δ + 1 ≠ 0) :
    depolarizingChannel (V := V) δ ∘ₗ depolarizingChannelInv (V := V) δ = LinearMap.id := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, depolarizingChannel_apply, depolarizingChannelInv_apply,
    map_sub, map_smul, hδ, LinearMap.id_apply]
  have hinv : (δ + 1)⁻¹ * (δ + 1) = 1 := inv_mul_cancel₀ hδ1
  have hinv' : (δ + 1) * (δ + 1)⁻¹ = 1 := mul_inv_cancel₀ hδ1
  have hcoeff : δ * (1 + δ)⁻¹ + (1 + δ)⁻¹ = 1 := by
    calc
      δ * (1 + δ)⁻¹ + (1 + δ)⁻¹ = (δ + 1) * (δ + 1)⁻¹ := by ring
      _ = 1 := hinv'
  match_scalars
  all_goals simp only [mul_one, hinv']
  all_goals field_simp [hδ1]; ring

/-- The simplified Haar measurement channel is invertible, with the inverse stated in
Observation 59. -/
def depolarizingChannelEquiv (hδ : LinearMap.trace 𝕜 V LinearMap.id = δ)
    (hδ1 : δ + 1 ≠ 0) : Module.End 𝕜 V ≃ₗ[𝕜] Module.End 𝕜 V :=
  LinearEquiv.ofLinear (depolarizingChannel (V := V) δ)
    (depolarizingChannelInv (V := V) δ)
    (depolarizingChannel_comp_inv δ hδ hδ1)
    (depolarizingChannelInv_comp δ hδ hδ1)

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp]
theorem depolarizingChannel_inverse (hδ : LinearMap.trace 𝕜 V LinearMap.id = δ)
    (hδ1 : δ + 1 ≠ 0) (X : Module.End 𝕜 V) :
    (depolarizingChannelEquiv (V := V) δ hδ hδ1).symm X =
      (δ + 1) • X - LinearMap.trace 𝕜 V X • LinearMap.id := by
  rfl

end Isotropic

end ClassicalShadows
