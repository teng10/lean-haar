/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TraceNotation

/-!
# Snapshot ensembles, the measurement channel and the classical-shadow estimators

This file sets up the abstract algebraic frame of the classical-shadow protocol: a finite
weighted family of snapshots `Sₓ`, the induced measurement channel `M(ρ) = ∑ₓ wₓ Tr(ρ Sₓ) Sₓ`,
and the estimators `ρ̂ = M⁻¹(Sₓ)` and `ô = Tr(O ρ̂)` built from it.

## Main definitions

* `ClassicalShadows.SnapshotEnsemble`: a finite weighted family of snapshots `Sₓ`, the
  abstract stand-in for the classical snapshots `U† |b⟩⟨b| U` produced by the experiment.
* `ClassicalShadows.SnapshotEnsemble.measurementChannel`: `M(ρ) = ∑ₓ wₓ Tr(ρ Sₓ) Sₓ`, and
  `ClassicalShadows.SnapshotEnsemble.invChannel`, its inverse `M⁻¹`.
* `ClassicalShadows.SnapshotEnsemble.stateEstimator`,
  `ClassicalShadows.SnapshotEnsemble.observableEstimator`: `ρ̂ = M⁻¹(Sₓ)` and `ô = Tr(O ρ̂)`.
* `ClassicalShadows.SnapshotEnsemble.IsTraceSelfAdjoint`: the trace self-adjointness
  hypothesis `Tr(A F(B)) = Tr(F(A) B)` used for `M⁻¹`.

## Main results

* `ClassicalShadows.SnapshotEnsemble.secondMoment_observableEstimator`: the second moment of
  the observable estimator is a contraction of the third snapshot moment.

## Implementation notes

Nothing here needs an analytic input, so everything is stated over an arbitrary field `𝕜` and
an arbitrary `𝕜`-module `V`; positivity and normalization of the weights are never used.
-/

noncomputable section

namespace ClassicalShadows

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [Fintype ι]

/-- A finite weighted family of classical snapshots `Sₓ`, indexed by the outcomes `x : ι`.
Positivity and normalization of the weights are irrelevant to the algebraic identities
below, so they are not imposed here. -/
structure SnapshotEnsemble (𝕜 V ι : Type*) [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [Fintype ι] where
  /-- The prior weight of an outcome. -/
  weight : ι → 𝕜
  /-- The snapshot recorded for an outcome. -/
  snapshot : ι → Module.End 𝕜 V

namespace SnapshotEnsemble

variable (E : SnapshotEnsemble 𝕜 V ι)

/-! ### The measurement channel -/

/-- The Born weight `wₓ Tr(ρ Sₓ)` of an outcome, including its prior weight. -/
def outcomeWeight (ρ : Module.End 𝕜 V) (x : ι) : 𝕜 :=
  E.weight x * Tr[ρ ∘ₗ E.snapshot x]

/-- The measurement channel `M(ρ) = ∑ₓ wₓ Tr(ρ Sₓ) Sₓ` of a snapshot ensemble. -/
def measurementChannel : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V where
  toFun ρ := ∑ x, E.outcomeWeight ρ x • E.snapshot x
  map_add' ρ σ := by
    simp only [outcomeWeight, LinearMap.add_comp, map_add, mul_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' c ρ := by
    simp only [outcomeWeight, LinearMap.smul_comp, map_smul, Finset.smul_sum, smul_smul,
      RingHom.id_apply, smul_eq_mul, mul_left_comm]

@[simp]
theorem measurementChannel_apply (ρ : Module.End 𝕜 V) :
    E.measurementChannel ρ = ∑ x, E.outcomeWeight ρ x • E.snapshot x := rfl

/-- The inverse `M⁻¹` of an invertible measurement channel. -/
def invChannel (hM : Function.Bijective E.measurementChannel) :
    Module.End 𝕜 V ≃ₗ[𝕜] Module.End 𝕜 V :=
  (LinearEquiv.ofBijective E.measurementChannel hM).symm

/-! ### The classical-shadow estimators -/

/-- The classical shadow `ρ̂ = M⁻¹(Sₓ)` of the state, for the outcome `x`. -/
def stateEstimator (hM : Function.Bijective E.measurementChannel) (x : ι) : Module.End 𝕜 V :=
  E.invChannel hM (E.snapshot x)

/-- The estimator `ô = Tr(O ρ̂)` of the expectation value of an observable `O`. -/
def observableEstimator (hM : Function.Bijective E.measurementChannel)
    (O : Module.End 𝕜 V) (x : ι) : 𝕜 :=
  Tr[O ∘ₗ E.stateEstimator hM x]

/-- Trace self-adjointness `Tr(A F(B)) = Tr(F(A) B)` of a map `F` on operators. The paper
uses it for `M` and hence, `M` being invertible, for `M⁻¹`. -/
def IsTraceSelfAdjoint (F : Module.End 𝕜 V → Module.End 𝕜 V) : Prop :=
  ∀ A B : Module.End 𝕜 V, Tr[A ∘ₗ F B] = Tr[F A ∘ₗ B]

/-- The scalar contraction `∑ₓ wₓ Tr(A Sₓ) Tr(B Sₓ) Tr(C Sₓ)` of the third snapshot moment
against three operators. -/
def thirdMoment (A B C : Module.End 𝕜 V) : 𝕜 :=
  ∑ x, E.weight x * Tr[A ∘ₗ E.snapshot x] * Tr[B ∘ₗ E.snapshot x] * Tr[C ∘ₗ E.snapshot x]

/-- The second moment of the observable estimator is a contraction of the third snapshot
moment; this is the scalar half of the computation behind Observation 58. -/
theorem secondMoment_observableEstimator (hM : Function.Bijective E.measurementChannel)
    (hself : IsTraceSelfAdjoint (E.invChannel hM)) (ρ O : Module.End 𝕜 V) :
    ∑ x, E.outcomeWeight ρ x * E.observableEstimator hM O x ^ 2 =
      E.thirdMoment ρ (E.invChannel hM O) (E.invChannel hM O) := by
  simp only [outcomeWeight, observableEstimator, stateEstimator, thirdMoment]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hself O (E.snapshot x)]
  ring

end SnapshotEnsemble

end ClassicalShadows
