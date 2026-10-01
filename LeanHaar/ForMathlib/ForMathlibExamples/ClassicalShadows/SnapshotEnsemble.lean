/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TraceContractions

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
* `ClassicalShadows.SnapshotEnsemble.secondTensorMoment`,
  `ClassicalShadows.SnapshotEnsemble.thirdTensorMoment`: the weighted twofold and threefold
  tensors of snapshots. These are tensors of endomorphisms, with no identification with
  endomorphisms of a tensor-product state space assumed here.

## Main results

The two identities of Observation 58 are proved here:

* `ClassicalShadows.SnapshotEnsemble.measurementChannel_eq_partialTrace_secondTensorMoment`:
  contracting the second tensor moment against `ρ` gives the measurement channel.
* `ClassicalShadows.SnapshotEnsemble.observableEstimatorVariance_eq_thirdTensorMoment`:
  contracting the third tensor moment against `ρ`, `M⁻¹(O)`, `M⁻¹(O)` gives the estimator's
  weighted square moment; subtracting `Tr(Oρ)²` gives the stated square-moment difference.

## Implementation notes

Nothing here needs an analytic input, so everything is stated over an arbitrary field `𝕜` and
an arbitrary `𝕜`-module `V`; positivity and normalization of the weights are never used.
The second-moment identity is therefore an algebraic identity of weighted sums; interpreting
the weights as a probability law requires additional hypotheses.

The finite tensor moments here are weighted sums in tensor products of `Module.End 𝕜 V`.
They do not duplicate `SchurWeyl.momentOp`, which integrates a unitary conjugation orbit of an
operator on `TensV d k`. No identification between these tensor models is assumed.
-/

noncomputable section

namespace ClassicalShadows

open scoped TensorProduct

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

/-! ### Tensor moments of the ensemble -/

/-- The second tensor moment `∑ₓ wₓ Sₓ ⊗ Sₓ` of a snapshot ensemble. -/
def secondTensorMoment : Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V :=
  ∑ x, E.weight x • (E.snapshot x ⊗ₜ[𝕜] E.snapshot x)

/-- The third tensor moment `∑ₓ wₓ Sₓ ⊗ Sₓ ⊗ Sₓ` of a snapshot ensemble. -/
def thirdTensorMoment :
    Module.End 𝕜 V ⊗[𝕜] (Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V) :=
  ∑ x, E.weight x • (E.snapshot x ⊗ₜ[𝕜] (E.snapshot x ⊗ₜ[𝕜] E.snapshot x))

/-! ### The measurement channel -/

/-- The Born weight `wₓ Tr(ρ Sₓ)` of an outcome, including its prior weight. -/
def outcomeWeight (ρ : Module.End 𝕜 V) (x : ι) : 𝕜 :=
  E.weight x * LinearMap.trace 𝕜 V (ρ ∘ₗ E.snapshot x)

/-- The measurement channel `M(ρ) = ∑ₓ wₓ Tr(ρ Sₓ) Sₓ` of a snapshot ensemble. -/
def measurementChannel : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V where
  toFun ρ := ∑ x, E.outcomeWeight ρ x • E.snapshot x
  map_add' ρ σ := by
    simp only [outcomeWeight, LinearMap.add_comp, map_add, mul_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' c ρ := by
    simp only [outcomeWeight, LinearMap.smul_comp, map_smul, Finset.smul_sum, smul_smul,
      RingHom.id_apply, smul_eq_mul, mul_left_comm]

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
  LinearMap.trace 𝕜 V (O ∘ₗ E.stateEstimator hM x)

/-! ### Tensor-moment identities (Observation 58) -/

/-- Expand the estimator's weighted square moment before contracting the tensor moment.

Write `Sₓ = E.snapshot x` and `B = E.invChannel hM O`. Trace symmetry of the inverse channel
rewrites `Tr(O M⁻¹(Sₓ))` as `Tr(B Sₓ)`. Its square contributes two factors involving `Sₓ`;
the outcome weight `wₓ Tr(ρ Sₓ)` contributes the third. Thus the summand is
`wₓ Tr(ρ Sₓ) Tr(B Sₓ) Tr(B Sₓ)`. This is the scalar calculation for the third-tensor-moment
identity below, using an algebraic square rather than an absolute square. -/
private theorem secondMoment_observableEstimator (hM : Function.Bijective E.measurementChannel)
    (hself : ∀ A B : Module.End 𝕜 V,
      LinearMap.trace 𝕜 V (A ∘ₗ E.invChannel hM B) =
        LinearMap.trace 𝕜 V (E.invChannel hM A ∘ₗ B)) (ρ O : Module.End 𝕜 V) :
    ∑ x, E.outcomeWeight ρ x * E.observableEstimator hM O x ^ 2 =
      ∑ x, E.weight x * LinearMap.trace 𝕜 V (ρ ∘ₗ E.snapshot x) *
        LinearMap.trace 𝕜 V (E.invChannel hM O ∘ₗ E.snapshot x) *
        LinearMap.trace 𝕜 V (E.invChannel hM O ∘ₗ E.snapshot x) := by
  simp only [outcomeWeight, observableEstimator, stateEstimator]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hself O (E.snapshot x)]
  ring

/-- **Observation 58**, first identity: contract the first factor of the second snapshot
moment against `ρ` to obtain the measurement channel. -/
theorem measurementChannel_eq_partialTrace_secondTensorMoment (ρ : Module.End 𝕜 V) :
    E.measurementChannel ρ = LinearMap.partialTraceFirst ρ E.secondTensorMoment := by
  simp [measurementChannel, outcomeWeight, secondTensorMoment, smul_smul]

/-- **Observation 58**, second identity: the algebraic estimator square-moment difference
is the contraction of the third snapshot moment against `ρ`, `M⁻¹(O)`, `M⁻¹(O)`, minus
`Tr(O ρ)²`. -/
theorem observableEstimatorVariance_eq_thirdTensorMoment
    (hM : Function.Bijective E.measurementChannel)
    (hself : ∀ A B : Module.End 𝕜 V,
      LinearMap.trace 𝕜 V (A ∘ₗ E.invChannel hM B) =
        LinearMap.trace 𝕜 V (E.invChannel hM A ∘ₗ B)) (ρ O : Module.End 𝕜 V) :
    (∑ x, E.outcomeWeight ρ x * E.observableEstimator hM O x ^ 2) -
        LinearMap.trace 𝕜 V (O ∘ₗ ρ) ^ 2 =
      LinearMap.tripleTraceContract ρ (E.invChannel hM O) (E.invChannel hM O) E.thirdTensorMoment -
        LinearMap.trace 𝕜 V (O ∘ₗ ρ) ^ 2 := by
  rw [E.secondMoment_observableEstimator hM hself ρ O]
  congr 1
  simp only [thirdTensorMoment, map_sum, map_smul, LinearMap.tripleTraceContract_tmul,
    smul_eq_mul, mul_assoc]

end SnapshotEnsemble

end ClassicalShadows
