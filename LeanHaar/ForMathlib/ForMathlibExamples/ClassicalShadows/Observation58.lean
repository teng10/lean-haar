/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.ClassicalShadows.SnapshotEnsemble
import LeanHaar.ForMathlib.ForMathlibExamples.ClassicalShadows.TraceContractions
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TraceNotation

/-!
# Observation 58: the measurement channel and the estimator variance as tensor moments

This file proves **Observation 58** of `classical_shadows.tex`: the measurement channel and
the variance of the observable estimator of a snapshot ensemble are contractions of the
second and third tensor moments `∑ₓ wₓ Sₓ^{⊗2}` and `∑ₓ wₓ Sₓ^{⊗3}` of the ensemble.

## Main definitions

* `ClassicalShadows.SnapshotEnsemble.secondTensorMoment`,
  `ClassicalShadows.SnapshotEnsemble.thirdTensorMoment`: `∑ₓ wₓ Sₓ^{⊗2}` and `∑ₓ wₓ Sₓ^{⊗3}`.
* `ClassicalShadows.SnapshotEnsemble.observableEstimatorVariance`: the variance of the
  observable estimator under the Born-weighted outcome law.

## Main results

* `ClassicalShadows.SnapshotEnsemble.measurementChannel_eq_partialTrace_secondTensorMoment`:
  `M(ρ) = Tr₁((ρ ⊗ I) ∑ₓ wₓ Sₓ^{⊗2})`.
* `ClassicalShadows.SnapshotEnsemble.observableEstimatorVariance_eq_thirdTensorMoment`: the
  variance is the contraction of `∑ₓ wₓ Sₓ^{⊗3}` against `ρ`, `M⁻¹(O)`, `M⁻¹(O)`, minus
  `Tr(O ρ)²`.
-/

noncomputable section

namespace ClassicalShadows

open scoped TensorProduct

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [Fintype ι]

namespace SnapshotEnsemble

variable (E : SnapshotEnsemble 𝕜 V ι)

/-- The second tensor moment `∑ₓ wₓ Sₓ ⊗ Sₓ` of a snapshot ensemble. -/
def secondTensorMoment : Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V :=
  ∑ x, E.weight x • (E.snapshot x ⊗ₜ[𝕜] E.snapshot x)

/-- The third tensor moment `∑ₓ wₓ Sₓ ⊗ Sₓ ⊗ Sₓ` of a snapshot ensemble. -/
def thirdTensorMoment :
    Module.End 𝕜 V ⊗[𝕜] (Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V) :=
  ∑ x, E.weight x • (E.snapshot x ⊗ₜ[𝕜] (E.snapshot x ⊗ₜ[𝕜] E.snapshot x))

/-- **Observation 58**, first identity: the measurement channel is the partial trace of the
second snapshot moment, `M(ρ) = Tr₁((ρ ⊗ I) ∑ₓ wₓ Sₓ^{⊗2})`. -/
theorem measurementChannel_eq_partialTrace_secondTensorMoment (ρ : Module.End 𝕜 V) :
    E.measurementChannel ρ = partialTraceFirst ρ E.secondTensorMoment := by
  simp [outcomeWeight, secondTensorMoment, smul_smul]

/-- The variance of the observable estimator under the Born-weighted outcome law, written
as its second moment minus the square of its true mean `Tr(O ρ)`. -/
def observableEstimatorVariance (hM : Function.Bijective E.measurementChannel)
    (ρ O : Module.End 𝕜 V) : 𝕜 :=
  (∑ x, E.outcomeWeight ρ x * E.observableEstimator hM O x ^ 2) - Tr[O ∘ₗ ρ] ^ 2

/-- **Observation 58**, second identity: the variance of the observable estimator is the
contraction of the third snapshot moment against `ρ`, `M⁻¹(O)`, `M⁻¹(O)`, minus
`Tr(O ρ)²`. -/
theorem observableEstimatorVariance_eq_thirdTensorMoment
    (hM : Function.Bijective E.measurementChannel)
    (hself : IsTraceSelfAdjoint (E.invChannel hM)) (ρ O : Module.End 𝕜 V) :
    E.observableEstimatorVariance hM ρ O =
      tripleTraceContract ρ (E.invChannel hM O) (E.invChannel hM O) E.thirdTensorMoment -
        Tr[O ∘ₗ ρ] ^ 2 := by
  rw [observableEstimatorVariance, E.secondMoment_observableEstimator hM hself ρ O]
  congr 1
  simp only [thirdMoment, thirdTensorMoment, map_sum, map_smul, tripleTraceContract_tmul,
    smul_eq_mul, mul_assoc]

end SnapshotEnsemble

end ClassicalShadows
