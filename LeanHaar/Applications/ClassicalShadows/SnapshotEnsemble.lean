/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.SupportingDocs.TraceContractions

/-!
# Finite measurement channels and the classical-shadow estimators

For explicit coefficients `w` and snapshots `S`, the measurement channel is
`M(ρ) = ∑ₓ wₓ Tr(ρ Sₓ) Sₓ`. Its inverse, when it exists, gives the state estimator
`M⁻¹(Sₓ)` and the observable estimator `Tr(O M⁻¹(Sₓ))`. The reconstruction and
observable-mean identities below follow algebraically from invertibility; they do not
assume that the trace coefficients form a probability distribution.

The two identities of Observation 58 are proved here:

* `ClassicalShadows.measurementChannel_eq_partialTrace_secondTensorMoment`: contracting
  `∑ₓ wₓ (Sₓ ⊗ Sₓ)` against `ρ` gives the measurement channel.
* `ClassicalShadows.observableEstimatorVariance_eq_thirdTensorMoment`: contracting
  `∑ₓ wₓ (Sₓ ⊗ Sₓ ⊗ Sₓ)` gives the estimator's weighted square moment; subtracting
  `Tr(Oρ)²` gives the stated square-moment difference.

These are algebraic identities over an arbitrary field. In a physical finite protocol,
`wₓ Sₓ` must be the effects of a POVM, whose Born probability on a density state is
`wₓ Tr(ρ Sₓ)`. For settings `a` sampled with probability `q a` and basis outcomes `b`,
use `w (a, b) = q a`; these coefficients need not sum to one over the combined index.
Positivity and completeness are not hypotheses of the algebraic identities below.

Physlib's `POVM.measure` supplies probabilities in the physical model; `UnitarySnapshots`
relates them to the trace coefficients and Haar averaging. The finite tensor sums here live
in tensor products of endomorphisms, whereas `SchurWeyl.momentOp` integrates operators on
`TensV d k`. No identification between these tensor models is assumed.
-/

noncomputable section

namespace ClassicalShadows

open scoped TensorProduct

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [Fintype ι]

variable (w : ι → 𝕜) (S : ι → Module.End 𝕜 V)

/-! ### The measurement channel -/

/-- The measurement channel `M(ρ) = ∑ₓ wₓ Tr(ρ Sₓ) Sₓ` for coefficients `w` and snapshots `S`. -/
def measurementChannel : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V where
  toFun ρ := ∑ x, (w x * LinearMap.trace 𝕜 V (ρ ∘ₗ S x)) • S x
  map_add' ρ σ := by
    simp only [LinearMap.add_comp, map_add, mul_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' c ρ := by
    simp only [LinearMap.smul_comp, map_smul, Finset.smul_sum, smul_smul,
      RingHom.id_apply, smul_eq_mul, mul_left_comm]

/-- Evaluate the finite measurement channel as its defining weighted sum. -/
@[simp] theorem measurementChannel_apply (ρ : Module.End 𝕜 V) :
    measurementChannel w S ρ = ∑ x, (w x * LinearMap.trace 𝕜 V (ρ ∘ₗ S x)) • S x := rfl

/-- The measurement channel is symmetric for the bilinear trace pairing. -/
theorem trace_comp_measurementChannel_comm (A B : Module.End 𝕜 V) :
    LinearMap.trace 𝕜 V (A ∘ₗ measurementChannel w S B) =
      LinearMap.trace 𝕜 V (measurementChannel w S A ∘ₗ B) := by
  have htrace (A B : Module.End 𝕜 V) :
      LinearMap.trace 𝕜 V (A ∘ₗ measurementChannel w S B) =
        ∑ x, w x * LinearMap.trace 𝕜 V (B ∘ₗ S x) *
          LinearMap.trace 𝕜 V (A ∘ₗ S x) := by
    simp only [measurementChannel_apply, ← Module.End.mul_eq_comp, Finset.mul_sum,
      mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  have h := LinearMap.trace_mul_comm (R := 𝕜) (measurementChannel w S A) B
  simp only [Module.End.mul_eq_comp] at h
  rw [h, htrace, htrace]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The inverse `M⁻¹` of an invertible measurement channel. -/
def invChannel (hM : Function.Bijective (measurementChannel w S)) :
    Module.End 𝕜 V ≃ₗ[𝕜] Module.End 𝕜 V :=
  (LinearEquiv.ofBijective (measurementChannel w S) hM).symm

/-- An invertible measurement channel has an inverse symmetric for the trace pairing. -/
theorem trace_comp_invChannel_comm (hM : Function.Bijective (measurementChannel w S))
    (A B : Module.End 𝕜 V) :
    LinearMap.trace 𝕜 V (A ∘ₗ invChannel w S hM B) =
      LinearMap.trace 𝕜 V (invChannel w S hM A ∘ₗ B) := by
  have hcancel (X : Module.End 𝕜 V) : measurementChannel w S (invChannel w S hM X) = X :=
    (LinearEquiv.ofBijective _ hM).apply_symm_apply X
  calc
    LinearMap.trace 𝕜 V (A ∘ₗ invChannel w S hM B) =
        LinearMap.trace 𝕜 V
          (measurementChannel w S (invChannel w S hM A) ∘ₗ invChannel w S hM B) := by
      rw [hcancel]
    _ = LinearMap.trace 𝕜 V
        (invChannel w S hM A ∘ₗ measurementChannel w S (invChannel w S hM B)) :=
      (trace_comp_measurementChannel_comm w S _ _).symm
    _ = _ := by rw [hcancel]

/-! ### The classical-shadow estimators -/

/-- The estimator `ô = Tr(O ρ̂)` of the expectation value of an observable `O`. -/
def observableEstimator (hM : Function.Bijective (measurementChannel w S))
    (O : Module.End 𝕜 V) (x : ι) : 𝕜 :=
  LinearMap.trace 𝕜 V (O ∘ₗ invChannel w S hM (S x))

/-- The algebraic reconstruction identity for an invertible finite measurement channel.

The coefficients need not form a probability distribution. When they are Born probabilities,
this states unbiasedness of the reconstructed state. -/
theorem sum_smul_invChannel_eq (hM : Function.Bijective (measurementChannel w S))
    (ρ : Module.End 𝕜 V) :
    ∑ x, (w x * LinearMap.trace 𝕜 V (ρ ∘ₗ S x)) • invChannel w S hM (S x) = ρ := by
  calc
    _ = invChannel w S hM (measurementChannel w S ρ) := by
      rw [measurementChannel_apply]
      simp only [map_sum, map_smul]
    _ = ρ := (LinearEquiv.ofBijective _ hM).symm_apply_apply ρ

/-- The weighted observable-estimator mean equals `Tr(Oρ)` algebraically.

This is a probabilistic mean only when the coefficients form the outcome distribution. -/
theorem sum_mul_observableEstimator_eq (hM : Function.Bijective (measurementChannel w S))
    (ρ O : Module.End 𝕜 V) :
    ∑ x, (w x * LinearMap.trace 𝕜 V (ρ ∘ₗ S x)) * observableEstimator w S hM O x =
      LinearMap.trace 𝕜 V (O ∘ₗ ρ) := by
  conv_rhs => rw [← sum_smul_invChannel_eq w S hM ρ]
  simp only [observableEstimator, ← Module.End.mul_eq_comp, Finset.mul_sum, mul_smul_comm,
    map_sum, map_smul, smul_eq_mul]

/-! ### Tensor-moment identities (Observation 58) -/

/-- **Observation 58**, first identity: contract the first factor of the second snapshot
moment against `ρ` to obtain the measurement channel. -/
theorem measurementChannel_eq_partialTrace_secondTensorMoment (ρ : Module.End 𝕜 V) :
    measurementChannel w S ρ = LinearMap.partialTraceFirst ρ
      (∑ x, w x • (S x ⊗ₜ[𝕜] S x)) := by
  simp [smul_smul]

/-- The estimator's weighted algebraic square moment is a third-tensor-moment contraction.

Write `B = invChannel w S hM O`. Trace symmetry of the inverse rewrites
`Tr(O M⁻¹(Sₓ))` as `Tr(B Sₓ)`. The square supplies two factors of `Sₓ`, while the
coefficient `wₓ Tr(ρ Sₓ)` supplies the third. This uses an algebraic square rather than
an absolute square and requires no positivity or probability normalization. -/
theorem sum_mul_observableEstimator_sq_eq (hM : Function.Bijective (measurementChannel w S))
    (ρ O : Module.End 𝕜 V) :
    ∑ x, (w x * LinearMap.trace 𝕜 V (ρ ∘ₗ S x)) * observableEstimator w S hM O x ^ 2 =
      LinearMap.tripleTraceContract ρ (invChannel w S hM O) (invChannel w S hM O)
        (∑ x, w x • (S x ⊗ₜ[𝕜] (S x ⊗ₜ[𝕜] S x))) := by
  simp only [map_sum, map_smul, LinearMap.tripleTraceContract_tmul,
    smul_eq_mul, observableEstimator]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [trace_comp_invChannel_comm w S hM O (S x)]
  ring

/-- **Observation 58**, second identity: the algebraic estimator square-moment difference
is the contraction of the third snapshot moment against `ρ`, `M⁻¹(O)`, `M⁻¹(O)`, minus
`Tr(O ρ)²`. This is a probabilistic variance only with a normalized outcome law and a
real-valued estimator. -/
theorem observableEstimatorVariance_eq_thirdTensorMoment
    (hM : Function.Bijective (measurementChannel w S)) (ρ O : Module.End 𝕜 V) :
    (∑ x, (w x * LinearMap.trace 𝕜 V (ρ ∘ₗ S x)) * observableEstimator w S hM O x ^ 2) -
        LinearMap.trace 𝕜 V (O ∘ₗ ρ) ^ 2 =
      LinearMap.tripleTraceContract ρ (invChannel w S hM O) (invChannel w S hM O)
        (∑ x, w x • (S x ⊗ₜ[𝕜] (S x ⊗ₜ[𝕜] S x))) -
        LinearMap.trace 𝕜 V (O ∘ₗ ρ) ^ 2 := by
  rw [sum_mul_observableEstimator_sq_eq]

end ClassicalShadows
