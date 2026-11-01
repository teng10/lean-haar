/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.SupportingDocs.TraceContractions

/-!
# Finite measurement channels and the classical-shadow estimators

For explicit coefficients `w` and snapshots `S`, the measurement channel is
`M(ρ) = ∑ₓ wₓ Tr(ρ Sₓ) Sₓ`. Its inverse, when it exists, gives the state estimator
`M⁻¹(Sₓ)` and the observable estimator `Tr(O M⁻¹(Sₓ))`.

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

/-- The inverse `M⁻¹` of an invertible measurement channel. -/
def invChannel (hM : Function.Bijective (measurementChannel w S)) :
    Module.End 𝕜 V ≃ₗ[𝕜] Module.End 𝕜 V :=
  (LinearEquiv.ofBijective (measurementChannel w S) hM).symm

/-! ### The classical-shadow estimators -/

/-- The estimator `ô = Tr(O ρ̂)` of the expectation value of an observable `O`. -/
def observableEstimator (hM : Function.Bijective (measurementChannel w S))
    (O : Module.End 𝕜 V) (x : ι) : 𝕜 :=
  LinearMap.trace 𝕜 V (O ∘ₗ invChannel w S hM (S x))

/-! ### Tensor-moment identities (Observation 58) -/

/-- Expand the estimator's weighted square moment before contracting the tensor moment.

Write `Sₓ = S x` and `B = invChannel w S hM O`. Trace symmetry of the inverse channel
rewrites `Tr(O M⁻¹(Sₓ))` as `Tr(B Sₓ)`. Its square contributes two factors involving `Sₓ`;
the outcome weight `wₓ Tr(ρ Sₓ)` contributes the third. Thus the summand is
`wₓ Tr(ρ Sₓ) Tr(B Sₓ) Tr(B Sₓ)`. This is the scalar calculation for the third-tensor-moment
identity below, using an algebraic square rather than an absolute square. -/
private theorem secondMoment_observableEstimator (hM : Function.Bijective (measurementChannel w S))
    (hself : ∀ A B : Module.End 𝕜 V,
      LinearMap.trace 𝕜 V (A ∘ₗ invChannel w S hM B) =
        LinearMap.trace 𝕜 V (invChannel w S hM A ∘ₗ B)) (ρ O : Module.End 𝕜 V) :
    ∑ x, (w x * LinearMap.trace 𝕜 V (ρ ∘ₗ S x)) * observableEstimator w S hM O x ^ 2 =
      ∑ x, w x * LinearMap.trace 𝕜 V (ρ ∘ₗ S x) *
        LinearMap.trace 𝕜 V (invChannel w S hM O ∘ₗ S x) *
        LinearMap.trace 𝕜 V (invChannel w S hM O ∘ₗ S x) := by
  simp only [observableEstimator]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hself O (S x)]
  ring

/-- **Observation 58**, first identity: contract the first factor of the second snapshot
moment against `ρ` to obtain the measurement channel. -/
theorem measurementChannel_eq_partialTrace_secondTensorMoment (ρ : Module.End 𝕜 V) :
    measurementChannel w S ρ = LinearMap.partialTraceFirst ρ
      (∑ x, w x • (S x ⊗ₜ[𝕜] S x)) := by
  simp [measurementChannel, smul_smul]

/-- **Observation 58**, second identity: the algebraic estimator square-moment difference
is the contraction of the third snapshot moment against `ρ`, `M⁻¹(O)`, `M⁻¹(O)`, minus
`Tr(O ρ)²`. -/
theorem observableEstimatorVariance_eq_thirdTensorMoment
    (hM : Function.Bijective (measurementChannel w S))
    (hself : ∀ A B : Module.End 𝕜 V,
      LinearMap.trace 𝕜 V (A ∘ₗ invChannel w S hM B) =
        LinearMap.trace 𝕜 V (invChannel w S hM A ∘ₗ B)) (ρ O : Module.End 𝕜 V) :
    (∑ x, (w x * LinearMap.trace 𝕜 V (ρ ∘ₗ S x)) * observableEstimator w S hM O x ^ 2) -
        LinearMap.trace 𝕜 V (O ∘ₗ ρ) ^ 2 =
      LinearMap.tripleTraceContract ρ (invChannel w S hM O) (invChannel w S hM O)
        (∑ x, w x • (S x ⊗ₜ[𝕜] (S x ⊗ₜ[𝕜] S x))) -
        LinearMap.trace 𝕜 V (O ∘ₗ ρ) ^ 2 := by
  rw [secondMoment_observableEstimator w S hM hself ρ O]
  congr 1
  simp only [map_sum, map_smul, LinearMap.tripleTraceContract_tmul,
    smul_eq_mul, mul_assoc]

end ClassicalShadows
