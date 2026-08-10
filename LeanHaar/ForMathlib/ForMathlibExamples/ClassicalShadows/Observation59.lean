/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.ClassicalShadows.DepolarizingChannel
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.HaarInvariance
import LeanHaar.ForMathlib.ForMathlibExamples.ClassicalShadows.MomentContraction
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TraceNotation

/-!
# Observation 59: the simplified Haar measurement channel and its inverse

The measurement channel of the classical-shadow protocol on `ℂ^d` averages, over a Haar-random
unitary `U` and over the measurement outcome `b`, the snapshot `U† |b⟩⟨b| U` weighted by its
Born probability `⟨b| U ρ U† |b⟩ = Tr(ρ U† |b⟩⟨b| U)`. **Observation 59** of
`classical_shadows.tex` evaluates it: `M(ρ) = (Tr(ρ) I + ρ)/(d+1)`, whence
`M⁻¹(ρ) = (d+1)ρ - Tr(ρ) I`.

## Main definitions

* `ClassicalShadows.haarMeasurementChannel`: the measurement channel of the Haar-random
  classical-shadow protocol, `M(ρ) = ∑_b 𝔼_{U∼μ}[⟨b|UρU†|b⟩ · U†|b⟩⟨b|U]`.
* `ClassicalShadows.haarMeasurementChannelEquiv`: that channel as a linear equivalence.

## Main results

* `ClassicalShadows.haarMeasurementChannel_apply`: `M(ρ) = (Tr(ρ) I + ρ)/(d + 1)`.
* `ClassicalShadows.haarMeasurementChannel_symm_apply`: `M⁻¹(ρ) = (d + 1)ρ - Tr(ρ) I`.

## Implementation notes

The Haar average of an operator-valued function is taken entrywise in the computational
basis, as is done for the moment operator `SchurWeyl.momentOp` of the framework; this avoids
putting a norm on `End(ℂ^d)` and is what makes the Bochner integrals here one-dimensional.
-/

noncomputable section

namespace ClassicalShadows

open SchurWeyl MeasureTheory Measure

variable {d : ℕ}

/-- Averaging the Born-weighted snapshots over the Haar measure and over the outcomes is the
same as contracting the second Haar moment `∑_b 𝔼_U[(U†|b⟩⟨b|U)^{⊗2}]` against `ρ` in the first
tensor factor: the partial-trace form of Observation 58 for the physical ensemble. -/
theorem sum_integral_bornWeighted_snapshot (ρ : Module.End ℂ (Fin d → ℂ)) (i j : Fin d) :
    ∑ b : Fin d, ∫ U, Tr[ρ ∘ₗ unitarySnapshot U b] * matrixOf (unitarySnapshot U b) i j
        ∂(haarProb d)
      = ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
          toEndMatrix d 2 (unitarySnapshotMoment d 2) ![p.2, i] ![p.1, j] := by
  have hb : ∀ b : Fin d, ∫ U, Tr[ρ ∘ₗ unitarySnapshot U b] * matrixOf (unitarySnapshot U b) i j
      ∂(haarProb d) = ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
        toEndMatrix d 2 (momentOp (diagAction d 2 (basisProjector d b))) ![p.2, i] ![p.1, j] := by
    intro b
    -- pointwise in `U`, the integrand contracts the tensor square of the snapshot
    have hrw : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        Tr[ρ ∘ₗ unitarySnapshot U b] * matrixOf (unitarySnapshot U b) i j =
        ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
          toEndMatrix d 2 (actOn (diagAction d 2 (basisProjector d b)) (star U))
            ![p.2, i] ![p.1, j] := fun U => by
      rw [trace_comp_mul_matrixOf, diagAction_unitarySnapshot]
    simp_rw [hrw]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun p _ => ?_
      -- Haar invariance under `U ↦ U†` turns the average into the moment operator
      rw [MeasureTheory.integral_const_mul, toEndMatrix_momentOp]
      exact congrArg _ (integral_star_haarProb (fun U => toEndMatrix d 2
        (actOn (diagAction d 2 (basisProjector d b)) U) ![p.2, i] ![p.1, j]))
    · exact fun p _ => integrable_haarProb_of_continuous (continuous_const.mul
        ((continuous_actOn_entry (diagAction d 2 (basisProjector d b)) ![p.2, i]
          ![p.1, j]).comp continuous_star))
  simp_rw [hb]
  rw [unitarySnapshotMoment, _root_.map_sum, Finset.sum_comm]
  simp only [Matrix.sum_apply, Finset.mul_sum]

/-- The **measurement channel** of the Haar-random classical-shadow protocol on `ℂ^d`:
`M(ρ) = ∑_b 𝔼_{U∼μ}[⟨b|UρU†|b⟩ · U†|b⟩⟨b|U]`, where the Born weight `⟨b|UρU†|b⟩` is written as
`Tr(ρ S)` for the snapshot `S = U†|b⟩⟨b|U`. The Haar average is taken entrywise in the
computational basis. -/
def haarMeasurementChannel (d : ℕ) (ρ : Module.End ℂ (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ) :=
  Matrix.toLin' (Matrix.of fun i j => ∑ b : Fin d,
    ∫ U, Tr[ρ ∘ₗ unitarySnapshot U b] * matrixOf (unitarySnapshot U b) i j ∂(haarProb d))

/-- **Observation 59**, first formula: the measurement channel of the Haar-random
classical-shadow protocol is `M(ρ) = (Tr(ρ) I + ρ)/(d + 1)`. -/
theorem haarMeasurementChannel_apply [NeZero d] [Fact (2 ≤ d)] (ρ : Module.End ℂ (Fin d → ℂ)) :
    haarMeasurementChannel d ρ = ((d : ℂ) + 1)⁻¹ • (Tr[ρ] • LinearMap.id + ρ) := by
  have hmat : (Matrix.of fun i j => ∑ b : Fin d,
      ∫ U, Tr[ρ ∘ₗ unitarySnapshot U b] * matrixOf (unitarySnapshot U b) i j ∂(haarProb d)) =
      ((d : ℂ) + 1)⁻¹ • (Tr[ρ] • (1 : Matrix (Fin d) (Fin d) ℂ) + matrixOf ρ) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    rw [sum_integral_bornWeighted_snapshot, contract_unitarySnapshotMoment_two]
    simp [Matrix.one_apply, mul_add]
  rw [haarMeasurementChannel, hmat]
  simp [(LinearEquiv.eq_symm_apply Matrix.toLin').mp (rfl : matrixOf ρ = matrixOf ρ)]

/-- The trace of the identity of `ℂ^d` is the dimension `d`. -/
theorem trace_id_eq_dim (d : ℕ) :
    LinearMap.trace ℂ (Fin d → ℂ) (LinearMap.id : Module.End ℂ (Fin d → ℂ)) = (d : ℂ) := by
  simp

/-- For a natural number `d`, the scalar `d + 1` is nonzero in `ℂ`. -/
theorem dim_add_one_ne_zero (d : ℕ) : ((d : ℂ) + 1) ≠ 0 :=
  Nat.cast_add_one_ne_zero (R := ℂ) d

/-- The measurement channel of the Haar-random classical-shadow protocol, packaged as a linear
equivalence via its explicit inverse; see `haarMeasurementChannelEquiv_apply`. -/
def haarMeasurementChannelEquiv (d : ℕ) :
    Module.End ℂ (Fin d → ℂ) ≃ₗ[ℂ] Module.End ℂ (Fin d → ℂ) :=
  depolarizingChannelEquiv (V := Fin d → ℂ) (d : ℂ) (trace_id_eq_dim d) (dim_add_one_ne_zero d)

/-- The linear equivalence `haarMeasurementChannelEquiv` is the measurement channel `M`. -/
@[simp]
theorem haarMeasurementChannelEquiv_apply [NeZero d] [Fact (2 ≤ d)]
    (ρ : Module.End ℂ (Fin d → ℂ)) :
    haarMeasurementChannelEquiv d ρ = haarMeasurementChannel d ρ := by
  rw [haarMeasurementChannel_apply, haarMeasurementChannelEquiv]
  exact depolarizingChannel_apply (V := Fin d → ℂ) (d : ℂ) ρ

/-- **Observation 59**, second formula: the inverse of the measurement channel of the
Haar-random classical-shadow protocol is `M⁻¹(ρ) = (d + 1)ρ - Tr(ρ) I`. -/
theorem haarMeasurementChannel_symm_apply (d : ℕ) (ρ : Module.End ℂ (Fin d → ℂ)) :
    (haarMeasurementChannelEquiv d).symm ρ = ((d : ℂ) + 1) • ρ - Tr[ρ] • LinearMap.id :=
  rfl

end ClassicalShadows
