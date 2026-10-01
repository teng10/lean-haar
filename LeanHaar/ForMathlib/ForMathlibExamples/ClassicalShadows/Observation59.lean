/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.k2Moment
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.HaarInvariance
import LeanHaar.ForMathlib.ForMathlibExamples.ClassicalShadows.UnitarySnapshots

/-!
# Observation 59: the simplified Haar measurement channel and its inverse

The measurement channel of the classical-shadow protocol on `ℂ^d` averages, over a Haar-random
unitary `U` and over the measurement outcome `b`, the snapshot `U† |b⟩⟨b| U` weighted by its
Born probability `⟨b| U ρ U† |b⟩ = Tr(ρ U† |b⟩⟨b| U)`. **Observation 59** of
`classical_shadows.tex` evaluates it: `M(ρ) = (Tr(ρ) I + ρ)/(d+1)`, whence
`M⁻¹(ρ) = (d+1)ρ - Tr(ρ) I`.

The channel and its candidate algebraic equivalence are defined in `UnitarySnapshots`.
This file specializes `k2_moment` to the computational-basis projectors, proves equality
with the integral channel for `d ≥ 2`, and gives the inverse formula.

## Main results

* `ClassicalShadows.unitarySnapshotMoment_two`: the summed second snapshot moment, obtained
  from `k2_moment`.
* `ClassicalShadows.haarMeasurementChannel_apply`: `M(ρ) = (Tr(ρ) I + ρ)/(d + 1)`.
* `ClassicalShadows.haarMeasurementChannel_symm_apply`: `M⁻¹(ρ) = (d + 1)ρ - Tr(ρ) I`.

## Implementation notes

This is a separate entrywise argument for the continuous Haar model. No identification with
the finite `SnapshotEnsemble` model or its tensor-of-endomorphisms model is asserted.

The Haar average of an operator-valued function is taken entrywise in the computational
basis, as is done for the moment operator `SchurWeyl.momentOp` of the framework; this avoids
putting a norm on `End(ℂ^d)` and is what makes the Bochner integrals here one-dimensional.
-/

noncomputable section

namespace ClassicalShadows

open SchurWeyl MeasureTheory Measure

variable {d : ℕ}

/-! ### Specializing the second Haar moment -/

/-- Specialize `k2_moment` to each computational-basis projector's tensor square and sum
across the `d` basis outcomes. Each projector has trace one and is idempotent, so the identity
and swap trace contractions are both one. The resulting unnormalized sum is
`(I + 𝔽)/(d + 1)`. This is a corollary of the existing second Haar moment formula. -/
theorem unitarySnapshotMoment_two (d : ℕ) [NeZero d] [Fact (2 ≤ d)] :
    unitarySnapshotMoment d 2 =
      ((d : ℂ) + 1)⁻¹ • ((LinearMap.id : Module.End ℂ (TensV d 2)) + 𝔽 d) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdm1 : (d : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr <| by exact_mod_cast Nat.ne_of_gt (Fact.out (p := 2 ≤ d))
  have hdp1 : (d : ℂ) + 1 ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_ne_zero]; omega
  have hd2m1 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [show (d : ℂ) ^ 2 - 1 = ((d : ℂ) - 1) * ((d : ℂ) + 1) by ring]
    exact mul_ne_zero hdm1 hdp1
  -- every summand has the same two trace contractions, both equal to `1`
  have hcoeff : (d : ℂ) * ((1 - (d : ℂ)⁻¹) / ((d : ℂ) ^ 2 - 1)) = ((d : ℂ) + 1)⁻¹ := by
    field_simp
    ring
  rw [unitarySnapshotMoment]
  simp_rw [k2_moment]
  simp only [smul_eq_mul, Module.End.mul_eq_comp, trace_diagAction, trace_swap_comp_diagAction,
    basisProjector_comp_self, trace_basisProjector, one_pow, mul_one]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul, hcoeff,
    smul_add]

/-! ### Contracting the second snapshot moment -/

/-- Contracting the second Haar moment `(I + 𝔽)/(d+1)` against `ρ` in the first tensor factor
produces `(Tr(ρ) I + ρ)/(d+1)`, entrywise. -/
private theorem contract_unitarySnapshotMoment_two [NeZero d] [Fact (2 ≤ d)]
    (ρ : Module.End ℂ (Fin d → ℂ)) (i j : Fin d) :
    ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
        toEndMatrix d 2 (unitarySnapshotMoment d 2) ![p.2, i] ![p.1, j] =
      ((d : ℂ) + 1)⁻¹ *
        (LinearMap.trace ℂ (Fin d → ℂ) ρ * (if i = j then 1 else 0) + matrixOf ρ i j) := by
  have h₁ : ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
      toEndMatrix d 2 (LinearMap.id : Module.End ℂ (TensV d 2)) ![p.2, i] ![p.1, j] =
      LinearMap.trace ℂ (Fin d → ℂ) ρ * (if i = j then 1 else 0) := by
    rw [trace_eq_sum_diag]
    by_cases h : i = j <;> simp [toEndMatrix, Matrix.one_apply, Fintype.sum_prod_type,
      funext_iff, Fin.forall_fin_two, h, eq_comm]
  have h₂ : ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
      toEndMatrix d 2 (𝔽 d) ![p.2, i] ![p.1, j] = matrixOf ρ i j := by
    simp [toEndMatrix_swap, Fintype.sum_prod_type, funext_iff, Fin.forall_fin_two,
      and_comm, ite_and]
  rw [unitarySnapshotMoment_two]
  simp only [_root_.map_smul, _root_.map_add, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  calc _ = ((d : ℂ) + 1)⁻¹ *
        ((∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
          toEndMatrix d 2 (LinearMap.id : Module.End ℂ (TensV d 2)) ![p.2, i] ![p.1, j]) +
        ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
          toEndMatrix d 2 (𝔽 d) ![p.2, i] ![p.1, j]) := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun p _ => by ring
    _ = _ := by rw [h₁, h₂]

/-! ### The Haar measurement channel -/

/-- Averaging the Born-weighted snapshots over the Haar measure and over the outcomes is the
same as contracting the second Haar moment `∑_b 𝔼_U[(U†|b⟩⟨b|U)^{⊗2}]` against `ρ` in the first
tensor factor: the analogous entrywise contraction identity for the continuous Haar model. -/
theorem sum_integral_bornWeighted_snapshot (ρ : Module.End ℂ (Fin d → ℂ)) (i j : Fin d) :
    ∑ b : Fin d, ∫ U, LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ unitarySnapshot U b) *
        matrixOf (unitarySnapshot U b) i j ∂(haarProb d)
      = ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
          toEndMatrix d 2 (unitarySnapshotMoment d 2) ![p.2, i] ![p.1, j] := by
  have hb : ∀ b : Fin d, ∫ U, LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ unitarySnapshot U b) *
      matrixOf (unitarySnapshot U b) i j ∂(haarProb d) = ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
        toEndMatrix d 2 (momentOp (diagAction d 2 (basisProjector d b))) ![p.2, i] ![p.1, j] := by
    intro b
    -- pointwise in `U`, the integrand contracts the tensor square of the snapshot
    have hrw : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ unitarySnapshot U b) *
          matrixOf (unitarySnapshot U b) i j =
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

/-- **Observation 59**, first formula: the measurement channel of the Haar-random
classical-shadow protocol is `M(ρ) = (Tr(ρ) I + ρ)/(d + 1)`. -/
theorem haarMeasurementChannel_apply [NeZero d] [Fact (2 ≤ d)] (ρ : Module.End ℂ (Fin d → ℂ)) :
    haarMeasurementChannel d ρ =
      ((d : ℂ) + 1)⁻¹ • (LinearMap.trace ℂ (Fin d → ℂ) ρ • LinearMap.id + ρ) := by
  have hmat : (Matrix.of fun i j => ∑ b : Fin d,
      ∫ U, LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ unitarySnapshot U b) *
        matrixOf (unitarySnapshot U b) i j ∂(haarProb d)) =
      ((d : ℂ) + 1)⁻¹ •
        (LinearMap.trace ℂ (Fin d → ℂ) ρ • (1 : Matrix (Fin d) (Fin d) ℂ) + matrixOf ρ) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    rw [sum_integral_bornWeighted_snapshot, contract_unitarySnapshotMoment_two]
    simp [Matrix.one_apply, mul_add]
  rw [haarMeasurementChannel, hmat]
  simp [(LinearEquiv.eq_symm_apply Matrix.toLin').mp (rfl : matrixOf ρ = matrixOf ρ)]

/-- For `d ≥ 2`, the explicit isotropic equivalence equals the integral measurement channel. -/
@[simp]
theorem haarMeasurementChannelEquiv_apply [NeZero d] [Fact (2 ≤ d)]
    (ρ : Module.End ℂ (Fin d → ℂ)) :
    haarMeasurementChannelEquiv d ρ = haarMeasurementChannel d ρ := by
  rw [haarMeasurementChannel_apply, haarMeasurementChannelEquiv]
  exact LinearMap.depolarizingChannel_apply (V := Fin d → ℂ) (d : ℂ) ρ

/-- The algebraic inverse formula `(d + 1)ρ - Tr(ρ) I` for the explicit isotropic
equivalence. For `d ≥ 2`, `haarMeasurementChannelEquiv_apply` identifies this with
the inverse of the integral Haar measurement channel, giving Observation 59. -/
theorem haarMeasurementChannel_symm_apply (d : ℕ) (ρ : Module.End ℂ (Fin d → ℂ)) :
    (haarMeasurementChannelEquiv d).symm ρ =
      ((d : ℂ) + 1) • ρ - LinearMap.trace ℂ (Fin d → ℂ) ρ • LinearMap.id :=
  rfl

end ClassicalShadows
