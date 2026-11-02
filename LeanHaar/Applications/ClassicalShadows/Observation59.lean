/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Moments.k2Moment
import LeanHaar.SupportingDocs.HaarInvariance
import LeanHaar.SupportingDocs.DepolarizingChannel
import LeanHaar.Applications.ClassicalShadows.UnitarySnapshots
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Observation 59: the Haar channel, its inverse, and shadow reconstruction

The measurement channel of the classical-shadow protocol on `ℂ^d` averages, over a Haar-random
unitary `U` and over the measurement outcome `b`, the snapshot `U† |b⟩⟨b| U` weighted by its
Born probability `⟨b| U ρ U† |b⟩ = Tr(ρ U† |b⟩⟨b| U)`. The project's **Observation 59**
evaluates it: `M(ρ) = (Tr(ρ) I + ρ)/(d+1)`, whence
`M⁻¹(ρ) = (d+1)ρ - Tr(ρ) I`.

The model and `haarShadow` estimator are defined in `UnitarySnapshots`. This file
specializes `k2_moment` to the computational-basis projectors, evaluates the channel for
`d ≥ 2`, and proves that `ρ ↦ (d + 1)ρ - Tr(ρ) I` is both its left and right inverse.
The final corollary `haarShadow_unbiased` combines that calculation with Physlib
Born-probability normalization to recover the input state in expectation.

For the protocol, see Huang, Kueng, and Preskill, *Predicting Many Properties of a Quantum
System from Very Few Measurements*, *Nature Physics* 16, 1050–1057 (2020)
([arXiv:2002.08953](https://arxiv.org/abs/2002.08953)).
The observation numbers are the project's labels.

## Main results

* `ClassicalShadows.unitarySnapshotMoment_two`: the summed second snapshot moment, obtained
  from `k2_moment`.
* `ClassicalShadows.haarMeasurementChannel_apply`: `M(ρ) = (Tr(ρ) I + ρ)/(d + 1)`.
* `ClassicalShadows.haarMeasurementChannel_leftInverse`,
  `ClassicalShadows.haarMeasurementChannel_rightInverse`: the formula
  `M⁻¹(ρ) = (d + 1)ρ - Tr(ρ) I` inverts the actual integral channel in both directions.
* `ClassicalShadows.haarShadow_unbiased`: the Born-weighted Haar expectation of the
  reconstructed sample equals the input density state.

## Implementation notes

This is a separate entrywise argument for the continuous Haar model. No identification with
the finite weighted-snapshot model or its tensor-of-endomorphisms model is asserted.

The channel and moment operator `SchurWeyl.momentOp` are integrated entrywise in the
computational basis, avoiding a norm on `End(ℂ^d)`. The final unbiasedness theorem is a
`HermitianMat`-valued Bochner integral; private continuity and entry-integral lemmas
connect it to the channel calculation.
-/

noncomputable section

namespace ClassicalShadows

open SchurWeyl MeasureTheory Measure

variable {d : ℕ}

/-! ### Specializing the second Haar moment -/

/-- Specialize `k2_moment` to each computational-basis projector's tensor square and sum
across the `d` basis outcomes. Each projector has trace one and is idempotent, so the identity
and swap trace contractions are both one. The resulting unnormalized sum is
`(I + 𝔽)/(d + 1)`. This is a corollary of the existing second Haar moment formula.
The sum contains no Born weights. Haar invariance under `U ↦ U†` relates these
projector-orbit moments to the physical snapshots. -/
theorem unitarySnapshotMoment_two (d : ℕ) [Fact (2 ≤ d)] :
    (∑ b : Fin d, momentOp (diagAction d 2 (basisProjector d b))) =
      ((d : ℂ) + 1)⁻¹ • ((LinearMap.id : Module.End ℂ (TensV d 2)) + 𝔽 d) := by
  letI : NeZero d := ⟨by have := Fact.out (p := 2 ≤ d); omega⟩
  have hd : (d : ℂ) ≠ 0 := NeZero.natCast_ne d ℂ
  have hdm1 : (d : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr <| by exact_mod_cast Nat.ne_of_gt (Fact.out (p := 2 ≤ d))
  have hdp1 : (d : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero d
  have hd2m1 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [show (d : ℂ) ^ 2 - 1 = ((d : ℂ) - 1) * ((d : ℂ) + 1) by ring]
    exact mul_ne_zero hdm1 hdp1
  -- every summand has the same two trace contractions, both equal to `1`
  have hcoeff : (d : ℂ) * ((1 - (d : ℂ)⁻¹) / ((d : ℂ) ^ 2 - 1)) = ((d : ℂ) + 1)⁻¹ := by
    field_simp
    ring
  simp_rw [k2_moment]
  simp only [smul_eq_mul, Module.End.mul_eq_comp, trace_diagAction, trace_swap_comp_diagAction,
    basisProjector_comp_self, trace_basisProjector, one_pow, mul_one]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul, hcoeff,
    smul_add]

/-! ### The Haar measurement channel -/

/-- The entrywise Born-weighted snapshot average is the contraction against `ρ` of the
summed projector-orbit moment. Haar invariance under `U ↦ U†` identifies this orbit moment
with `∑_b 𝔼_U[(U†|b⟩⟨b|U)^{⊗2}]`; the proof makes that change of variables explicitly. -/
private theorem sum_integral_bornWeighted_snapshot (ρ : Module.End ℂ (Fin d → ℂ)) (i j : Fin d) :
    ∑ b : Fin d, ∫ U, LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ unitarySnapshot U b) *
        matrixOf (unitarySnapshot U b) i j ∂(haarProb d)
      = ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
          toEndMatrix d 2 (∑ b : Fin d, momentOp (diagAction d 2 (basisProjector d b)))
            ![p.2, i] ![p.1, j] := by
  simp_rw [_root_.map_sum, Matrix.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [trace_comp_mul_matrixOf, diagAction_unitarySnapshot]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [MeasureTheory.integral_const_mul, toEndMatrix_momentOp]
    exact congrArg _ (integral_star_haarProb (fun U => toEndMatrix d 2
      (actOn (diagAction d 2 (basisProjector d b)) U) ![p.2, i] ![p.1, j]))
  · exact fun p _ => integrable_haarProb_of_continuous (continuous_const.mul
      ((continuous_actOn_entry (diagAction d 2 (basisProjector d b)) ![p.2, i]
        ![p.1, j]).comp continuous_star))

/-- **Observation 59**, first formula: the measurement channel of the Haar-random
classical-shadow protocol is `M(ρ) = (Tr(ρ) I + ρ)/(d + 1)`. -/
theorem haarMeasurementChannel_apply [Fact (2 ≤ d)] (ρ : Module.End ℂ (Fin d → ℂ)) :
    haarMeasurementChannel d ρ =
      ((d : ℂ) + 1)⁻¹ • (LinearMap.trace ℂ (Fin d → ℂ) ρ • LinearMap.id + ρ) := by
  have hmat : (Matrix.of fun i j => ∑ b : Fin d,
      ∫ U, LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ unitarySnapshot U b) *
        matrixOf (unitarySnapshot U b) i j ∂(haarProb d)) =
      ((d : ℂ) + 1)⁻¹ •
        (LinearMap.trace ℂ (Fin d → ℂ) ρ • (1 : Matrix (Fin d) (Fin d) ℂ) + matrixOf ρ) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    -- Write the channel as a contraction of the second moment.
    rw [sum_integral_bornWeighted_snapshot]
    -- Apply the computed second-moment formula here.
    rw [unitarySnapshotMoment_two]
    -- Evaluate the identity and swap contributions.
    rw [smul_add, contract_smul_id_add_smul_swap]
    simp [Matrix.one_apply, mul_add]
  rw [haarMeasurementChannel, hmat]
  simp [show Matrix.toLin' (matrixOf ρ) = ρ from endOf_matrixOf ρ]

/-- **Observation 59**, inverse formula: applying `ρ ↦ (d + 1)ρ - Tr(ρ) I` after
the Haar measurement channel recovers the input operator. -/
theorem haarMeasurementChannel_leftInverse [Fact (2 ≤ d)]
    (ρ : Module.End ℂ (Fin d → ℂ)) :
    ((d : ℂ) + 1) • haarMeasurementChannel d ρ -
        LinearMap.trace ℂ (Fin d → ℂ) (haarMeasurementChannel d ρ) • LinearMap.id = ρ := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.depolarizingChannel_apply, LinearMap.depolarizingChannelInv_apply,
    haarMeasurementChannel_apply] using
    congrArg (fun f => f ρ) (LinearMap.depolarizingChannelInv_comp
      (V := Fin d → ℂ) (d : ℂ) (by simp) (Nat.cast_add_one_ne_zero d))

/-- **Observation 59**, inverse formula: applying the Haar measurement channel after
`ρ ↦ (d + 1)ρ - Tr(ρ) I` also recovers the input operator. -/
theorem haarMeasurementChannel_rightInverse [Fact (2 ≤ d)]
    (ρ : Module.End ℂ (Fin d → ℂ)) :
    haarMeasurementChannel d
      (((d : ℂ) + 1) • ρ - LinearMap.trace ℂ (Fin d → ℂ) ρ • LinearMap.id) = ρ := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.depolarizingChannel_apply, LinearMap.depolarizingChannelInv_apply,
    haarMeasurementChannel_apply] using
    congrArg (fun f => f ρ) (LinearMap.depolarizingChannel_comp_inv
      (V := Fin d → ℂ) (d : ℂ) (by simp) (Nat.cast_add_one_ne_zero d))

/-! ### Born-weighted Haar reconstruction -/

private lemma continuous_unitaryBasis_mats (b : Fin d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => (POVM.unitaryBasis U).mats b) := by
  unfold POVM.unitaryBasis
  apply (HermitianMat.continuous_conj _).comp
  fun_prop

private lemma continuous_bornWeighted_snapshot (ρ : MState (Fin d)) (b : Fin d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      ((POVM.unitaryBasis U).measure ρ b : ℝ) • (POVM.unitaryBasis U).mats b) :=
  ((continuous_unitaryBasis_mats b).inner continuous_const).smul (continuous_unitaryBasis_mats b)

private lemma continuous_bornWeighted_snapshots (ρ : MState (Fin d)) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      ∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) • (POVM.unitaryBasis U).mats b) :=
  continuous_finsetSum _ fun b _ => continuous_bornWeighted_snapshot ρ b

/-- The `(i, j)` matrix entry of a Hermitian matrix, as a continuous `ℝ`-linear functional. -/
private def entryCLM (i j : Fin d) : HermitianMat (Fin d) ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℝ] ℂ).comp
    ((ContinuousLinearMap.proj i : Matrix (Fin d) (Fin d) ℂ →L[ℝ] (Fin d → ℂ)).comp
      (HermitianMat.matₗ (R := ℝ)))

/-- Entries of the Haar average of a continuous `HermitianMat`-valued function are the Haar
averages of its entries. Stated with `Continuous`, so no `ContinuousENorm` instance on
`HermitianMat` has to be synthesized. -/
private lemma mat_integral_apply {f : Matrix.unitaryGroup (Fin d) ℂ → HermitianMat (Fin d) ℂ}
    (hf : Continuous f) (i j : Fin d) :
    (∫ U, f U ∂haarProb d).mat i j = ∫ U, (f U).mat i j ∂haarProb d :=
  ((entryCLM i j).integral_comp_comm
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm

private lemma integral_bornWeighted_snapshots [Fact (2 ≤ d)] (ρ : MState (Fin d)) :
    (∫ U, (∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) •
      (POVM.unitaryBasis U).mats b) ∂haarProb d) =
      ((d : ℝ) + 1)⁻¹ • (1 + ρ.M) := by
  have ht : LinearMap.trace ℂ (Fin d → ℂ) (endOf ρ.m) = 1 := by
    rw [← trace_matrixOf, matrixOf_endOf]
    exact ρ.tr'
  have hc := congrArg matrixOf (haarMeasurementChannel_apply (endOf ρ.m))
  rw [haarMeasurementChannel_eq_integral_measure, ht, one_smul] at hc
  apply HermitianMat.ext
  ext i j
  rw [mat_integral_apply (continuous_bornWeighted_snapshots ρ)]
  simp only [HermitianMat.mat_finset_sum, HermitianMat.mat_smul, Matrix.sum_apply,
    Matrix.smul_apply]
  rw [integral_finsetSum]
  · have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) hc
    simp only [matrixOf, endOf, LinearMap.toMatrix_eq_toMatrix', map_smul, map_add,
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id, Matrix.of_apply,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at he
    simpa only [← matrixOf_unitarySnapshot, HermitianMat.mat_smul,
      HermitianMat.mat_add, HermitianMat.mat_one, Matrix.smul_apply, Matrix.add_apply,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one] using he
  · intro b _
    exact integrable_haarProb_of_continuous
      ((entryCLM i j).continuous.comp (continuous_bornWeighted_snapshot ρ b))

/-- The Born-weighted expectation of the Haar shadow equals the unknown input state.
The integral samples the basis with `haarProb`; the inner sum samples its Born outcome. -/
lemma haarShadow_unbiased [Fact (2 ≤ d)] (ρ : MState (Fin d)) :
    (∫ U, (∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) • haarShadow U b)
      ∂haarProb d) = ρ.M := by
  have hsum (U : Matrix.unitaryGroup (Fin d) ℂ) :
      ∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) • haarShadow U b =
        ((d : ℝ) + 1) • (∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) •
          (POVM.unitaryBasis U).mats b) - 1 := by
    simp only [haarShadow, smul_sub, smul_comm _ ((d : ℝ) + 1),
      Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.sum_smul,
      ProbDistribution.normalized, one_smul]
  simp_rw [hsum]
  rw [integral_sub]
  · rw [integral_smul, integral_bornWeighted_snapshots, integral_const]
    simp only [probReal_univ, one_smul, smul_smul,
      mul_inv_cancel₀ (by positivity : (d : ℝ) + 1 ≠ 0)]
    abel
  · exact ((continuous_bornWeighted_snapshots ρ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).smul ((d : ℝ) + 1)
  · exact integrable_const _

end ClassicalShadows
