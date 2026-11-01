/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Applications.ClassicalShadows.Observation59
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Haar classical shadows

`haarShadow U b` reconstructs the recorded outcome of a global Haar-random basis measurement.
It is a Hermitian matrix, not necessarily a positive state, and needs only the experimental
record `(U, b)`. Physlib supplies the Born probabilities in `haarShadow_unbiased`.

Unbiasedness follows directly from Observation 59's existing second-Haar-moment calculation
and normalization of the Born probabilities. The dimension restriction `d ≥ 2` belongs to
the existing moment calculation; the estimator's formula is defined without it.
-/

noncomputable section
open MeasureTheory SchurWeyl
namespace ClassicalShadows
variable {d : ℕ}
local instance : ContinuousENorm (HermitianMat (Fin d) ℂ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The reconstructed snapshot `(d + 1) U†|b⟩⟨b|U - I` for a global Haar basis measurement.
The setting and observed outcome determine the estimate; the unknown state does not. -/
def haarShadow (U : Matrix.unitaryGroup (Fin d) ℂ) (b : Fin d) :
    HermitianMat (Fin d) ℂ :=
  ((d : ℝ) + 1) • (POVM.unitaryBasis U).mats b - 1

private lemma unitaryBasis_mat_eq_snapshot (U : Matrix.unitaryGroup (Fin d) ℂ) (b : Fin d) :
    ((POVM.unitaryBasis U).mats b).mat = matrixOf (unitarySnapshot U b) := by
  simp [POVM.unitaryBasis, unitarySnapshot, matrixOf, endOf, basisProjector,
    LinearMap.toMatrix'_comp, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

private lemma continuous_unitaryBasis_mats (b : Fin d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => (POVM.unitaryBasis U).mats b) := by
  unfold POVM.unitaryBasis
  apply (HermitianMat.continuous_conj _).comp
  fun_prop

private lemma continuous_bornWeighted_snapshot (ρ : MState (Fin d)) (b : Fin d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      ((POVM.unitaryBasis U).measure ρ b : ℝ) • (POVM.unitaryBasis U).mats b) := by
  exact ((continuous_unitaryBasis_mats b).inner continuous_const).smul
    (continuous_unitaryBasis_mats b)

private lemma integrable_bornWeighted_snapshots (ρ : MState (Fin d)) :
    Integrable (fun U => ∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) •
      (POVM.unitaryBasis U).mats b) (haarProb d) :=
  (continuous_finsetSum _ (fun b _ => continuous_bornWeighted_snapshot ρ b)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private lemma integral_bornWeighted_snapshots [Fact (2 ≤ d)] (ρ : MState (Fin d)) :
    (∫ U, (∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) •
      (POVM.unitaryBasis U).mats b) ∂haarProb d) =
      ((d : ℝ) + 1)⁻¹ • (1 + ρ.M) := by
  letI : NeZero d := ⟨by have := Fact.out (p := 2 ≤ d); omega⟩
  have ht : LinearMap.trace ℂ (Fin d → ℂ) (endOf ρ.m) = 1 := by
    rw [← trace_matrixOf]
    simpa only [matrixOf, endOf, LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin'] using ρ.tr'
  have hc := congrArg matrixOf (haarMeasurementChannel_apply (endOf ρ.m))
  rw [haarMeasurementChannel_eq_integral_measure, ht, one_smul] at hc
  apply HermitianMat.ext
  ext i j
  let L : HermitianMat (Fin d) ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℝ] ℂ).comp
      ((ContinuousLinearMap.proj i : Matrix (Fin d) (Fin d) ℂ →L[ℝ] (Fin d → ℂ)).comp
        (HermitianMat.matₗ (R := ℝ)))
  have hL := L.integral_comp_comm (integrable_bornWeighted_snapshots ρ)
  change _ = L (∫ U, (∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) •
    (POVM.unitaryBasis U).mats b) ∂haarProb d) at hL
  change L (∫ U, (∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) •
    (POVM.unitaryBasis U).mats b) ∂haarProb d) = _
  rw [← hL]
  simp only [map_sum, map_smul]
  change (∫ U, (∑ b, ((POVM.unitaryBasis U).measure ρ b : ℝ) •
    ((POVM.unitaryBasis U).mats b).mat i j) ∂haarProb d) = _
  rw [integral_finsetSum]
  · have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) hc
    simp only [matrixOf, endOf, LinearMap.toMatrix_eq_toMatrix', map_smul, map_add,
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id, Matrix.of_apply,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at he
    simpa only [unitaryBasis_mat_eq_snapshot, HermitianMat.mat_smul,
      HermitianMat.mat_add, HermitianMat.mat_one, Matrix.smul_apply, Matrix.add_apply,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one] using he
  · intro b _
    exact (L.continuous.comp (continuous_bornWeighted_snapshot ρ b)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

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
  · exact (integrable_bornWeighted_snapshots ρ).smul ((d : ℝ) + 1)
  · exact integrable_const _
end ClassicalShadows
