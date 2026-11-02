/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QuantumInfo.Measurements.POVM

/-!
# Unitary-basis measurements

Local extensions intended for contribution to Physlib. The `POVM` type and its
`measure` probabilities already come from Physlib; this module adds measurement in
a unitary-rotated computational basis and the trace formula for those probabilities.

These extensions depend only on Physlib and are not yet upstream. LeanHaar-specific
snapshot conversions and Haar averaging belong in the classical-shadow application.
-/

noncomputable section
open scoped BigOperators ComplexOrder RealInnerProductSpace

namespace POVM

/-- The computational-basis measurement after applying the unitary `U`.
Its effects are `U† |b⟩⟨b| U`. -/
def unitaryBasis {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) : POVM n n where
  mats b := HermitianMat.conj ((U : Matrix n n ℂ).conjTranspose)
    ⟨Matrix.single b b 1, by
      change (Matrix.single b b (1 : ℂ)).IsHermitian
      simp [Matrix.IsHermitian]⟩
  nonneg b := HermitianMat.conj_nonneg _ (HermitianMat.zero_le_iff.mpr
    ((Matrix.PosSemidef.stdBasisMatrix_iff_eq b b (zero_lt_one' ℂ)).2 rfl))
  normalized := by
    apply HermitianMat.ext
    simp only [HermitianMat.mat_finset_sum, HermitianMat.conj_apply_mat,
      HermitianMat.mat_mk, HermitianMat.mat_one, Matrix.conjTranspose_conjTranspose]
    rw [← Finset.sum_mul, ← Finset.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
    exact U.prop.1

/-- The matrix of a rotated-basis effect is `U† |b⟩⟨b| U`. -/
@[simp] theorem unitaryBasis_mats_mat {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (b : n) :
    ((unitaryBasis U).mats b).mat =
      star (U : Matrix n n ℂ) * Matrix.single b b 1 * (U : Matrix n n ℂ) := by
  simp [unitaryBasis, HermitianMat.conj_apply_mat, Matrix.star_eq_conjTranspose]

/-- A POVM's outcome probability is the Born trace coefficient. -/
theorem measure_eq_trace {n X : Type*} [Fintype n] [DecidableEq n]
    [Fintype X] (E : POVM X n) (ρ : MState n) (x : X) :
    (((E.measure ρ) x : ℝ) : ℂ) = Matrix.trace (ρ.m * (E.mats x).mat) := by
  change ((⟪E.mats x, ρ.M⟫ : ℝ) : ℂ) = _
  calc
    _ = ((E.mats x).mat * ρ.M.mat).trace := HermitianMat.inner_eq_trace_rc _ _
    _ = _ := Matrix.trace_mul_comm _ _

end POVM
