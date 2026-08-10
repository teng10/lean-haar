/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.Haar
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Invariance properties of the Haar probability measure on the unitary group

This file collects the invariance properties of the Haar probability measure
`SchurWeyl.haarProb` on the unitary group `U(d)` that the examples need. The unitary group is
compact, so its left invariant Haar probability measure is also right invariant, and hence
invariant under `g ↦ g⁻¹`:

* the classical-shadow protocol records the snapshots `U† |b⟩⟨b| U`, that is, conjugations by
  `U†`, while the Haar moment operator of the framework averages conjugations by `U`;
* the quantum machine learning example averages expressions such as `U† O U` over the group.

Both uses are served by the same statements, which are therefore proved here once.

## Main results

* `MeasureTheory.Measure.modularCharacterFun_eq_one_of_compactSpace`: the modular character of
  a Haar probability measure on a compact group is trivial.
* `MeasureTheory.Measure.isMulRightInvariant_of_compactSpace`: such a measure is right
  invariant.
* `MeasureTheory.Measure.isInvInvariant_of_compactSpace`: an inner regular Haar probability
  measure on a compact group is invariant under `g ↦ g⁻¹`.
* `SchurWeyl.instIsHaarMeasureHaarProb`, `SchurWeyl.instInnerRegularHaarProb`,
  `SchurWeyl.instIsMulRightInvariantHaarProb`, `SchurWeyl.instIsInvInvariantHaarProb`: the
  corresponding instances for the Haar probability measure on `U(d)`.
* `SchurWeyl.integral_star_haarProb`: Haar averages over `U(d)` are unchanged by `U ↦ U†`.
* `SchurWeyl.integrable_haarProb_of_continuous`: a continuous function on the compact group
  `U(d)` is Haar integrable.
-/

noncomputable section

open MeasureTheory

namespace MeasureTheory.Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- On a compact group the modular character of a Haar probability measure is trivial: the
translated measure `μ(· * g)` is `modularCharacterFun g • μ`, and both are probability
measures. -/
theorem modularCharacterFun_eq_one_of_compactSpace (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] (g : G) : modularCharacterFun g = 1 := by
  have h := map_right_mul_eq_modularCharacterFun_smul μ g
  have h₁ : (map (fun x => x * g) μ) Set.univ = (modularCharacterFun g • μ) Set.univ := by rw [h]
  rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Measure.smul_apply] at h₁
  simp only [Set.preimage_univ, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at h₁
  exact_mod_cast h₁.symm

/-- On a compact group a Haar probability measure is right invariant, since its modular
character is trivial. -/
theorem isMulRightInvariant_of_compactSpace (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] : μ.IsMulRightInvariant :=
  ⟨fun g => by
    rw [map_right_mul_eq_modularCharacterFun_smul μ g,
      modularCharacterFun_eq_one_of_compactSpace μ g]
    simp⟩

/-- On a compact group, a Haar probability measure is invariant under inversion. Indeed `μ` is
right invariant by `isMulRightInvariant_of_compactSpace`, so `μ.inv` is a left-invariant
probability measure, and uniqueness of Haar measure forces `μ.inv = μ`. -/
theorem isInvInvariant_of_compactSpace (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] [μ.InnerRegular] : μ.IsInvInvariant := by
  have : μ.IsMulRightInvariant := isMulRightInvariant_of_compactSpace μ
  have : IsProbabilityMeasure μ.inv := ⟨by rw [Measure.inv_apply]; simp⟩
  have h := isMulLeftInvariant_eq_smul_of_innerRegular μ.inv μ
  have huniv : μ.inv Set.univ = (μ.inv.haarScalarFactor μ • μ) Set.univ := by rw [← h]
  rw [Measure.smul_apply] at huniv
  simp only [measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at huniv
  have h_scalar : μ.inv.haarScalarFactor μ = 1 := by exact_mod_cast huniv.symm
  exact ⟨by rw [h, h_scalar, one_smul]⟩

end MeasureTheory.Measure

namespace SchurWeyl

/-- The Haar probability measure on `U(d)` is a Haar measure: it is a positive multiple of
`Measure.haar`. -/
instance instIsHaarMeasureHaarProb (d : ℕ) : (haarProb d).IsHaarMeasure :=
  Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr (haar_univ_ne_top d))
    (ENNReal.inv_ne_top.mpr (haar_univ_ne_zero d))

/-- The Haar probability measure on `U(d)` is inner regular. -/
instance instInnerRegularHaarProb (d : ℕ) : (haarProb d).InnerRegular := by
  unfold haarProb; infer_instance

/-- The unitary group is compact, so its Haar probability measure is right invariant. -/
instance instIsMulRightInvariantHaarProb (d : ℕ) : (haarProb d).IsMulRightInvariant :=
  Measure.isMulRightInvariant_of_compactSpace _

/-- The unitary group is compact, so its Haar probability measure is invariant under
`U ↦ U†`. -/
instance instIsInvInvariantHaarProb (d : ℕ) : (haarProb d).IsInvInvariant :=
  Measure.isInvInvariant_of_compactSpace _

variable {d : ℕ}

/-- Haar averages are unchanged by `U ↦ U†`. -/
theorem integral_star_haarProb (f : Matrix.unitaryGroup (Fin d) ℂ → ℂ) :
    ∫ U, f (star U) ∂(haarProb d) = ∫ U, f U ∂(haarProb d) := by
  simpa using integral_inv_eq_self f (haarProb d)

/-- A continuous function on the compact group `U(d)` is Haar integrable. -/
theorem integrable_haarProb_of_continuous {f : Matrix.unitaryGroup (Fin d) ℂ → ℂ}
    (hf : Continuous f) : Integrable f (haarProb d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end SchurWeyl

end
