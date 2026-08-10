import Mathlib.MeasureTheory.Measure.Haar.Unique
import LeanHaar.ForMathlib.ForMathlibExamples.k1Moment

/-!
# Invariance properties of the Haar probability measure on the unitary group

The unitary group is compact, so its left invariant Haar probability measure `SchurWeyl.haarProb`
is also right invariant, and hence invariant under `U ↦ U⁻¹`. The inversion invariance is what
allows the quantum machine learning example to average expressions such as `U† O U` over the
group.

## Main declarations

* `QML.instIsHaarMeasureHaarProb`: `haarProb d` is a Haar measure.
* `QML.instIsMulRightInvariantHaarProb`: it is right invariant.
* `QML.instIsInvInvariantHaarProb`: it is invariant under inversion.
-/

noncomputable section

open Matrix MeasureTheory SchurWeyl

namespace QML

/-- `haarProb d` is a Haar measure: it is a positive multiple of `Measure.haar`. -/
instance instIsHaarMeasureHaarProb (d : ℕ) : (haarProb d).IsHaarMeasure := by
  unfold haarProb
  exact Measure.IsHaarMeasure.smul _ (by simp [haar_univ_ne_top d])
    (by simp [haar_univ_ne_zero d])

/-- On the compact unitary group the left invariant Haar probability measure is also right
invariant: right translation is again a left invariant probability measure, so it is a multiple
of `haarProb d`, and comparing total masses shows the multiple is `1`. -/
instance instIsMulRightInvariantHaarProb (d : ℕ) : (haarProb d).IsMulRightInvariant := by
  constructor
  intro g
  set c := Measure.haarScalarFactor (Measure.map (· * g) (haarProb d)) (haarProb d)
  have hmap : Measure.map (· * g) (haarProb d) = c • haarProb d :=
    Measure.isMulInvariant_eq_smul_of_compactSpace _ _
  have huniv : (Measure.map (· * g) (haarProb d)) Set.univ = 1 := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  rw [hmap] at huniv
  have hc : c = 1 := by simpa [ENNReal.smul_def] using huniv
  rw [hmap, hc, one_smul]

/-- Consequently `haarProb d` is invariant under inversion. -/
instance instIsInvInvariantHaarProb (d : ℕ) : (haarProb d).IsInvInvariant := by
  set c := Measure.haarScalarFactor (haarProb d).inv (haarProb d)
  have hinv : (haarProb d).inv = c • haarProb d :=
    Measure.isMulInvariant_eq_smul_of_compactSpace _ _
  have huniv : ((haarProb d).inv) Set.univ = 1 := by
    rw [Measure.inv, Measure.map_apply measurable_inv MeasurableSet.univ]
    simp
  rw [hinv] at huniv
  have hc : c = 1 := by simpa [ENNReal.smul_def] using huniv
  exact ⟨by rw [hinv, hc, one_smul]⟩

end QML

end
