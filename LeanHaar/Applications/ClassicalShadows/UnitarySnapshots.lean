/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.TensorPower
import LeanHaar.SupportingDocs.TensorPowerTraces
import LeanHaar.ForPhyslib.POVM

/-!
# The physical ensemble of Haar-random unitary snapshots

This file introduces the snapshots `U† |b⟩⟨b| U` actually recorded by the classical-shadow
experiment on `ℂ^d`, relates their tensor powers to the unitary conjugation orbit used by the
Haar moment operator of the framework, and defines the Born-weighted Haar measurement
channel and reconstructed estimator `haarShadow`. The four definitions precede their
elementary projector, Born-rule, and orbit lemmas. Observation59 applies `k2_moment`
to evaluate the summed second moment and prove the channel formula, its inverse identities,
and `haarShadow_unbiased`.

The physical protocol follows Huang, Kueng, and Preskill,
[Predicting Many Properties of a Quantum System from Very Few Measurements](
https://arxiv.org/abs/2002.08953), *Nature Physics* 16, 1050–1057 (2020).

## Main definitions

* `ClassicalShadows.basisProjector`: the computational-basis projector `|b⟩⟨b|`.
* `ClassicalShadows.unitarySnapshot`: the physical snapshot `U† |b⟩⟨b| U`.
* `ClassicalShadows.haarMeasurementChannel`: the entrywise Haar integral of Born-weighted
  snapshots, summed over measurement outcomes.
* `ClassicalShadows.haarShadow`: the reconstructed Hermitian sample `(d + 1) S(U,b) - I`.
  It depends only on the recorded unitary and outcome and need not be positive.

## Main results

* `ClassicalShadows.measure_unitaryBasis`: Physlib's outcome probability equals the
  trace coefficient of the recorded snapshot.
* `ClassicalShadows.haarMeasurementChannel_eq_integral_measure`: on physical states,
  the channel is the Haar average of snapshots weighted by `POVM.measure`.
* `ClassicalShadows.diagAction_unitarySnapshot`: `(U† |b⟩⟨b| U)^{⊗k}` is the point of the
  conjugation orbit of `(|b⟩⟨b|)^{⊗k}` at the parameter `U†`.

The evaluated theorem `ClassicalShadows.unitarySnapshotMoment_two` belongs to Observation59;
this module does not import a computed Haar-moment formula.
-/

noncomputable section

namespace ClassicalShadows

open SchurWeyl MeasureTheory

/-! ### Protocol definitions -/

/-- The computational-basis projector `|b⟩⟨b|` on `ℂ^d`. -/
def basisProjector (d : ℕ) (b : Fin d) : Module.End ℂ (Fin d → ℂ) :=
  Matrix.toLin' (Matrix.single b b 1)

/-- The classical snapshot `U† |b⟩⟨b| U` recorded by the experiment. -/
def unitarySnapshot {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (b : Fin d) :
    Module.End ℂ (Fin d → ℂ) :=
  endOf (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ basisProjector d b ∘ₗ
    endOf (U : Matrix (Fin d) (Fin d) ℂ)

/-- The **measurement channel** of the Haar-random classical-shadow protocol on `ℂ^d`:
`M(ρ) = ∑_b 𝔼_{U∼μ}[⟨b|UρU†|b⟩ · U†|b⟩⟨b|U]`.
The trace coefficient equals Physlib's `POVM.measure` on a physical state, as proved in
`measure_unitaryBasis`; `haarProb` supplies the sampling law for `U`. The formula extends
linearly to arbitrary operators and takes the Haar average entrywise. -/
def haarMeasurementChannel (d : ℕ) (ρ : Module.End ℂ (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ) :=
  Matrix.toLin' (Matrix.of fun i j => ∑ b : Fin d,
    ∫ U, LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ unitarySnapshot U b) *
      matrixOf (unitarySnapshot U b) i j ∂(haarProb d))

/-- The reconstructed snapshot `(d + 1) U†|b⟩⟨b|U - I` for a global Haar basis measurement.
The setting and observed outcome determine the estimate; the unknown state does not. -/
def haarShadow {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (b : Fin d) :
    HermitianMat (Fin d) ℂ :=
  ((d : ℝ) + 1) • (POVM.unitaryBasis U).mats b - 1

/-! ### Elementary projector and orbit identities -/

/-- Each computational-basis projector has trace one. -/
@[simp] theorem trace_basisProjector (d : ℕ) (b : Fin d) :
    LinearMap.trace ℂ (Fin d → ℂ) (basisProjector d b) = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin d))]
  simp [basisProjector, Matrix.trace]

/-- Each computational-basis projector is idempotent. -/
@[simp] theorem basisProjector_comp_self (d : ℕ) (b : Fin d) :
    basisProjector d b ∘ₗ basisProjector d b = basisProjector d b := by
  rw [basisProjector, ← Matrix.toLin'_mul, Matrix.single_mul_single_same, one_mul]

/-- The endomorphism snapshot and Physlib's rotated-basis effect have the same matrix. -/
@[simp] theorem matrixOf_unitarySnapshot {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (b : Fin d) :
    matrixOf (unitarySnapshot U b) = ((POVM.unitaryBasis U).mats b).mat := by
  simp [POVM.unitaryBasis_mats_mat, unitarySnapshot, matrixOf, endOf, basisProjector,
    LinearMap.toMatrix'_comp, Matrix.mul_assoc]

/-- Physlib's probability for the rotated-basis measurement is the snapshot's Born trace.
Nonnegativity and normalization are supplied by `POVM.measure` and `MState`. -/
theorem measure_unitaryBasis {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : MState (Fin d)) (b : Fin d) :
    (((POVM.unitaryBasis U).measure ρ b : ℝ) : ℂ) =
      LinearMap.trace ℂ (Fin d → ℂ) (endOf ρ.m ∘ₗ unitarySnapshot U b) := by
  rw [POVM.measure_eq_trace, ← trace_matrixOf, matrixOf_comp, matrixOf_unitarySnapshot,
    matrixOf_endOf]

/-- On a physical state, the Haar channel averages the recorded snapshots with Physlib's
Born probabilities for each fixed `U` and LeanHaar's Haar probability measure for `U`. -/
theorem haarMeasurementChannel_eq_integral_measure {d : ℕ} (ρ : MState (Fin d)) :
    haarMeasurementChannel d (endOf ρ.m) =
      Matrix.toLin' (Matrix.of fun i j => ∑ b : Fin d,
        ∫ U, (((POVM.unitaryBasis U).measure ρ b : ℝ) : ℂ) *
          matrixOf (unitarySnapshot U b) i j ∂(haarProb d)) := by
  simp_rw [measure_unitaryBasis]
  rfl

/-- Taking tensor powers commutes with forming the physical snapshot: the tensor power
`(U† |b⟩⟨b| U)^{⊗k}` is the point of the conjugation orbit of `(|b⟩⟨b|)^{⊗k}` at the
parameter `U†`. -/
theorem diagAction_unitarySnapshot {d k : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (b : Fin d) :
    diagAction d k (unitarySnapshot U b) =
      actOn (diagAction d k (basisProjector d b)) (star U) := by
  rw [unitarySnapshot, actOn, ← diagAction_comp, ← diagAction_comp]
  congr 1
  simp

end ClassicalShadows
