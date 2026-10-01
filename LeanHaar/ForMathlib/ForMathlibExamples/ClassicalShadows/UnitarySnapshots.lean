/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.TensorPower
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TensorPowerTraces
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.DepolarizingChannel

/-!
# The physical ensemble of Haar-random unitary snapshots

This file introduces the snapshots `U† |b⟩⟨b| U` actually recorded by the classical-shadow
experiment on `ℂ^d`, relates their tensor powers to the unitary conjugation orbit used by the
Haar moment operator of the framework, and defines the Born-weighted Haar measurement
channel. All five protocol definitions precede their elementary projector and orbit lemmas.
Observation59 applies `k2_moment` to evaluate the summed second moment and identify the
integral channel with the explicit invertible isotropic map defined here.

## Main definitions

* `ClassicalShadows.basisProjector`: the computational-basis projector `|b⟩⟨b|`.
* `ClassicalShadows.unitarySnapshot`: the physical snapshot `U† |b⟩⟨b| U`.
* `ClassicalShadows.unitarySnapshotMoment`: `∑_b 𝔼_{U∼μ}[(U† |b⟩⟨b| U)^{⊗k}]`.
  This sums over outcomes without dividing by `d` or inserting Born weights.
* `ClassicalShadows.haarMeasurementChannel`: the entrywise Haar integral of Born-weighted
  snapshots, summed over measurement outcomes.
* `ClassicalShadows.haarMeasurementChannelEquiv`: the explicit isotropic equivalence;
  Observation59 proves that it equals the integral channel for `d ≥ 2`.

## Main results

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

/-- The `k`-th Haar moment of the physical snapshot ensemble, summed over the computational
basis: `∑ b, 𝔼_{U∼μ}[(U† |b⟩⟨b| U)^{⊗k}]`. Haar invariance under `U ↦ U†` lets one write it
through the moment operator of the projectors `|b⟩⟨b|`. The sum is unnormalized over
basis outcomes and contains no state-dependent Born weight. -/
def unitarySnapshotMoment (d k : ℕ) : Module.End ℂ (TensV d k) :=
  ∑ b : Fin d, momentOp (diagAction d k (basisProjector d b))

/-- The **measurement channel** of the Haar-random classical-shadow protocol on `ℂ^d`:
`M(ρ) = ∑_b 𝔼_{U∼μ}[⟨b|UρU†|b⟩ · U†|b⟩⟨b|U]`, where the Born weight `⟨b|UρU†|b⟩` is written as
`Tr(ρ S)` for the snapshot `S = U†|b⟩⟨b|U`. The Haar average is taken entrywise in the
computational basis. -/
def haarMeasurementChannel (d : ℕ) (ρ : Module.End ℂ (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ) :=
  Matrix.toLin' (Matrix.of fun i j => ∑ b : Fin d,
    ∫ U, LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ unitarySnapshot U b) *
      matrixOf (unitarySnapshot U b) i j ∂(haarProb d))

/-- The explicit isotropic map on `ℂ^d`, packaged with its algebraic inverse.
This specialization is defined for every `d`. Its identification with the Haar measurement
channel for `d ≥ 2` is proved in `haarMeasurementChannelEquiv_apply` in Observation59. -/
def haarMeasurementChannelEquiv (d : ℕ) :
    Module.End ℂ (Fin d → ℂ) ≃ₗ[ℂ] Module.End ℂ (Fin d → ℂ) :=
  LinearMap.depolarizingChannelEquiv (V := Fin d → ℂ) (d : ℂ) (by simp)
    (Nat.cast_add_one_ne_zero (R := ℂ) d)

/-! ### Elementary projector and orbit identities -/

@[simp] theorem trace_basisProjector (d : ℕ) (b : Fin d) :
    LinearMap.trace ℂ (Fin d → ℂ) (basisProjector d b) = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin d))]
  simp [basisProjector, Matrix.trace]

@[simp] theorem basisProjector_comp_self (d : ℕ) (b : Fin d) :
    basisProjector d b ∘ₗ basisProjector d b = basisProjector d b := by
  rw [basisProjector, ← Matrix.toLin'_mul, Matrix.single_mul_single_same, one_mul]

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
