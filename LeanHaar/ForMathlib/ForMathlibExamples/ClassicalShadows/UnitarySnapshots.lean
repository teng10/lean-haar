/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TensorPowerTraces

/-!
# The physical ensemble of Haar-random unitary snapshots

This file introduces the snapshots `U† |b⟩⟨b| U` actually recorded by the classical-shadow
experiment on `ℂ^d`, relates their tensor powers to the unitary conjugation orbit used by the
Haar moment operator of the framework, and evaluates the second Haar moment of the ensemble.

## Main definitions

* `ClassicalShadows.basisProjector`: the computational-basis projector `|b⟩⟨b|`.
* `ClassicalShadows.unitarySnapshot`: the physical snapshot `U† |b⟩⟨b| U`.
* `ClassicalShadows.unitarySnapshotMoment`: `∑_b 𝔼_{U∼μ}[(U† |b⟩⟨b| U)^{⊗k}]`.

## Main results

* `ClassicalShadows.diagAction_unitarySnapshot`: `(U† |b⟩⟨b| U)^{⊗k}` is the point of the
  conjugation orbit of `(|b⟩⟨b|)^{⊗k}` at the parameter `U†`.
* `ClassicalShadows.unitarySnapshotMoment_two`: the second Haar moment of the ensemble is
  `(I + 𝔽)/(d + 1)`, for `d ≥ 2`.
-/

noncomputable section

namespace ClassicalShadows

open SchurWeyl

/-- The computational-basis projector `|b⟩⟨b|` on `ℂ^d`. -/
def basisProjector (d : ℕ) (b : Fin d) : Module.End ℂ (Fin d → ℂ) :=
  Matrix.toLin' (Matrix.single b b 1)

@[simp] theorem trace_basisProjector (d : ℕ) (b : Fin d) :
    LinearMap.trace ℂ (Fin d → ℂ) (basisProjector d b) = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin d))]
  simp [basisProjector, Matrix.trace]

@[simp] theorem basisProjector_comp_self (d : ℕ) (b : Fin d) :
    basisProjector d b ∘ₗ basisProjector d b = basisProjector d b := by
  rw [basisProjector, ← Matrix.toLin'_mul, Matrix.single_mul_single_same, one_mul]

/-- The classical snapshot `U† |b⟩⟨b| U` recorded by the experiment. -/
def unitarySnapshot {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (b : Fin d) :
    Module.End ℂ (Fin d → ℂ) :=
  endOf (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ basisProjector d b ∘ₗ
    endOf (U : Matrix (Fin d) (Fin d) ℂ)

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

/-- The `k`-th Haar moment of the physical snapshot ensemble, summed over the computational
basis: `∑ b, 𝔼_{U∼μ}[(U† |b⟩⟨b| U)^{⊗k}]`. Haar invariance under `U ↦ U†` lets one write it
through the moment operator of the projectors `|b⟩⟨b|`. -/
def unitarySnapshotMoment (d k : ℕ) : Module.End ℂ (TensV d k) :=
  ∑ b : Fin d, momentOp (diagAction d k (basisProjector d b))

@[simp] theorem trace_diagAction_basisProjector (d k : ℕ) (b : Fin d) :
    LinearMap.trace ℂ (TensV d k) (diagAction d k (basisProjector d b)) = 1 := by
  simp [trace_diagAction]

@[simp] theorem trace_swap_comp_diagAction_basisProjector (d : ℕ) (b : Fin d) :
    LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ diagAction d 2 (basisProjector d b)) = 1 := by
  simp [trace_swap_comp_diagAction]

/-- The second-order Haar moment of the physical snapshot ensemble is `(I + F)/(d + 1)`.
By Schur--Weyl duality the Haar twirl of `(|b⟩⟨b|)^{⊗2}` lies in the span of the identity
and the swap, and its two trace contractions, both equal to `1`, pin down the
coefficients. -/
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
  simp_rw [k2_moment, show ∀ b, LinearMap.trace ℂ (TensV d 2)
      (𝔽 d • diagAction d 2 (basisProjector d b)) = 1 from
    trace_swap_comp_diagAction_basisProjector d]
  simp only [smul_eq_mul, trace_diagAction_basisProjector, mul_one]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul, hcoeff,
    smul_add]

end ClassicalShadows
