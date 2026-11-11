/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Circuits.Schedule
import LeanHaar.Circuits.HaarMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independent circuit moments

Independent samples are indexed by gate occurrence, including repeated uses of
the same gate location. The factorization theorem is valid for arbitrary finite
sampling measures on a compact sample space; Haar randomness is a specialization.
All equalities hold as full superoperators, not just on product-state inputs.
-/

noncomputable section

open MeasureTheory

namespace SchurWeyl.Circuits

section Factorization

variable {α A : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A finite independent chronological product averages to the chronological
product of its averages. No commutation assumption on the operators is needed. -/
theorem integral_scheduleProduct {length : ℕ}
    (operators : Fin length → α → A)
    (hoperators : ∀ i, Continuous (operators i))
    (measures : Fin length → Measure α) [∀ i, IsFiniteMeasure (measures i)] :
    (∫ samples, scheduleProduct (fun i => operators i (samples i))
      ∂Measure.pi measures) =
    scheduleProduct (fun i => ∫ sample, operators i sample ∂measures i) := by
  induction length with
  | zero => simp [measureReal_def]
  | succ length ih =>
    have htail : Integrable
        (fun samples : Fin length → α =>
          scheduleProduct (fun i => operators i.succ (samples i)))
        (Measure.pi (fun i => measures i.succ)) :=
      (continuous_scheduleProduct _ (fun i => hoperators i.succ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hfirst : Integrable (operators 0) (measures 0) :=
      (hoperators 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      _ = ∫ samples : α × (Fin length → α),
          scheduleProduct (fun i => operators i.succ (samples.2 i)) * operators 0 samples.1
          ∂((measures 0).prod (Measure.pi (fun i => measures i.succ))) := by
        rw [← ((measurePreserving_piFinSuccAbove measures 0).symm).integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          scheduleProduct_succ, Fin.cons_zero, Fin.cons_succ, cast_eq]
      _ = (∫ samples : Fin length → α,
          scheduleProduct (fun i => operators i.succ (samples i))
          ∂Measure.pi (fun i => measures i.succ)) *
          (∫ sample, operators 0 sample ∂measures 0) := by
        exact integral_prod_bilin (ContinuousLinearMap.mul ℂ A).flip hfirst htail
      _ = scheduleProduct (fun i => ∫ sample, operators i sample ∂measures i) := by
        rw [ih _ (fun i => hoperators i.succ), scheduleProduct_succ]

end Factorization

/-- Multiplication of sampled unitaries agrees with chronological composition of
their vectorized conjugations. -/
theorem vecActOn_scheduleProduct {d k length : ℕ}
    (gates : Fin length → Matrix.unitaryGroup (Fin d) ℂ) :
    vecActOn (k := k) (scheduleProduct gates) =
      scheduleProduct (fun i => vecActOn (k := k) (gates i)) := by
  exact map_scheduleProduct (vecActOnHom d k).toMonoidHom gates

/-- Independent sampled gate families, with a deterministic continuous placement
at each occurrence. This is the interface for local Haar circuits. -/
theorem integral_vecActOn_placed_schedule {d D k length : ℕ}
    (placements : Fin length → Matrix.unitaryGroup (Fin d) ℂ →
      Matrix.unitaryGroup (Fin D) ℂ)
    (hplacements : ∀ i, Continuous (placements i))
    (measures : Fin length → Measure (Matrix.unitaryGroup (Fin d) ℂ))
    [∀ i, IsFiniteMeasure (measures i)] :
    (∫ samples, vecActOn (k := k)
        (scheduleProduct (fun i => placements i (samples i))) ∂Measure.pi measures) =
      scheduleProduct (fun i => ∫ U, vecActOn (k := k) (placements i U) ∂measures i) := by
  simp_rw [vecActOn_scheduleProduct]
  exact integral_scheduleProduct _
    (fun i => continuous_vecActOn.comp (hplacements i)) measures

end SchurWeyl.Circuits
