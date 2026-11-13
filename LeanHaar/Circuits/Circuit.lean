/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Circuits.Schedule
import LeanHaar.Circuits.HaarMoment
import LeanHaar.Circuits.LocalGate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Physical circuits and their moments

The public interface takes a `Fin length`-indexed sequence of gate occurrences. Each occurrence
gets a fresh independent sample, even when its support repeats. The first gate
acts first: a two-gate circuit has unitary `U₁ * U₀` and moment `M₁ * M₀`.

`circuitMoment` works on vectorized operators; `operatorMap` expresses any such moment
on ordinary endomorphisms. The ensemble identities quantify over arbitrary
input operators. Neither copy number nor register size is restricted.
-/

noncomputable section

open MeasureTheory

namespace SchurWeyl.Circuits

/-! ### Independent averages

The chronological factorization holds for arbitrary finite measures on a compact sample
space. Haar-distributed circuit gates are a specialization. -/

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

/-! ### Physical circuits -/

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

/-- Multiply physically placed gates in chronological order. -/
def circuitUnitary {s n length : ℕ} (q : ℕ)
    (sites : Fin length → (Fin s ↪ Fin n)) (samples : Fin length → Matrix.unitaryGroup (Fin (q ^ s)) ℂ) :
    Matrix.unitaryGroup (Fin (q ^ n)) ℂ :=
  scheduleProduct (fun i => placeUnitary q (sites i) (samples i))

/-- The moment of independent Haar gates at the specified occurrences. -/
def circuitMoment {s n length : ℕ} (q k : ℕ)
    (sites : Fin length → (Fin s ↪ Fin n)) : MomentOperator (q ^ n) k :=
  scheduleProduct (fun i => gateMoment (placeUnitary q (sites i)) k)

theorem continuous_circuitUnitary {s n length : ℕ} (q : ℕ)
    (sites : Fin length → (Fin s ↪ Fin n)) : Continuous (circuitUnitary q sites) :=
  continuous_scheduleProduct _ (fun i => (placeUnitary q (sites i)).continuous)

/-- Vectorized circuit actions are integrable over their independent Haar samples. -/
theorem integrable_circuitAction {s n length : ℕ} (q k : ℕ)
    (sites : Fin length → (Fin s ↪ Fin n)) :
    Integrable (fun samples => vecActOn (k := k) (circuitUnitary q sites samples))
      (Measure.pi (fun _ : Fin length => haarProb (q ^ s))) :=
  (continuous_vecActOn.comp (continuous_circuitUnitary q sites)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Concatenation executes the first circuit and then the second. -/
theorem circuitUnitary_append {s n l₁ l₂ : ℕ} (q : ℕ)
    (first : Fin l₁ → (Fin s ↪ Fin n)) (second : Fin l₂ → (Fin s ↪ Fin n))
    (x : Fin l₁ → Matrix.unitaryGroup (Fin (q ^ s)) ℂ)
    (y : Fin l₂ → Matrix.unitaryGroup (Fin (q ^ s)) ℂ) :
    circuitUnitary q (Fin.append first second) (Fin.append x y) =
      circuitUnitary q second y * circuitUnitary q first x := by
  unfold circuitUnitary
  rw [← scheduleProduct_append]
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp

/-- Independent circuit moments compose in the same chronological order. -/
theorem circuitMoment_append {s n l₁ l₂ : ℕ} (q k : ℕ)
    (first : Fin l₁ → (Fin s ↪ Fin n)) (second : Fin l₂ → (Fin s ↪ Fin n)) :
    circuitMoment q k (Fin.append first second) =
      circuitMoment q k second * circuitMoment q k first := by
  unfold circuitMoment
  rw [← scheduleProduct_append]
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp

private theorem adjoint_scheduleProduct {d k length : ℕ}
    (gates : Fin length → MomentOperator d k) :
    (scheduleProduct gates).adjoint = scheduleProduct (fun i => (gates i.rev).adjoint) := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [scheduleProduct_succ]
    change ((scheduleProduct fun i => gates i.succ).comp (gates 0)).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, scheduleProduct_succ']
    simp only [Fin.rev_last, Fin.rev_castSucc]
    rw [ih]
    rfl

/-- Haar gate moments are self-adjoint, so reversing the schedule gives the adjoint circuit. -/
theorem circuitMoment_adjoint {s n length : ℕ} (q k : ℕ)
    (sites : Fin length → (Fin s ↪ Fin n)) :
    (circuitMoment q k sites).adjoint = circuitMoment q k (fun i => sites i.rev) := by
  unfold circuitMoment
  rw [adjoint_scheduleProduct]
  simp only [gateMoment_adjoint]

/-- The physical product-Haar ensemble has exactly the compositional moment. -/
theorem integral_circuitUnitary {s n length : ℕ} (q k : ℕ)
    (sites : Fin length → (Fin s ↪ Fin n)) :
    (∫ samples, vecActOn (k := k) (circuitUnitary q sites samples)
      ∂Measure.pi (fun _ : Fin length => haarProb (q ^ s))) = circuitMoment q k sites :=
  integral_vecActOn_placed_schedule _
    (fun i => (placeUnitary q (sites i)).continuous) _

/-- Circuit averaging is valid on any input operator, including entangled inputs. -/
theorem circuitMoment_endVec {s n length : ℕ} (q k : ℕ)
    (sites : Fin length → (Fin s ↪ Fin n)) (X : Module.End ℂ (TensV (q ^ n) k)) :
    circuitMoment q k sites (endVec X) =
      ∫ samples, endVec (actOn X (circuitUnitary q sites samples))
        ∂Measure.pi (fun _ : Fin length => haarProb (q ^ s)) := by
  rw [← integral_circuitUnitary,
    ContinuousLinearMap.integral_apply (integrable_circuitAction q k sites)]
  simp only [vecActOn_endVec]

/-- Entrywise ensemble formula for the ordinary-operator circuit interface. -/
theorem circuitChannel_entry {s n length : ℕ} (q k : ℕ)
    (sites : Fin length → (Fin s ↪ Fin n)) (X : Module.End ℂ (TensV (q ^ n) k))
    (i j : Fin k → Fin (q ^ n)) :
    toEndMatrix (q ^ n) k (operatorMap (circuitMoment q k sites) X) i j =
      ∫ samples, toEndMatrix (q ^ n) k (actOn X (circuitUnitary q sites samples)) i j
        ∂Measure.pi (fun _ : Fin length => haarProb (q ^ s)) := by
  have hi := integrable_circuitAction q k sites
  have hx : Integrable (fun samples => endVec (actOn X (circuitUnitary q sites samples)))
      (Measure.pi (fun _ : Fin length => haarProb (q ^ s))) := by
    simpa only [ContinuousLinearMap.apply_apply, vecActOn_endVec] using
      ((ContinuousLinearMap.apply ℂ _ (endVec X)).integrable_comp hi)
  rw [toEndMatrix_operatorMap, circuitMoment_endVec]
  exact ((EuclideanSpace.proj (i, j)).integral_comp_comm hx).symm

/-- Averaging the inverse conjugations of a Haar circuit gives the adjoint moment. -/
theorem integral_star_circuitUnitary {s n length : ℕ} (q k : ℕ)
    (sites : Fin length → (Fin s ↪ Fin n)) :
    (∫ samples, vecActOn (k := k) (star (circuitUnitary q sites samples))
      ∂Measure.pi (fun _ : Fin length => haarProb (q ^ s))) =
      (circuitMoment q k sites).adjoint := by
  rw [← integral_circuitUnitary, adjoint_integral_vecActOn (integrable_circuitAction q k sites)]


end SchurWeyl.Circuits
