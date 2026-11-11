/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Circuits.IndependentMoments
import LeanHaar.Circuits.Brickwork

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

/-- Express a vectorized superoperator as a linear map on ordinary operators. -/
def operatorMap {d k : ℕ} (T : MomentOperator d k) :
    Module.End ℂ (TensV d k) →ₗ[ℂ] Module.End ℂ (TensV d k) :=
  (endVecEquiv d k).symm.toLinearMap.comp
    (T.toLinearMap.comp (endVecEquiv d k).toLinearMap)

@[simp] theorem endVec_operatorMap {d k : ℕ} (T : MomentOperator d k)
    (X : Module.End ℂ (TensV d k)) :
    endVec (operatorMap T X) = T (endVec X) :=
  (endVecEquiv d k).apply_symm_apply _

set_option maxRecDepth 1024 in
/-- Matrix entries can be read directly from the vectorized result. -/
theorem toEndMatrix_operatorMap {d k : ℕ} (T : MomentOperator d k)
    (X : Module.End ℂ (TensV d k)) (i j : Fin k → Fin d) :
    toEndMatrix d k (operatorMap T X) i j = T (endVec X) (i, j) :=
  congrArg (fun v : MomentSpace d k => v (i, j)) (endVec_operatorMap T X)

@[simp] theorem operatorMap_haarMoment {d k : ℕ} (X : Module.End ℂ (TensV d k)) :
    operatorMap (haarMoment d k) X = momentOp X := by
  apply (endVecEquiv d k).injective
  exact (endVec_operatorMap _ _).trans (haarMoment_endVec X)

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

/-- A periodic brickwork circuit with exactly `depth` matching layers.
Its independent random variables are indexed by gate occurrence, of count `depth * m`. -/
def brickworkSchedule (m depth : ℕ) : Fin (depth * m) → (Fin 2 ↪ Fin (2 * m)) :=
  fun i => brickworkLayer m (finProdFinEquiv.symm i).1.val (finProdFinEquiv.symm i).2

/-- Sampled periodic circuit, with one independent variable per gate occurrence. -/
def brickworkUnitary (q m depth : ℕ)
    (samples : Fin (depth * m) → Matrix.unitaryGroup (Fin (q ^ 2)) ℂ) :
    Matrix.unitaryGroup (Fin (q ^ (2 * m))) ℂ :=
  circuitUnitary q (brickworkSchedule m depth) samples

/-- The full `k`-copy moment of a periodic brickwork circuit at literal layer depth. -/
def brickworkMoment (q k m depth : ℕ) : MomentOperator (q ^ (2 * m)) k :=
  circuitMoment q k (brickworkSchedule m depth)

/-- Entrywise physical ensemble formula for the periodic brickwork channel. -/
theorem brickworkChannel_entry (q k m depth : ℕ)
    (X : Module.End ℂ (TensV (q ^ (2 * m)) k)) (i j : Fin k → Fin (q ^ (2 * m))) :
    toEndMatrix (q ^ (2 * m)) k (operatorMap (brickworkMoment q k m depth) X) i j =
      ∫ samples, toEndMatrix (q ^ (2 * m)) k (actOn X (brickworkUnitary q m depth samples)) i j
        ∂Measure.pi (fun _ : Fin (depth * m) => haarProb (q ^ 2)) :=
  circuitChannel_entry q k _ X i j

/-- Product-Haar semantics of the periodic brickwork moment. -/
theorem integral_brickworkUnitary (q k m depth : ℕ) :
    (∫ samples, vecActOn (k := k) (brickworkUnitary q m depth samples)
      ∂Measure.pi (fun _ : Fin (depth * m) => haarProb (q ^ 2))) =
      brickworkMoment q k m depth :=
  integral_circuitUnitary q k _

/-- Zero matching layers act as the identity superoperator. -/
@[simp] theorem brickworkMoment_zero (q k m : ℕ) : brickworkMoment q k m 0 = 1 := by
  unfold brickworkMoment circuitMoment scheduleProduct
  have h : List.ofFn (fun i => gateMoment (placeUnitary q (brickworkSchedule m 0 i)) k) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp
  rw [h]
  rfl

/-- Evaluate a brickwork circuit by composing its successive matching-layer moments. -/
theorem brickworkMoment_layers (q k m depth : ℕ) :
    brickworkMoment q k m depth = scheduleProduct (fun t : Fin depth =>
      circuitMoment q k (brickworkLayer m t.val)) := by
  unfold brickworkMoment circuitMoment
  rw [scheduleProduct_mul]
  simp only [brickworkSchedule, Equiv.symm_apply_apply]

end SchurWeyl.Circuits
