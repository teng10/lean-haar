/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Circuits.Layer
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# Periodic brickwork geometry and moments

A register has `2 * m` sites. The odd matching contains the ordered pairs
`(0, 1), (2, 3), ...`; the even matching shifts these pairs by one site, so its
last pair crosses the periodic boundary in the order `(2 * m - 1, 0)`.
The order of each pair is part of the local-gate interface.

`brickworkLayer m t` indexes the gates of matching layer `t`, starting with
an odd layer. Circuit schedules retain every occurrence, including repeated supports. In particular, the two-site ring
has the ordered pair `(0, 1)` in an odd layer and `(1, 0)` in an even layer.

Geometry is independent of local Hilbert-space dimension and moment order.
The empty register `m = 0` is allowed and has empty matching layers; a physical
nonempty ring is obtained by taking positive `m`.
-/

namespace SchurWeyl.Circuits

/-- The ordered pair `(2j, 2j+1)` in a register of `2m` sites. -/
def oddEdge (m : ℕ) (j : Fin m) : (Fin 2 ↪ Fin (2 * m)) where
  toFun a := ⟨2 * j.val + a.val, by have := j.isLt; have := a.isLt; omega⟩
  inj' a b h := by
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

@[simp] theorem oddEdge_val (m : ℕ) (j : Fin m) (a : Fin 2) :
    (oddEdge m j a).val = 2 * j.val + a.val := rfl

/-- Shift an odd pair by one site, including the periodic wraparound. -/
def evenEdge (m : ℕ) (j : Fin m) : (Fin 2 ↪ Fin (2 * m)) :=
  (oddEdge m j).trans (finRotate (2 * m)).toEmbedding

@[simp] theorem evenEdge_apply (m : ℕ) (j : Fin m) (a : Fin 2) :
    evenEdge m j a = finRotate (2 * m) (oddEdge m j a) := rfl

/-- Distinct odd pairs have disjoint supports. -/
theorem oddEdge_disjoint {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    Disjoint (Set.range (oddEdge m i)) (Set.range (oddEdge m j)) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨b, h⟩
  have he := congrArg Fin.val h
  simp only [oddEdge_val] at he
  have ha := a.isLt
  have hb := b.isLt
  apply hij
  apply Fin.ext
  omega

/-- Every site lies in one of the odd pairs. -/
theorem oddEdge_covers {m : ℕ} (x : Fin (2 * m)) :
    ∃ j : Fin m, x ∈ Set.range (oddEdge m j) := by
  refine ⟨⟨x.val / 2, by have := x.isLt; omega⟩, ⟨⟨x.val % 2, by omega⟩, ?_⟩⟩
  apply Fin.ext
  simp only [oddEdge_val]
  omega

/-- Distinct even pairs have disjoint supports. -/
theorem evenEdge_disjoint {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    Disjoint (Set.range (evenEdge m i)) (Set.range (evenEdge m j)) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨b, h⟩
  have he : oddEdge m j b = oddEdge m i a := (finRotate (2 * m)).injective h
  exact Set.disjoint_left.mp (oddEdge_disjoint hij) ⟨a, rfl⟩ ⟨b, he⟩

/-- Every site lies in one of the even pairs. -/
theorem evenEdge_covers {m : ℕ} (x : Fin (2 * m)) :
    ∃ j : Fin m, x ∈ Set.range (evenEdge m j) := by
  obtain ⟨j, a, ha⟩ := oddEdge_covers ((finRotate (2 * m)).symm x)
  refine ⟨j, a, ?_⟩
  change finRotate (2 * m) (oddEdge m j a) = x
  rw [ha, Equiv.apply_symm_apply]

/-- Matching number `t`, indexed by its gate occurrences, starting with the odd matching. -/
def brickworkLayer (m t : ℕ) : Fin m → (Fin 2 ↪ Fin (2 * m)) :=
  if t % 2 = 0 then oddEdge m else evenEdge m

@[simp] theorem brickworkLayer_two_mul (m t : ℕ) :
    brickworkLayer m (2 * t) = oddEdge m := by simp [brickworkLayer]

@[simp] theorem brickworkLayer_two_mul_add_one (m t : ℕ) :
    brickworkLayer m (2 * t + 1) = evenEdge m := by simp [brickworkLayer]

/-- Distinct occurrences within a matching have disjoint supports. -/
theorem brickworkLayer_pairwise_disjoint (m t : ℕ) {i j : Fin m} (hij : i ≠ j) :
    Disjoint (Set.range (brickworkLayer m t i)) (Set.range (brickworkLayer m t j)) := by
  unfold brickworkLayer
  split <;> first | exact oddEdge_disjoint hij | exact evenEdge_disjoint hij

/-- Every site lies in a gate of each matching. -/
theorem brickworkLayer_covers {m : ℕ} (t : ℕ) (x : Fin (2 * m)) :
    ∃ j, x ∈ Set.range (brickworkLayer m t j) := by
  unfold brickworkLayer
  split <;> first | exact oddEdge_covers x | exact evenEdge_covers x

noncomputable section

open MeasureTheory

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

end

/-- The gate of the odd matching that contains a site. -/
def oddGate (m : ℕ) (i : Fin (2 * m)) : Fin m := ⟨i.val / 2, by have := i.isLt; omega⟩

theorem oddGate_oddEdge (m : ℕ) (j : Fin m) (a : Fin 2) : oddGate m (oddEdge m j a) = j := by
  apply Fin.ext
  have := a.isLt
  simp only [oddGate, oddEdge_val]
  omega

theorem mem_range_oddEdge_oddGate (m : ℕ) (i : Fin (2 * m)) :
    i ∈ Set.range (oddEdge m (oddGate m i)) := by
  refine ⟨⟨i.val % 2, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [oddGate, oddEdge_val]
  omega

/-- The gate of the even matching that contains a site. -/
def evenGate (m : ℕ) (i : Fin (2 * m)) : Fin m := oddGate m ((finRotate (2 * m)).symm i)

theorem evenGate_evenEdge (m : ℕ) (j : Fin m) (a : Fin 2) :
    evenGate m (evenEdge m j a) = j := by
  rw [evenGate, evenEdge_apply, Equiv.symm_apply_apply, oddGate_oddEdge]

theorem mem_range_evenEdge_evenGate (m : ℕ) (i : Fin (2 * m)) :
    i ∈ Set.range (evenEdge m (evenGate m i)) := by
  obtain ⟨a, ha⟩ := mem_range_oddEdge_oddGate m ((finRotate (2 * m)).symm i)
  exact ⟨a, by rw [evenEdge_apply, evenGate, ha, Equiv.apply_symm_apply]⟩

/-! ### Evaluated matching moments -/

open InnerProductSpace

/-- The odd matching moment, with one copy permutation and inverse-Gram factor per gate. -/
theorem circuitMoment_oddEdge {k : ℕ} (q m : ℕ) (hk : k ≤ q ^ 2) :
    circuitMoment q k (oddEdge m) =
      ∑ σ : Fin m → Equiv.Perm (Fin k), ∑ π : Fin m → Equiv.Perm (Fin k),
        (∏ g, (weingartenGram (q ^ 2) k)⁻¹ (σ g) (π g)) •
          rankOne ℂ (endVec (sitePerm q (fun i => σ (oddGate m i))))
            (endVec (sitePerm q (fun i => π (oddGate m i)))) :=
  circuitMoment_eq_weingarten_sum q hk (oddEdge m) (oddGate m) (oddGate_oddEdge m)
    (mem_range_oddEdge_oddGate m)

/-- The even matching moment includes the ordered gate across the periodic boundary. -/
theorem circuitMoment_evenEdge {k : ℕ} (q m : ℕ) (hk : k ≤ q ^ 2) :
    circuitMoment q k (evenEdge m) =
      ∑ σ : Fin m → Equiv.Perm (Fin k), ∑ π : Fin m → Equiv.Perm (Fin k),
        (∏ g, (weingartenGram (q ^ 2) k)⁻¹ (σ g) (π g)) •
          rankOne ℂ (endVec (sitePerm q (fun i => σ (evenGate m i))))
            (endVec (sitePerm q (fun i => π (evenGate m i)))) :=
  circuitMoment_eq_weingarten_sum q hk (evenEdge m) (evenGate m) (evenGate_evenEdge m)
    (mem_range_evenEdge_evenGate m)

/-- A depth-two brickwork moment is the even matching after the odd matching. -/
theorem brickworkMoment_two (q k m : ℕ) :
    brickworkMoment q k m 2 = circuitMoment q k (evenEdge m) * circuitMoment q k (oddEdge m) := by
  rw [brickworkMoment_layers, scheduleProduct_two]
  simp [brickworkLayer]

end SchurWeyl.Circuits
