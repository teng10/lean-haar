/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Circuits.LocalGate
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# Periodic brickwork geometry

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

end SchurWeyl.Circuits
