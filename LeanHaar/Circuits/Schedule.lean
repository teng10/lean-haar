/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Chronological products

Schedules are written in execution order. Thus `[A, B]` acts as `B * A`, and
appending a later schedule multiplies its operator on the left. These definitions
work for arbitrary monoids, including unitaries and continuous linear operators.
-/

namespace SchurWeyl.Circuits

variable {M : Type*} [Monoid M]

/-- A schedule indexed by its number of gate occurrences, in chronological order. -/
def scheduleProduct {length : ℕ} (gates : Fin length → M) : M :=
  (List.ofFn gates).reverse.prod

@[simp] theorem scheduleProduct_zero (gates : Fin 0 → M) :
    scheduleProduct gates = 1 := by simp [scheduleProduct]

/-- Peel off the first occurrence. The tail acts after the first gate. -/
theorem scheduleProduct_succ {length : ℕ} (gates : Fin (length + 1) → M) :
    scheduleProduct gates = scheduleProduct (fun i => gates i.succ) * gates 0 := by
  simp [scheduleProduct, List.ofFn_succ]

/-- Peel off the last occurrence, which acts after the preceding schedule. -/
theorem scheduleProduct_succ' {length : ℕ} (gates : Fin (length + 1) → M) :
    scheduleProduct gates = gates (Fin.last length) *
      scheduleProduct (fun i => gates i.castSucc) := by
  unfold scheduleProduct
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append, List.reverse_append, List.reverse_singleton,
    List.prod_append, List.prod_singleton]

@[simp] theorem scheduleProduct_one (gates : Fin 1 → M) :
    scheduleProduct gates = gates 0 := by rw [scheduleProduct_succ]; simp

@[simp] theorem scheduleProduct_two (gates : Fin 2 → M) :
    scheduleProduct gates = gates 1 * gates 0 := by rw [scheduleProduct_succ]; simp

/-- Appending a later schedule multiplies its product on the left. -/
theorem scheduleProduct_append {m n : ℕ} (first : Fin m → M) (second : Fin n → M) :
    scheduleProduct (Fin.append first second) = scheduleProduct second * scheduleProduct first := by
  simp [scheduleProduct, List.ofFn_fin_append]

/-- Evaluate a schedule layer by layer, retaining the order within each layer. -/
theorem scheduleProduct_mul {m n : ℕ} (gates : Fin (m * n) → M) :
    scheduleProduct gates = scheduleProduct (fun i : Fin m =>
      scheduleProduct (fun j : Fin n => gates (finProdFinEquiv (i, j)))) := by
  unfold scheduleProduct
  rw [List.ofFn_mul]
  simp only [List.reverse_flatten, List.prod_flatten, List.map_reverse,
    List.map_ofFn]
  congr 3
  funext i
  dsimp only [Function.comp_apply]
  congr 3
  funext j
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

/-- Applying a monoid homomorphism commutes with chronological evaluation. -/
theorem map_scheduleProduct {N : Type*} [Monoid N] (f : M →* N)
    {length : ℕ} (gates : Fin length → M) :
    f (scheduleProduct gates) = scheduleProduct (fun i => f (gates i)) := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [scheduleProduct_succ, map_mul, scheduleProduct_succ, ih]

/-- A finite chronological product depends continuously on its samples. -/
theorem continuous_scheduleProduct {α : Type*} [TopologicalSpace α]
    [TopologicalSpace M] [ContinuousMul M] {length : ℕ}
    (gates : Fin length → α → M) (hgates : ∀ i, Continuous (gates i)) :
    Continuous (fun samples : Fin length → α =>
      scheduleProduct (fun i => gates i (samples i))) := by
  induction length with
  | zero => simpa using (continuous_const : Continuous (fun _ : Fin 0 → α => (1 : M)))
  | succ length ih =>
    simp_rw [scheduleProduct_succ]
    exact ((ih (fun i => gates i.succ) (fun i => hgates i.succ)).comp
      (continuous_pi fun i => continuous_apply i.succ)).mul
      ((hgates 0).comp (continuous_apply 0))

end SchurWeyl.Circuits
