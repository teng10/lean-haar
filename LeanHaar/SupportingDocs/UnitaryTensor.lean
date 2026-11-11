/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix

/-!
# Tensor products of unitary gates in an ordered register decomposition

## Main definitions

* `SchurWeyl.tensorUnitary`: place two local unitaries in the register specified by `e`.
* `SchurWeyl.tensorCopiesEquiv` and `SchurWeyl.tensorEntriesEquiv`: supporting coordinate
  equivalences grouping copies and matrix entries by the two local factors.

## Main results

* `SchurWeyl.tensorUnitary_apply`: the placed gate's matrix entries.
* `SchurWeyl.tensorUnitary_star`: compatibility with inverse conjugation.
* `SchurWeyl.continuous_tensorUnitary`: continuity in the two local gates.
-/
noncomputable section
open scoped Matrix Kronecker
namespace SchurWeyl

/-- Tensor two unitaries, reading the full register through an ordered decomposition. -/
def tensorUnitary {D d₁ d₂ : ℕ} (e : Fin D ≃ Fin d₁ × Fin d₂)
    (U : Matrix.unitaryGroup (Fin d₁) ℂ) (V : Matrix.unitaryGroup (Fin d₂) ℂ) :
    Matrix.unitaryGroup (Fin D) ℂ :=
  ⟨(U.val ⊗ₖ V.val).submatrix e e, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv]
    change ((star (U.val ⊗ₖ V.val) * (U.val ⊗ₖ V.val)).submatrix e e) = 1
    rw [(Matrix.kronecker_mem_unitary U.property V.property).1,
      Matrix.submatrix_one_equiv]⟩

@[simp] theorem tensorUnitary_apply {D d₁ d₂ : ℕ} (e : Fin D ≃ Fin d₁ × Fin d₂)
    (U : Matrix.unitaryGroup (Fin d₁) ℂ) (V : Matrix.unitaryGroup (Fin d₂) ℂ)
    (i j : Fin D) : tensorUnitary e U V i j = U (e i).1 (e j).1 * V (e i).2 (e j).2 := rfl

@[simp] theorem tensorUnitary_star {D d₁ d₂ : ℕ} (e : Fin D ≃ Fin d₁ × Fin d₂)
    (U : Matrix.unitaryGroup (Fin d₁) ℂ) (V : Matrix.unitaryGroup (Fin d₂) ℂ) :
    tensorUnitary e (star U) (star V) = star (tensorUnitary e U V) := by
  apply Subtype.ext
  change (U.valᴴ ⊗ₖ V.valᴴ).submatrix e e = ((U.val ⊗ₖ V.val).submatrix e e)ᴴ
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

/-- The placed gate varies continuously with both local unitaries. -/
theorem continuous_tensorUnitary {D d₁ d₂ : ℕ} (e : Fin D ≃ Fin d₁ × Fin d₂) :
    Continuous (fun p : Matrix.unitaryGroup (Fin d₁) ℂ × Matrix.unitaryGroup (Fin d₂) ℂ =>
      tensorUnitary e p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun p : Matrix.unitaryGroup (Fin d₁) ℂ ×
      Matrix.unitaryGroup (Fin d₂) ℂ => p.1.val (e i).1 (e j).1 * p.2.val (e i).2 (e j).2)
  have h₁ : Continuous (fun p : Matrix.unitaryGroup (Fin d₁) ℂ ×
      Matrix.unitaryGroup (Fin d₂) ℂ => p.1.val) := continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous (fun p : Matrix.unitaryGroup (Fin d₁) ℂ ×
      Matrix.unitaryGroup (Fin d₂) ℂ => p.2.val) := continuous_subtype_val.comp continuous_snd
  exact (h₁.matrix_elem _ _).mul (h₂.matrix_elem _ _)

/-- Regroup `k` copies of a register as copies of each of its two factors. -/
def tensorCopiesEquiv {D d₁ d₂ : ℕ} (e : Fin D ≃ Fin d₁ × Fin d₂) (k : ℕ) :
    (Fin k → Fin D) ≃ (Fin k → Fin d₁) × (Fin k → Fin d₂) :=
  (Equiv.piCongrRight fun _ => e).trans (Equiv.arrowProdEquivProdArrow _ _ _)

@[simp] theorem tensorCopiesEquiv_apply {D d₁ d₂ k : ℕ}
    (e : Fin D ≃ Fin d₁ × Fin d₂) (I : Fin k → Fin D) :
    tensorCopiesEquiv e k I = (fun c => (e (I c)).1, fun c => (e (I c)).2) := rfl

/-- Group both matrix indices by the two factors of an ordered register decomposition. -/
def tensorEntriesEquiv {D d₁ d₂ : ℕ}
    (e : Fin D ≃ Fin d₁ × Fin d₂) (k : ℕ) :
    ((Fin k → Fin D) × (Fin k → Fin D)) ≃
      ((Fin k → Fin d₁) × (Fin k → Fin d₁)) ×
        ((Fin k → Fin d₂) × (Fin k → Fin d₂)) :=
  ((tensorCopiesEquiv e k).prodCongr (tensorCopiesEquiv e k)).trans
    (Equiv.prodProdProdComm _ _ _ _)

end SchurWeyl
