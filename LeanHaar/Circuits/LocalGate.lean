/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Circuits.Register
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Set
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Ordered local gates on a finite register

`Fin s ↪ Fin n` selects an ordered block of `s` distinct sites in an `n`-site register.
`placeUnitary q sites` embeds a gate on this block as a continuous monoid homomorphism.
It acts as the identity on all other sites. The public entry formula
`placeUnitary_apply` characterizes this action without exposing any enumeration of the
complement. In particular, gates may cross a periodic boundary: site order is explicit.

All dimensions are uniform but otherwise arbitrary. No restriction on the later moment
order, and no subtraction such as `n - s`, enters the placement interface.
-/

noncomputable section

open scoped Matrix Kronecker
open ContinuousMonoidHom

namespace SchurWeyl

/-! ### Tensor products in an ordered register -/

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

/-- Tensoring respects multiplication in both factors. -/
theorem tensorUnitary_mul {D d₁ d₂ : ℕ} (e : Fin D ≃ Fin d₁ × Fin d₂)
    (U U' : Matrix.unitaryGroup (Fin d₁) ℂ)
    (V V' : Matrix.unitaryGroup (Fin d₂) ℂ) :
    tensorUnitary e (U * U') (V * V') = tensorUnitary e U V * tensorUnitary e U' V' := by
  apply Subtype.ext
  change ((U.val * U'.val) ⊗ₖ (V.val * V'.val)).submatrix e e =
    (U.val ⊗ₖ V.val).submatrix e e * (U'.val ⊗ₖ V'.val).submatrix e e
  rw [Matrix.mul_kronecker_mul, Matrix.submatrix_mul_equiv]

@[simp] theorem tensorUnitary_one {D d₁ d₂ : ℕ} (e : Fin D ≃ Fin d₁ × Fin d₂) :
    tensorUnitary e 1 1 = 1 := by
  apply Subtype.ext
  change ((1 : Matrix (Fin d₁) (Fin d₁) ℂ) ⊗ₖ
    (1 : Matrix (Fin d₂) (Fin d₂) ℂ)).submatrix e e = 1
  rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/-! ### Placement on selected sites -/

namespace Circuits

/-- Sites outside an ordered local block. -/
private abbrev RemainingSites {s n : ℕ} (sites : Fin s ↪ Fin n) :=
  {i : Fin n // i ∉ Set.range sites}

/-- Read the chosen sites in their specified order. -/
def localRead {s n : ℕ} (q : ℕ) (sites : Fin s ↪ Fin n) (x : Fin (q ^ n)) :
    Fin (q ^ s) :=
  finFunctionFinEquiv (fun a => registerEquiv q n x (sites a))

/-- The two-site local index reads the first input before the second input. -/
@[simp] theorem localRead_embFinTwo {n : ℕ} (q : ℕ) (i j : Fin n) (h : i ≠ j)
    (x : Fin (q ^ n)) :
    localRead q (Function.Embedding.embFinTwo h) x =
      finFunctionFinEquiv ![registerEquiv q n x i, registerEquiv q n x j] := by
  congr 1

/-- Split site configurations into an ordered local block and its complement. -/
private def splitRegister {s n : ℕ} (q : ℕ) (sites : Fin s ↪ Fin n) :
    (Fin n → Fin q) ≃ (Fin s → Fin q) × (RemainingSites sites → Fin q) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (· ∈ Set.range sites) (fun _ : Fin n => Fin q)).trans
    ((Equiv.arrowCongr (Equiv.ofInjective sites sites.injective).symm
      (Equiv.refl (Fin q))).prodCongr (Equiv.refl _))

/-- Dimension of the untouched register. Its enumeration is internal to placement. -/
private def remainingDimension {s n : ℕ} (q : ℕ) (sites : Fin s ↪ Fin n) : ℕ := by
  classical
  exact Fintype.card (RemainingSites sites → Fin q)

/-- The ordered tensor decomposition used by local gate placement. -/
private def blockIndexEquiv {s n : ℕ} (q : ℕ) (sites : Fin s ↪ Fin n) :
    Fin (q ^ n) ≃ Fin (q ^ s) × Fin (remainingDimension q sites) := by
  classical
  exact (registerEquiv q n).trans ((splitRegister q sites).trans
    (finFunctionFinEquiv.prodCongr (Fintype.equivFin (RemainingSites sites → Fin q))))

@[simp] private theorem blockIndexEquiv_fst {s n : ℕ} (q : ℕ) (sites : Fin s ↪ Fin n)
    (x : Fin (q ^ n)) :
    (blockIndexEquiv q sites x).1 = localRead q sites x := rfl

/-- Embed an ordered local gate, acting identically on all remaining sites. -/
def placeUnitary {s n : ℕ} (q : ℕ) (sites : Fin s ↪ Fin n) :
    Matrix.unitaryGroup (Fin (q ^ s)) ℂ →ₜ* Matrix.unitaryGroup (Fin (q ^ n)) ℂ where
  toFun U := tensorUnitary (blockIndexEquiv q sites) U 1
  map_one' := tensorUnitary_one _
  map_mul' U V := by simpa using tensorUnitary_mul (blockIndexEquiv q sites) U V 1 1
  continuous_toFun := (continuous_tensorUnitary (blockIndexEquiv q sites)).comp
    (continuous_id.prodMk continuous_const)

/-- The placed matrix acts on the local coordinates and preserves all other site values. -/
theorem placeUnitary_apply {s n : ℕ} (q : ℕ) (sites : Fin s ↪ Fin n)
    (U : Matrix.unitaryGroup (Fin (q ^ s)) ℂ) (x y : Fin (q ^ n)) :
    placeUnitary q sites U x y =
      U (localRead q sites x) (localRead q sites y) *
        if (∀ i, i ∉ Set.range sites → registerEquiv q n x i = registerEquiv q n y i)
        then 1 else 0 := by
  classical
  change U (blockIndexEquiv q sites x).1 (blockIndexEquiv q sites y).1 *
    (1 : Matrix (Fin (remainingDimension q sites)) (Fin (remainingDimension q sites)) ℂ)
      (blockIndexEquiv q sites x).2 (blockIndexEquiv q sites y).2 = _
  rw [Matrix.one_apply, blockIndexEquiv_fst, blockIndexEquiv_fst]
  congr 1
  apply if_congr
  · change Fintype.equivFin (RemainingSites sites → Fin q)
        (fun i => registerEquiv q n x i) =
      Fintype.equivFin (RemainingSites sites → Fin q) (fun i => registerEquiv q n y i) ↔ _
    exact ((Fintype.equivFin (RemainingSites sites → Fin q)).injective.eq_iff.trans
      funext_iff).trans (by simp only [Subtype.forall])
  · rfl
  · rfl

/-- Outside the selected support, a changed site forces a zero matrix entry. -/
theorem placeUnitary_apply_eq_zero {s n : ℕ} (q : ℕ) (sites : Fin s ↪ Fin n)
    (U : Matrix.unitaryGroup (Fin (q ^ s)) ℂ) (x y : Fin (q ^ n))
    (i : Fin n) (hi : i ∉ Set.range sites) (h : registerEquiv q n x i ≠ registerEquiv q n y i) :
    placeUnitary q sites U x y = 0 := by
  rw [placeUnitary_apply, if_neg (fun hxy => h (hxy i hi)), mul_zero]

/-- Placement preserves the unitary adjoint. -/
@[simp] theorem placeUnitary_star {s n : ℕ} (q : ℕ) (sites : Fin s ↪ Fin n)
    (U : Matrix.unitaryGroup (Fin (q ^ s)) ℂ) :
    placeUnitary q sites (star U) = star (placeUnitary q sites U) := by
  change tensorUnitary (blockIndexEquiv q sites) (star U) 1 =
    star (tensorUnitary (blockIndexEquiv q sites) U 1)
  simpa using tensorUnitary_star (blockIndexEquiv q sites) U 1

end Circuits
end SchurWeyl
