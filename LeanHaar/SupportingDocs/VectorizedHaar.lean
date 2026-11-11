/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.WeingartenInverse
import LeanHaar.SupportingDocs.EuclideanTensor
import LeanHaar.SupportingDocs.UnitaryTensor
import LeanHaar.SupportingDocs.HaarInvariance
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Vectorized unitary conjugation and its Haar average

`vecActOn` is the continuous linear map on matrix entries induced by the existing
conjugation `actOn`. Its Haar average agrees with the vectorization of `momentOp`.
`vecActOn_tensorUnitary` transports the action through an ordered register decomposition.

## Main definitions

* `SchurWeyl.vecActOn`: continuous linear conjugation on vectorized operators.
* `SchurWeyl.vecActOnHom`: the same action bundled with its composition and continuity laws.

## Main results

* `SchurWeyl.vecActOn_endVec`: agreement with the core tensor-power action.
* `SchurWeyl.integral_vecActOn_endVec`: agreement of the Haar average with `momentOp`.
* `SchurWeyl.vecActOn_tensorUnitary`: tensoring local gates tensors their actions.
* `SchurWeyl.integral_vecActOn_tensorUnitary`: independent tensor-gate Haar averages
  factor into local averages, for arbitrary local dimensions and copy number.

The matrix and continuity lemmas support these interfaces; the computed fourth-moment
formula is supplied by the application, not assumed in the factorization theorem.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Kronecker
open EuclideanSpace

namespace SchurWeyl

variable {d k : ℕ}

/-- Conjugation by `U^{⊗k}`, acting on vectorized operators. -/
def vecActOn (U : Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d)) →L[ℂ]
      EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d)) :=
  (Matrix.toEuclideanLin (fun p q =>
    (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.1 c) (q.1 c)) *
      star (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.2 c) (q.2 c)))).toContinuousLinearMap

/-- Matrix entries of vectorized conjugation. -/
theorem matrix_vecActOn (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.toEuclideanLin.symm (vecActOn (k := k) U).toLinearMap =
      fun p q => (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.1 c) (q.1 c)) *
        star (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.2 c) (q.2 c)) := by
  exact Matrix.toEuclideanLin.symm_apply_apply _

/-- The coordinate construction is exactly the existing tensor-power conjugation. -/
theorem vecActOn_endVec (U : Matrix.unitaryGroup (Fin d) ℂ)
    (X : Module.End ℂ (TensV d k)) :
    vecActOn U (endVec X) = endVec (actOn X U) := by
  let A : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
    fun I J => ∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (I c) (J c)
  have hU : toEndMatrix d k (diagAction d k (endOf (U : Matrix (Fin d) (Fin d) ℂ))) = A := by
    ext I J
    simp only [toEndMatrix_diagAction, endOf, LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin', A]
  have hstar : (toEndMatrix d k (diagAction d k
      (endOf (star (U : Matrix (Fin d) (Fin d) ℂ))))).transpose = A.map star := by
    ext I J
    simp only [Matrix.transpose_apply, toEndMatrix_diagAction, endOf,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.star_apply,
      Matrix.map_apply, A, star_prod]
  -- Mathlib vectorizes by (column, row), while endVec uses (row, column).
  apply (WithLp.equiv 2 _).injective
  change (A ⊗ₖ A.map star) *ᵥ (toEndMatrix d k X).transpose.vec =
    (toEndMatrix d k (actOn X U)).transpose.vec
  rw [Matrix.kronecker_mulVec_vec, actOn, toEndMatrix_comp, toEndMatrix_comp]
  simp only [Matrix.transpose_mul, hU, hstar, Matrix.mul_assoc]

/-- Multiplication of sampled gates becomes composition of their conjugation maps. -/
theorem vecActOn_mul (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    vecActOn (k := k) (U * V) = (vecActOn U).comp (vecActOn V) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨X, rfl⟩ := (endVecEquiv d k).surjective x
  change vecActOn (U * V) (endVec X) = vecActOn U (vecActOn V (endVec X))
  rw [vecActOn_endVec, vecActOn_endVec, vecActOn_endVec]
  exact congrArg endVec (conj_actOn X U V).symm

/-- The identity unitary acts as the identity superoperator. -/
@[simp] theorem vecActOn_one : vecActOn (d := d) (k := k) 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨X, rfl⟩ := (endVecEquiv d k).surjective x
  change vecActOn (d := d) (k := k) 1 (endVec X) = endVec X
  rw [vecActOn_endVec]
  have hid : diagAction d k LinearMap.id = LinearMap.id := map_one (diagAction d k)
  simp [actOn, endOf_one, hid]

/-- Adjoint conjugation is conjugation by the inverse unitary. -/
@[simp] theorem vecActOn_adjoint (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (vecActOn (k := k) U).adjoint = vecActOn (k := k) (star U) := by
  unfold vecActOn
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 2
  ext p q
  simp only [_root_.Unitary.coe_star, Matrix.star_apply, Matrix.conjTranspose_apply, star_mul, star_star, star_prod]
  ring

/-- Vectorized conjugation varies continuously with the sampled unitary. -/
theorem continuous_vecActOn : Continuous (vecActOn (d := d) (k := k)) := by
  let T := ((Matrix.toEuclideanLin (𝕜 := ℂ)
    (m := (Fin k → Fin d) × (Fin k → Fin d))
    (n := (Fin k → Fin d) × (Fin k → Fin d))).trans
      LinearMap.toContinuousLinearMap).toLinearMap
  change Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => T
    (fun p q => (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.1 c) (q.1 c)) *
      star (∏ c, (U : Matrix (Fin d) (Fin d) ℂ) (p.2 c) (q.2 c))))
  apply T.continuous_of_finiteDimensional.comp
  have hm : Continuous (fun U : Matrix (Fin d) (Fin d) ℂ =>
      fun p q : (Fin k → Fin d) × (Fin k → Fin d) =>
        (∏ c, U (p.1 c) (q.1 c)) * star (∏ c, U (p.2 c) (q.2 c))) :=
    continuous_pi fun _ => continuous_pi fun _ => by fun_prop
  exact hm.comp continuous_subtype_val

/-- Vectorized conjugation with its composition and continuity laws. -/
def vecActOnHom (d k : ℕ) : Matrix.unitaryGroup (Fin d) ℂ →ₜ*
    (EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d)) →L[ℂ]
      EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d))) where
  toFun := vecActOn
  map_one' := vecActOn_one
  map_mul' := vecActOn_mul
  continuous_toFun := continuous_vecActOn

/-- The adjoint of an averaged conjugation averages the inverse conjugations. -/
theorem adjoint_integral_vecActOn {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {L : α → Matrix.unitaryGroup (Fin d) ℂ}
    (hi : Integrable (fun a => vecActOn (k := k) (L a)) μ) :
    (∫ a, vecActOn (k := k) (L a) ∂μ).adjoint =
      ∫ a, vecActOn (k := k) (star (L a)) ∂μ := by
  let A := (ContinuousLinearMap.adjoint (𝕜 := ℂ)
    (E := EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d)))
    (F := EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d)))).toContinuousLinearEquiv
      |>.toContinuousLinearMap
  have h := ContinuousLinearMap.integral_comp_commSL (by simp) A hi
  change (∫ a, (vecActOn (k := k) (L a)).adjoint ∂μ) =
    (∫ a, vecActOn (k := k) (L a) ∂μ).adjoint at h
  rw [← h]
  simp_rw [vecActOn_adjoint]

/-- A continuous operator-valued function on the compact unitary group is integrable. -/
theorem integrable_vecActOn : Integrable (vecActOn (d := d) (k := k)) (haarProb d) :=
  continuous_vecActOn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Averaging vectorized conjugation computes the existing Haar moment operator. -/
theorem integral_vecActOn_endVec (X : Module.End ℂ (TensV d k)) :
    (∫ U, vecActOn U ∂haarProb d) (endVec X) = endVec (momentOp X) := by
  rw [ContinuousLinearMap.integral_apply integrable_vecActOn]
  simp_rw [vecActOn_endVec]
  ext p
  have hi : Integrable (fun U : Matrix.unitaryGroup (Fin d) ℂ => endVec (actOn X U))
      (haarProb d) := by
    simpa only [ContinuousLinearMap.apply_apply, vecActOn_endVec] using
      ((ContinuousLinearMap.apply ℂ _ (endVec X)).integrable_comp integrable_vecActOn)
  have h := (EuclideanSpace.proj p).integral_comp_comm hi
  change (∫ U, endVec (actOn X U) ∂haarProb d) p = _
  change (EuclideanSpace.proj p) (∫ U, endVec (actOn X U) ∂haarProb d) = _
  rw [← h]
  change (∫ U, toEndMatrix d k (actOn X U) p.1 p.2 ∂haarProb d) =
    toEndMatrix d k (momentOp X) p.1 p.2
  rw [toEndMatrix_momentOp]
  rfl

/-- Vectorized conjugation respects the ordered register decomposition. -/
theorem vecActOn_tensorUnitary {D d₁ d₂ k : ℕ}
    (e : Fin D ≃ Fin d₁ × Fin d₂)
    (U : Matrix.unitaryGroup (Fin d₁) ℂ) (V : Matrix.unitaryGroup (Fin d₂) ℂ) :
    vecActOn (k := k) (tensorUnitary e U V) =
      tensorMap (tensorEntriesEquiv e k) (vecActOn U) (vecActOn V) := by
  apply ContinuousLinearMap.coe_injective
  apply Matrix.toEuclideanLin.symm.injective
  rw [matrix_vecActOn, tensorMap_matrix, matrix_vecActOn, matrix_vecActOn]
  ext p q
  change (∏ c, U (e (p.1 c)).1 (e (q.1 c)).1 * V (e (p.1 c)).2 (e (q.1 c)).2) *
      star (∏ c, U (e (p.2 c)).1 (e (q.2 c)).1 * V (e (p.2 c)).2 (e (q.2 c)).2) =
    ((∏ c, U (e (p.1 c)).1 (e (q.1 c)).1) *
      star (∏ c, U (e (p.2 c)).1 (e (q.2 c)).1)) *
    ((∏ c, V (e (p.1 c)).2 (e (q.1 c)).2) *
      star (∏ c, V (e (p.2 c)).2 (e (q.2 c)).2))
  simp only [Finset.prod_mul_distrib, star_mul]
  ring

/-- Independent local Haar averages factor through the tensor operator map.
The left side uses Heisenberg conjugation; inversion invariance makes each local
average on the right a forward conjugation average. No stable-range bound is needed. -/
theorem integral_vecActOn_tensorUnitary {D d₁ d₂ k : ℕ} (e : Fin D ≃ Fin d₁ × Fin d₂) :
    (∫ p, vecActOn (k := k) (star (tensorUnitary e p.1 p.2))
      ∂((haarProb d₁).prod (haarProb d₂))) =
      tensorMap (tensorEntriesEquiv e k)
        (∫ U, vecActOn (k := k) U ∂haarProb d₁)
        (∫ V, vecActOn (k := k) V ∂haarProb d₂) := by
  have hi (d : ℕ) : Integrable
      (fun U : Matrix.unitaryGroup (Fin d) ℂ => vecActOn (k := k) (star U))
      (haarProb d) :=
    (continuous_vecActOn.comp continuous_star).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [← tensorUnitary_star, vecActOn_tensorUnitary]
  rw [integral_prod_bilin _ (hi d₁) (hi d₂)]
  simp only [_root_.Unitary.star_eq_inv, integral_inv_eq_self]

end SchurWeyl
