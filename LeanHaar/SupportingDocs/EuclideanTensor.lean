/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Tensoring finite-coordinate operators

An ordered coordinate equivalence identifies a finite register with two factors. The
bilinear operator map transports their Kronecker product through that equivalence.

## Main definitions

* `EuclideanSpace.tensorVec`: a product vector in the selected coordinates.
* `EuclideanSpace.tensorMap`: the continuous bilinear map tensoring two operators.

## Main results

* `EuclideanSpace.tensorMap_matrix`: the transported Kronecker-product matrix.
* `EuclideanSpace.tensorMap_rankOne`: tensoring rank-one maps tensors their ket and bra.
-/

noncomputable section

open scoped Matrix Kronecker

namespace EuclideanSpace

variable {α β γ : Type*}

/-- The product vector, placed in the coordinates specified by `e`. -/
def tensorVec (e : γ ≃ α × β) (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) :
    EuclideanSpace ℂ γ := WithLp.toLp 2 fun i => x (e i).1 * y (e i).2

@[simp] theorem tensorVec_apply (e : γ ≃ α × β) (x : EuclideanSpace ℂ α)
    (y : EuclideanSpace ℂ β) (i : γ) : tensorVec e x y i = x (e i).1 * y (e i).2 := rfl

variable [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]

private def tensorMapRaw (e : γ ≃ α × β)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (B : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β) :
    EuclideanSpace ℂ γ →L[ℂ] EuclideanSpace ℂ γ :=
  (Matrix.toEuclideanLin
    ((Matrix.toEuclideanLin.symm A.toLinearMap ⊗ₖ
      Matrix.toEuclideanLin.symm B.toLinearMap).submatrix e e)).toContinuousLinearMap

private theorem tensorMapRaw_apply (e : γ ≃ α × β)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (B : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β)
    (x : EuclideanSpace ℂ γ) (i : γ) :
    tensorMapRaw e A B x i = ∑ j,
      Matrix.toEuclideanLin.symm A.toLinearMap (e i).1 (e j).1 *
      Matrix.toEuclideanLin.symm B.toLinearMap (e i).2 (e j).2 * x j := rfl

/-- Tensor two continuous linear operators using the ordered register decomposition `e`.
Bundled bilinearity makes finite sums and independent integrals commute with this map. -/
def tensorMap (e : γ ≃ α × β) :
    (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) →L[ℂ]
      (EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β) →L[ℂ]
        EuclideanSpace ℂ γ →L[ℂ] EuclideanSpace ℂ γ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => LinearMap.toContinuousLinearMap {
      toFun := tensorMapRaw e A
      map_add' := by
        intro B C
        ext x i
        simp [tensorMapRaw_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c B
        ext x i
        simp [tensorMapRaw_apply, map_smul, Finset.mul_sum, mul_assoc, mul_left_comm] }
    map_add' := by
      intro A C
      ext B x i
      simp [tensorMapRaw_apply, map_add, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c A
      ext B x i
      simp [tensorMapRaw_apply, map_smul, Finset.mul_sum, mul_assoc] }

/-- Matrix of the tensor operator in the selected coordinates. -/
theorem tensorMap_matrix (e : γ ≃ α × β)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (B : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β) :
    Matrix.toEuclideanLin.symm (tensorMap e A B).toLinearMap =
      (Matrix.toEuclideanLin.symm A.toLinearMap ⊗ₖ
        Matrix.toEuclideanLin.symm B.toLinearMap).submatrix e e :=
  Matrix.toEuclideanLin.symm_apply_apply _

/-- Tensoring rank-one operators tensors their ket and bra vectors. -/
theorem tensorMap_rankOne (e : γ ≃ α × β)
    (x x' : EuclideanSpace ℂ α) (y y' : EuclideanSpace ℂ β) :
    tensorMap e (InnerProductSpace.rankOne ℂ x x') (InnerProductSpace.rankOne ℂ y y') =
      InnerProductSpace.rankOne ℂ (tensorVec e x y) (tensorVec e x' y') := by
  apply ContinuousLinearMap.coe_injective
  apply Matrix.toEuclideanLin.symm.injective
  rw [tensorMap_matrix]
  simp only [InnerProductSpace.symm_toEuclideanLin_rankOne]
  ext i j
  simp [Matrix.vecMulVec_apply, tensorVec_apply, mul_comm,
    mul_left_comm, mul_assoc]

end EuclideanSpace
