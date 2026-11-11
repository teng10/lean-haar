/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.SupportingDocs.EuclideanTensor
import LeanHaar.SupportingDocs.VectorizedHaar
import LeanHaar.SupportingDocs.UnitaryTensor
import LeanHaar.Applications.MagicMonotone.SingleGateMoment
import LeanHaar.Applications.MagicMonotone.LayerGates
import LeanHaar.Applications.MagicMonotone.Equation24
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independent Haar gates on the four-qubit register

The ordered layer gates are sampled independently from `haarProb 4`. Their fourth
Heisenberg moments are the existing algebraic layer sums, and physical execution
of A followed by B gives the existing composition `layerA ∘L layerB`.

## Main results

* `MagicMonotone.integral_vecActOn_layerA` and `MagicMonotone.integral_vecActOn_layerB`:
  the two local-gate averages are the existing algebraic layer operators.
* `MagicMonotone.integral_vecActOn_twoLayer`: the four-gate Heisenberg average is
  `twoLayerMoment`, as an equality of operators.
* `MagicMonotone.integral_twoLayer_endVec`: the same equality applied to any global
  input operator; rewrite with `twoLayerMoment_eq_kernel_sum` to obtain Equation (24).

The shared tensor-Haar factorization supplies independence, and `integral_vecActOn`
supplies the computed single-gate fourth moment. Coordinate and sum bookkeeping stays
private here. This file introduces no additional definitions.
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped Matrix Kronecker

namespace MagicMonotone
open SchurWeyl EuclideanSpace

private theorem tensorMap_sum_rankOne {α β γ ι κ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [Fintype ι] [Fintype κ]
    (e : γ ≃ α × β) (v : ι → EuclideanSpace ℂ α) (w : κ → EuclideanSpace ℂ β)
    (a : ι → ι → ℂ) (b : κ → κ → ℂ) :
    tensorMap e (∑ i, ∑ p, a i p • rankOne ℂ (v i) (v p))
      (∑ j, ∑ q, b j q • rankOne ℂ (w j) (w q)) =
    ∑ i, ∑ j, ∑ p, ∑ q, (a i p * b j q) •
      rankOne ℂ (tensorVec e (v i) (w j)) (tensorVec e (v p) (w q)) := by
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, tensorMap_rankOne, Finset.smul_sum, smul_smul]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  simp only [mul_comm]

private theorem tensorVec_layerA (σ τ : Equiv.Perm Copies) :
    tensorVec (tensorEntriesEquiv layerIndexA 4)
      (endVec (permOp 4 σ)) (endVec (permOp 4 τ)) = layerAKet σ τ := by
  ext p
  change _ = toEndMatrix 16 4 (V12 σ * V34 τ) p.1 p.2
  rw [toEndMatrix_layerA_perm]
  rfl

private theorem tensorVec_layerB (σ τ : Equiv.Perm Copies) :
    tensorVec (tensorEntriesEquiv layerIndexB 4)
      (endVec (permOp 4 σ)) (endVec (permOp 4 τ)) = layerBKet σ τ := by
  ext p
  change _ = toEndMatrix 16 4 (V23 σ * V41 τ) p.1 p.2
  rw [toEndMatrix_layerB_perm]
  rfl

/-- Two independent two-qubit Haar gates give the existing layer-A fourth moment.
The inverse conjugations are the physical Heisenberg action. -/
theorem integral_vecActOn_layerA :
    (∫ p, vecActOn (k := 4) (star (layerUnitaryA p))
      ∂((haarProb 4).prod (haarProb 4))) = layerA := by
  change (∫ p, vecActOn (k := 4) (star (tensorUnitary layerIndexA p.1 p.2))
    ∂((haarProb 4).prod (haarProb 4))) = _
  rw [integral_vecActOn_tensorUnitary]
  simp only [integral_vecActOn 4 (by omega)]
  unfold vecMomentOp
  rw [tensorMap_sum_rankOne]
  simp_rw [tensorVec_layerA]
  rfl

/-- The staggered ordered pairing gives the existing layer-B fourth moment. -/
theorem integral_vecActOn_layerB :
    (∫ p, vecActOn (k := 4) (star (layerUnitaryB p))
      ∂((haarProb 4).prod (haarProb 4))) = layerB := by
  change (∫ p, vecActOn (k := 4) (star (tensorUnitary layerIndexB p.1 p.2))
    ∂((haarProb 4).prod (haarProb 4))) = _
  rw [integral_vecActOn_tensorUnitary]
  simp only [integral_vecActOn 4 (by omega)]
  unfold vecMomentOp
  rw [tensorMap_sum_rankOne]
  simp_rw [tensorVec_layerB]
  rfl

private theorem integrable_layerAction
    (L : Matrix.unitaryGroup (Fin 4) ℂ × Matrix.unitaryGroup (Fin 4) ℂ →
      Matrix.unitaryGroup (Fin 16) ℂ) (hL : Continuous L) :
    Integrable (fun p => vecActOn (k := 4) (star (L p)))
      ((haarProb 4).prod (haarProb 4)) :=
  (continuous_vecActOn.comp (continuous_star.comp hL)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Four independent Haar gates, executed as A followed by B, give the existing
Heisenberg composition. The sampled circuit unitary is explicitly `B * A`. -/
theorem integral_vecActOn_twoLayer :
    (∫ p, vecActOn (k := 4) (star (layerUnitaryB p.2 * layerUnitaryA p.1))
      ∂(((haarProb 4).prod (haarProb 4)).prod
        ((haarProb 4).prod (haarProb 4)))) = twoLayerMoment := by
  simp_rw [star_mul, vecActOn_mul]
  change (∫ p, (ContinuousLinearMap.compL ℂ Vecs Vecs Vecs)
    (vecActOn (star (layerUnitaryA p.1))) (vecActOn (star (layerUnitaryB p.2)))
    ∂(((haarProb 4).prod (haarProb 4)).prod
      ((haarProb 4).prod (haarProb 4)))) = _
  rw [integral_prod_bilin _
    (integrable_layerAction layerUnitaryA continuous_layerUnitaryA)
    (integrable_layerAction layerUnitaryB continuous_layerUnitaryB),
    integral_vecActOn_layerA, integral_vecActOn_layerB]
  rfl

/-- The four-gate Haar calculation for every global operator `X`, including operators
that do not factor across a layer. Rewrite `twoLayerMoment` using Equation (24) to
obtain the explicit kernel formula. -/
theorem integral_twoLayer_endVec (X : RegOp) :
    (∫ p, endVec (actOn X (star (layerUnitaryB p.2 * layerUnitaryA p.1)))
      ∂(((haarProb 4).prod (haarProb 4)).prod
        ((haarProb 4).prod (haarProb 4)))) = twoLayerMoment (endVec X) := by
  have hi : Integrable (fun p => vecActOn (k := 4)
      (star (layerUnitaryB p.2 * layerUnitaryA p.1)))
      (((haarProb 4).prod (haarProb 4)).prod ((haarProb 4).prod (haarProb 4))) :=
    (continuous_vecActOn.comp (continuous_star.comp
      ((continuous_layerUnitaryB.comp continuous_snd).mul
        (continuous_layerUnitaryA.comp continuous_fst)))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  rw [← integral_vecActOn_twoLayer, ContinuousLinearMap.integral_apply hi]
  simp_rw [vecActOn_endVec]

end MagicMonotone
