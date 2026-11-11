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
import LeanHaar.Circuits.Circuit
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
* `MagicMonotone.twoLayerMoment_eq_adjoint_brickworkMoment`: the calculation is the
  adjoint of the generic four-copy circuit moment on two matching layers.

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

/-! ### Identification with the compositional circuit interface -/

open SchurWeyl.Circuits

private theorem tensorUnitary_eq_circuitUnitary
    (e : Fin 16 ≃ Fin 4 × Fin 4) (sites : Fin 2 → (Fin 2 ↪ Fin 4))
    (hread : ∀ x, e x = (localRead 2 (sites 0) x, localRead 2 (sites 1) x))
    (hleft : ∀ x y, (e x).2 = (e y).2 ↔
      ∀ i, i ∉ Set.range (sites 0) → registerEquiv 2 4 x i = registerEquiv 2 4 y i)
    (hright : ∀ x y, (e x).1 = (e y).1 ↔
      ∀ i, i ∉ Set.range (sites 1) → registerEquiv 2 4 x i = registerEquiv 2 4 y i)
    (U V : Matrix.unitaryGroup (Fin 4) ℂ) :
    tensorUnitary e U V = circuitUnitary 2 sites ![U, V] := by
  have hU : tensorUnitary e U 1 = placeUnitary 2 (sites 0) U := by
    apply Subtype.ext
    ext x y
    refine Eq.trans ?_ (placeUnitary_apply 2 (sites 0) U x y).symm
    change U (e x).1 (e y).1 * (1 : Matrix (Fin 4) (Fin 4) ℂ) (e x).2 (e y).2 = _
    rw [Matrix.one_apply]
    rw [show (e x).1 = localRead 2 (sites 0) x from congrArg Prod.fst (hread x),
      show (e y).1 = localRead 2 (sites 0) y from congrArg Prod.fst (hread y)]
    congr 1
    exact if_congr (hleft x y) rfl rfl
  have hV : tensorUnitary e 1 V = placeUnitary 2 (sites 1) V := by
    apply Subtype.ext
    ext x y
    refine Eq.trans ?_ (placeUnitary_apply 2 (sites 1) V x y).symm
    change (1 : Matrix (Fin 4) (Fin 4) ℂ) (e x).1 (e y).1 * V (e x).2 (e y).2 = _
    rw [Matrix.one_apply, mul_comm]
    rw [show (e x).2 = localRead 2 (sites 1) x from congrArg Prod.snd (hread x),
      show (e y).2 = localRead 2 (sites 1) y from congrArg Prod.snd (hread y)]
    congr 1
    exact if_congr (hright x y) rfl rfl
  have h : tensorUnitary e U V = tensorUnitary e 1 V * tensorUnitary e U 1 := by
    simpa using tensorUnitary_mul e 1 U V 1
  rw [h, hU, hV]
  simp [circuitUnitary]

set_option maxRecDepth 8192 in
private theorem layerUnitaryA_eq_circuitUnitary (U V : Matrix.unitaryGroup (Fin 4) ℂ) :
    layerUnitaryA (U, V) = circuitUnitary 2 (oddEdge 2) ![U, V] := by
  apply tensorUnitary_eq_circuitUnitary
  · decide
  · simp only [Set.mem_range, not_exists]
    decide
  · simp only [Set.mem_range, not_exists]
    decide

set_option maxRecDepth 8192 in
private theorem layerUnitaryB_eq_circuitUnitary (U V : Matrix.unitaryGroup (Fin 4) ℂ) :
    layerUnitaryB (U, V) = circuitUnitary 2 (evenEdge 2) ![U, V] := by
  apply tensorUnitary_eq_circuitUnitary
  · decide
  · simp only [Set.mem_range, not_exists]
    decide
  · simp only [Set.mem_range, not_exists]
    decide

private theorem adjoint_circuitMoment_layer
    (sites : Fin 2 → (Fin 2 ↪ Fin 4))
    (L : Matrix.unitaryGroup (Fin 4) ℂ × Matrix.unitaryGroup (Fin 4) ℂ →
      Matrix.unitaryGroup (Fin 16) ℂ) (hL : Continuous L)
    (heq : ∀ U V, L (U, V) = circuitUnitary 2 sites ![U, V]) :
    (circuitMoment 2 4 sites).adjoint =
      ∫ p, vecActOn (k := 4) (star (L p)) ∂((haarProb 4).prod (haarProb 4)) := by
  have hmoment : circuitMoment 2 4 sites =
      ∫ p, vecActOn (k := 4) (L p) ∂((haarProb 4).prod (haarProb 4)) := by
    rw [← integral_circuitUnitary,
      ← (measurePreserving_finTwoArrow (haarProb 4)).integral_comp'
        (fun p => vecActOn (k := 4) (L p))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    change vecActOn (circuitUnitary 2 sites s) = vecActOn (L (s 0, s 1))
    rw [heq]
    congr 2
    funext i
    fin_cases i <;> rfl
  rw [hmoment]
  exact adjoint_integral_vecActOn
    ((continuous_vecActOn.comp hL).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

/-- The four-copy, four-qubit Heisenberg calculation is the adjoint of the generic
Schrödinger brickwork moment with two matching layers. -/
theorem twoLayerMoment_eq_adjoint_brickworkMoment :
    twoLayerMoment = (brickworkMoment 2 4 2 2).adjoint := by
  rw [brickworkMoment_layers, scheduleProduct_two]
  change twoLayerMoment =
    (circuitMoment 2 4 (evenEdge 2) * circuitMoment 2 4 (oddEdge 2)).adjoint
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    adjoint_circuitMoment_layer _ _ continuous_layerUnitaryA layerUnitaryA_eq_circuitUnitary,
    adjoint_circuitMoment_layer _ _ continuous_layerUnitaryB layerUnitaryB_eq_circuitUnitary,
    integral_vecActOn_layerA, integral_vecActOn_layerB]
  rfl

end MagicMonotone
