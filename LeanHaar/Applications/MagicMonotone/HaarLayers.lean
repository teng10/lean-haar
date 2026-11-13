/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Applications.MagicMonotone.Equation24
import LeanHaar.Circuits.Brickwork

/-!
# Independent Haar gates on the four-qubit register

The ordered layer gates are sampled independently from `haarProb 4`. Their fourth
Heisenberg moments are the existing algebraic layer sums, and physical execution
of A followed by B gives the existing composition `layerA ∘L layerB`.

`layerUnitaryA/B` specialize the circuit interface to the two matchings. The generic
layer formula, evaluated with the core fourth-moment Weingarten values, proves
`integral_vecActOn_layerA/B`. The two-layer and arbitrary-input identities preserve
the paper's product-Haar sampling convention and Equation (24).
-/
noncomputable section
open MeasureTheory SchurWeyl SchurWeyl.Circuits
namespace MagicMonotone

/-- A two-gate product average is the average over the two-point sample family. -/
private theorem integral_prod_eq_integral_pi_two {G E : Type*} [MeasurableSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure G) [SigmaFinite μ]
    (f : (Fin 2 → G) → E) :
    ∫ p, f ![p.1, p.2] ∂(μ.prod μ) = ∫ s, f s ∂Measure.pi (fun _ : Fin 2 => μ) := by
  rw [← (measurePreserving_finTwoArrow μ).integral_comp' (fun p => f ![p.1, p.2])]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  change f ![s 0, s 1] = f s
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem sum_fin_two_arrow {α M : Type*} [Fintype α] [AddCommMonoid M]
    (f : (Fin 2 → α) → M) : ∑ σ : Fin 2 → α, f σ = ∑ a, ∑ b, f ![a, b] := by
  rw [← (finTwoArrowEquiv α).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

/-! ### The application's layer sums are the circuit moments of the two matchings -/

private theorem inv_gram (σ π : Equiv.Perm (Fin 4)) :
    (weingartenGram (2 ^ 2) 4)⁻¹ σ π = wg (σ⁻¹ * π) := by
  have h := SchurWeyl.K4.inv_weingartenGram_four 4 (by norm_num) σ π
  simpa [wg] using h

private theorem oddKet_eq (σ : Fin 2 → Equiv.Perm (Fin 4)) :
    endVec (sitePerm 2 (fun i => σ (oddGate 2 i))) = layerAKet (σ 0) (σ 1) := by
  unfold layerAKet
  rw [layerA_regPerm]
  change endVec (regPerm fun i => σ (oddGate 2 i)) = _
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem evenKet_eq (σ : Fin 2 → Equiv.Perm (Fin 4)) :
    endVec (sitePerm 2 (fun i => σ (evenGate 2 i))) = layerBKet (σ 0) (σ 1) := by
  unfold layerBKet
  rw [layerB_regPerm]
  change endVec (regPerm fun i => σ (evenGate 2 i)) = _
  congr 2
  funext i
  fin_cases i <;> rfl

set_option maxRecDepth 1024 in
/-- The algebraic layer-A sum is the moment of the odd matching on four qubits. -/
private theorem circuitMoment_oddEdge_eq_layerA : circuitMoment 2 4 (oddEdge 2) = layerA := by
  rw [circuitMoment_oddEdge 2 2 (by norm_num)]
  simp only [sum_fin_two_arrow, Fin.prod_univ_two, oddKet_eq, inv_gram,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

set_option maxRecDepth 1024 in
/-- The algebraic layer-B sum is the moment of the even matching on four qubits. -/
private theorem circuitMoment_evenEdge_eq_layerB : circuitMoment 2 4 (evenEdge 2) = layerB := by
  rw [circuitMoment_evenEdge 2 2 (by norm_num)]
  simp only [sum_fin_two_arrow, Fin.prod_univ_two, evenKet_eq, inv_gram,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

private theorem odd_disjoint :
    Pairwise fun g h : Fin 2 => Disjoint (Set.range (oddEdge 2 g)) (Set.range (oddEdge 2 h)) :=
  fun _ _ h => oddEdge_disjoint h

private theorem even_disjoint :
    Pairwise fun g h : Fin 2 => Disjoint (Set.range (evenEdge 2 g)) (Set.range (evenEdge 2 h)) :=
  fun _ _ h => evenEdge_disjoint h

/-! ### Sampled layers and Haar averages -/

/-- `p.1` acts on `(0,1)` and `p.2` on `(2,3)`. The first qubit in each pair is
the least significant bit of the local gate index. -/
def layerUnitaryA (p : Matrix.unitaryGroup (Fin 4) ℂ × Matrix.unitaryGroup (Fin 4) ℂ) :
    Matrix.unitaryGroup (Fin 16) ℂ := circuitUnitary 2 (oddEdge 2) ![p.1, p.2]

/-- `p.1` acts on `(1,2)` and `p.2` on `(3,0)`. The first qubit in each pair is
the least significant bit of the local gate index, so the wrapping gate reads qubit 3 first. -/
def layerUnitaryB (p : Matrix.unitaryGroup (Fin 4) ℂ × Matrix.unitaryGroup (Fin 4) ℂ) :
    Matrix.unitaryGroup (Fin 16) ℂ := circuitUnitary 2 (evenEdge 2) ![p.1, p.2]

/-- The layer-A gate depends continuously on its two samples. -/
theorem continuous_layerUnitaryA : Continuous layerUnitaryA :=
  (continuous_circuitUnitary 2 (oddEdge 2)).comp (by fun_prop)

/-- The layer-B gate depends continuously on its two samples. -/
theorem continuous_layerUnitaryB : Continuous layerUnitaryB :=
  (continuous_circuitUnitary 2 (evenEdge 2)).comp (by fun_prop)

/-- Two independent two-qubit Haar gates give the existing layer-A fourth moment.
The inverse conjugations are the physical Heisenberg action. -/
theorem integral_vecActOn_layerA :
    (∫ p, vecActOn (k := 4) (star (layerUnitaryA p))
      ∂((haarProb 4).prod (haarProb 4))) = layerA := by
  have h : (∫ p, vecActOn (k := 4) (star (layerUnitaryA p))
      ∂((haarProb 4).prod (haarProb 4))) = (circuitMoment 2 4 (oddEdge 2)).adjoint :=
    (integral_prod_eq_integral_pi_two (haarProb 4)
      (fun s => vecActOn (k := 4) (star (circuitUnitary 2 (oddEdge 2) s)))).trans
      (integral_star_circuitUnitary 2 4 (oddEdge 2))
  rw [h, circuitMoment_adjoint_of_disjoint 2 (oddEdge 2) odd_disjoint,
    circuitMoment_oddEdge_eq_layerA]

/-- The staggered ordered pairing gives the existing layer-B fourth moment. -/
theorem integral_vecActOn_layerB :
    (∫ p, vecActOn (k := 4) (star (layerUnitaryB p))
      ∂((haarProb 4).prod (haarProb 4))) = layerB := by
  have h : (∫ p, vecActOn (k := 4) (star (layerUnitaryB p))
      ∂((haarProb 4).prod (haarProb 4))) = (circuitMoment 2 4 (evenEdge 2)).adjoint :=
    (integral_prod_eq_integral_pi_two (haarProb 4)
      (fun s => vecActOn (k := 4) (star (circuitUnitary 2 (evenEdge 2) s)))).trans
      (integral_star_circuitUnitary 2 4 (evenEdge 2))
  rw [h, circuitMoment_adjoint_of_disjoint 2 (evenEdge 2) even_disjoint,
    circuitMoment_evenEdge_eq_layerB]

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

/-- The four-copy, four-qubit Heisenberg calculation is the adjoint of the generic
Schrödinger brickwork moment with two matching layers. -/
theorem twoLayerMoment_eq_adjoint_brickworkMoment :
    twoLayerMoment = (brickworkMoment 2 4 2 2).adjoint := by
  rw [brickworkMoment_two, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    circuitMoment_adjoint_of_disjoint 2 (oddEdge 2) odd_disjoint,
    circuitMoment_adjoint_of_disjoint 2 (evenEdge 2) even_disjoint,
    circuitMoment_oddEdge_eq_layerA, circuitMoment_evenEdge_eq_layerB]
  rfl

end MagicMonotone
