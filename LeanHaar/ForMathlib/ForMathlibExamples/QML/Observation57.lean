import Mathlib.Algebra.Lie.Classical
import LeanHaar.ForMathlib.ForMathlibExamples.QML.CostFunction

/-!
# Observation 57: barren plateaus

For two independent Haar-random unitaries `U_A`, `U_B`, a state `ρ` and traceless `O` and `H`,
the gradient `∂C = i Tr[U_B ρ U_B† [H, U_A† O U_A]]` of the cost function has vanishing mean and
variance `2d ((Tr ρ² - d⁻¹)/(d² - 1)) (Tr O² / (d² - 1)) Tr H²`, which is exponentially small in
the number of qubits.

The statements retain the iterated Haar integrals in the order `U_A`, then `U_B`.
The variance formula is the algebraic square-moment difference `𝔼[∂C²] - 𝔼[∂C]²`
for complex matrices; a real probabilistic interpretation requires additional
real-valuedness and square-integrability results.
-/

noncomputable section

open Matrix MeasureTheory SchurWeyl

namespace QML

/-- **Observation 57 (expectation of the gradient of the cost function).**

For two independent Haar-random unitaries `U_A`, `U_B` and arbitrary matrices
`ρ`, `O`, and `H`, the gradient expression has vanishing mean. No normalization or
tracelessness hypotheses are needed. -/
theorem observation57_expectation (d : ℕ) (hd : 2 ≤ d) (ρ O H : Matrix (Fin d) (Fin d) ℂ) :
    (∫ UA, (∫ UB, gradient ρ O H UA UB ∂(haarProb d)) ∂(haarProb d)) = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hmean_inner : ∀ UA : Matrix.unitaryGroup (Fin d) ℂ,
      (∫ UB, gradient ρ O H UA UB ∂(haarProb d)) = 0 := by
    intro UA
    simp only [gradient]
    rw [integral_const_mul, haar_integral_trace_conj ρ _,
      LieAlgebra.matrix_trace_commutator_zero, mul_zero, zero_div, mul_zero]
  simp [hmean_inner]

/-- **Observation 57 (variance of the gradient of the cost function).**

For two independent Haar-random unitaries `U_A`, `U_B`, a state `ρ` (`Tr ρ = 1`) and traceless
`O` and `H`, the gradient of the cost function has variance
`2d ((Tr ρ² - d⁻¹)/(d² - 1)) (Tr O² / (d² - 1)) Tr H²`. -/
theorem observation57_variance (d : ℕ) (hd : 2 ≤ d) (ρ O H : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.trace = 1) (hO : O.trace = 0) (hH : H.trace = 0) :
    (∫ UA, (∫ UB, gradient ρ O H UA UB ^ 2 ∂(haarProb d)) ∂(haarProb d))
      - (∫ UA, (∫ UB, gradient ρ O H UA UB ∂(haarProb d)) ∂(haarProb d)) ^ 2
      = 2 * d * (((ρ * ρ).trace - (d : ℂ)⁻¹) / ((d : ℂ) ^ 2 - 1))
          * ((O * O).trace / ((d : ℂ) ^ 2 - 1)) * (H * H).trace := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : Fact (2 ≤ d) := ⟨hd⟩
  have hmean : (∫ UA, (∫ UB, gradient ρ O H UA UB ∂(haarProb d)) ∂(haarProb d)) = 0 :=
    observation57_expectation d hd ρ O H
  -- the inner average over `U_B` of the squared gradient
  have hsq_inner : ∀ UA : Matrix.unitaryGroup (Fin d) ℂ,
      (∫ UB, gradient ρ O H UA UB ^ 2 ∂(haarProb d))
        = -(cSwap d ρ) * (⁅H, conjBy UA⁻¹ O⁆ * ⁅H, conjBy UA⁻¹ O⁆).trace := by
    intro UA
    have hsq : ∀ UB : Matrix.unitaryGroup (Fin d) ℂ,
        gradient ρ O H UA UB ^ 2 = -(cost ρ ⁅H, conjBy UA⁻¹ O⁆ UB ^ 2) := by
      intro UB
      simp [gradient, cost, mul_pow, Complex.I_sq]
    simp_rw [hsq]
    rw [integral_neg]
    have hcost := haar_expectation_cost_sq (d := d) ρ ⁅H, conjBy UA⁻¹ O⁆
    rw [hcost, LieAlgebra.matrix_trace_commutator_zero]
    ring
  have hsq : (∫ UA, (∫ UB, gradient ρ O H UA UB ^ 2 ∂(haarProb d)) ∂(haarProb d))
      = -(cSwap d ρ) * (2 * cSwap d O * ((H.trace) ^ 2 - d * (H * H).trace)) := by
    simp only [hsq_inner]
    rw [integral_const_mul, haar_integral_trace_commutator_sq]
  rw [hmean, hsq]
  simp only [cSwap, hρ, hO, hH]
  ring

end QML

end
