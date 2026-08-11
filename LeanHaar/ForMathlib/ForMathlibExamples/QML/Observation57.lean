import LeanHaar.ForMathlib.ForMathlibExamples.QML.CommutatorTrace
import LeanHaar.ForMathlib.ForMathlibExamples.QML.CostFunction

/-!
# Observation 57: barren plateaus

For two independent Haar-random unitaries `U_A`, `U_B`, a state `ρ` and traceless `O` and `H`,
the gradient `∂C = i Tr[U_B ρ U_B† [H, U_A† O U_A]]` of the cost function has vanishing mean and
variance `2d ((Tr ρ² - d⁻¹)/(d² - 1)) (Tr O² / (d² - 1)) Tr H²`, which is exponentially small in
the number of qubits.
-/

noncomputable section

open Matrix MeasureTheory SchurWeyl

namespace QML

/-- **Observation 57 (expectation of the gradient of the cost function).**

For two independent Haar-random unitaries `U_A`, `U_B`, a state `ρ` (`Tr ρ = 1`) and traceless
`O` and `H`, the gradient of the cost function has vanishing mean. -/
theorem observation57_expectation (d : ℕ) (hd : 2 ≤ d) (ρ O H : Matrix (Fin d) (Fin d) ℂ) :
    haarExp₂ d (gradient ρ O H) = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hmean_inner : ∀ UA : Matrix.unitaryGroup (Fin d) ℂ,
      (∫ UB, gradient ρ O H UA UB ∂(haarProb d)) = 0 := by
    intro UA
    simp only [gradient]
    rw [integral_const_mul, haar_integral_trace_conj ρ _, trace_commutator, mul_zero, zero_div,
      mul_zero]
  simp [haarExp₂, hmean_inner]

/-- **Observation 57 (variance of the gradient of the cost function).**

For two independent Haar-random unitaries `U_A`, `U_B`, a state `ρ` (`Tr ρ = 1`) and traceless
`O` and `H`, the gradient of the cost function has variance
`2d ((Tr ρ² - d⁻¹)/(d² - 1)) (Tr O² / (d² - 1)) Tr H²`. -/
theorem observation57_variance (d : ℕ) (hd : 2 ≤ d) (ρ O H : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.trace = 1) (hO : O.trace = 0) (hH : H.trace = 0) :
    haarVar₂ d (gradient ρ O H)
      = 2 * d * (((ρ * ρ).trace - (d : ℂ)⁻¹) / ((d : ℂ) ^ 2 - 1))
          * ((O * O).trace / ((d : ℂ) ^ 2 - 1)) * (H * H).trace := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : Fact (2 ≤ d) := ⟨hd⟩
  have hmean : haarExp₂ d (gradient ρ O H) = 0 := observation57_expectation d hd ρ O H
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
    simp only [haarExp] at hcost
    rw [hcost, trace_commutator]
    ring
  have hsq : haarExp₂ d (fun UA UB => gradient ρ O H UA UB ^ 2)
      = -(cSwap d ρ) * (2 * cSwap d O * ((H.trace) ^ 2 - d * (H * H).trace)) := by
    simp only [haarExp₂, hsq_inner]
    rw [integral_const_mul, haar_integral_trace_commutator_sq]
  rw [haarVar₂, hmean, hsq]
  simp only [cSwap, hρ, hO, hH]
  ring

end QML

end
