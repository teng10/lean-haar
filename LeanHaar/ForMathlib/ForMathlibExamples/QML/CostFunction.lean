import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.HaarMoments

/-!
# The cost function of a variational quantum algorithm and its Haar moments

This file defines the objects appearing in the statements of Observations 56 and 57 of the
blueprint:

* the cost function `C(U) = Tr[U ρ U† O]`, and
* the gradient expression `∂C = i Tr[U_B ρ U_B† [H, U_A† O U_A]]`.

Expectations use ordinary integrals against `SchurWeyl.haarProb`; no separate
expectation or variance definitions are introduced.

It then computes the first two Haar moments of the cost function, for arbitrary `ρ` and `O`.

## Main declarations

* `QML.cost`, `QML.gradient`.
* `QML.haar_expectation_cost`, `QML.haar_expectation_cost_sq`.
-/

noncomputable section

open Matrix MeasureTheory SchurWeyl

namespace QML

variable {d : ℕ}

/-- The cost function `C(U) = Tr[U ρ U† O]` of a variational quantum algorithm. -/
def cost (ρ O : Matrix (Fin d) (Fin d) ℂ) (U : Matrix.unitaryGroup (Fin d) ℂ) : ℂ :=
  (conjBy U ρ * O).trace

/-- The gradient expression `∂C = i Tr[U_B ρ U_B† [H, U_A† O U_A]]` for a circuit split
as `U = U_A U_B`, with generator `H`. This defines the expression; identifying it with
a derivative of a parameterized circuit requires a separate theorem. -/
def gradient (ρ O H : Matrix (Fin d) (Fin d) ℂ)
    (UA UB : Matrix.unitaryGroup (Fin d) ℂ) : ℂ :=
  Complex.I * (conjBy UB ρ * ⁅H, conjBy UA⁻¹ O⁆).trace

/-- The expectation of the cost function is `Tr ρ · Tr O / d`. -/
theorem haar_expectation_cost [NeZero d] (ρ O : Matrix (Fin d) (Fin d) ℂ) :
    (∫ U, cost ρ O U ∂(haarProb d)) = ρ.trace * O.trace / d :=
  haar_integral_trace_conj ρ O

/-- The second moment of the cost function. -/
theorem haar_expectation_cost_sq [NeZero d] [Fact (2 ≤ d)] (ρ O : Matrix (Fin d) (Fin d) ℂ) :
    (∫ U, cost ρ O U ^ 2 ∂(haarProb d)) = cId d ρ * (O.trace) ^ 2 + cSwap d ρ * (O * O).trace := by
  have hpt : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      cost ρ O U ^ 2
        = LinearMap.trace ℂ (TensV d 2) (tensorPow d 2 O ∘ₗ actOn (tensorPow d 2 ρ) U) := by
    intro U
    simp only [tensorPow, actOn_tensorOp, tensorOp_comp, trace_tensorOp_two]
    rw [Matrix.trace_mul_comm]
    simp [cost, conjBy, sq]
  simp only [hpt]
  rw [haar_integral_trace_comp_actOn_tensorPow_two ρ (tensorPow d 2 O)]
  simp only [tensorPow, trace_tensorOp_two, trace_swap_comp_tensorOp]
  ring

end QML

end
