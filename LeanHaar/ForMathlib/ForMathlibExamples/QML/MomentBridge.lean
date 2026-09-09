import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TensorPowerTraces

/-!
# From Haar trace integrals to the moment operator

Averaging `U ↦ Tr[Y · U^{⊗k} P U^{†⊗k}]` over the Haar probability measure of the unitary group
is the same as contracting `Y` against the Haar moment operator `SchurWeyl.momentOp P`. This file
proves that bridge, together with the integrability statement it needs.

## Main declarations

* `QML.integrable_trace_comp_actOn`: `U ↦ Tr[Y · actOn P U]` is Haar integrable.
* `QML.haar_integral_trace_comp_actOn`: `∫ Tr[Y · actOn P U] = Tr[Y · momentOp P]`.
-/

noncomputable section

open Matrix MeasureTheory SchurWeyl

namespace QML

variable {d k : ℕ}

/-- Each function `U ↦ Tr[Y · actOn P U]` is Haar integrable. -/
theorem integrable_trace_comp_actOn (Y P : Module.End ℂ (TensV d k)) :
    Integrable (fun U => LinearMap.trace ℂ (TensV d k) (Y ∘ₗ actOn P U)) (haarProb d) := by
  simp_rw [trace_comp_eq_sum_toEndMatrix]
  exact integrable_finsetSum _ fun I _ =>
    integrable_finsetSum _ fun J _ => (integrable_actOn_entry P J I).const_mul _

/-- **Bridge to the moment operator**: averaging a trace against the conjugation action is the
same as contracting with the Haar moment operator. -/
theorem haar_integral_trace_comp_actOn (Y P : Module.End ℂ (TensV d k)) :
    (∫ U, LinearMap.trace ℂ (TensV d k) (Y ∘ₗ actOn P U) ∂(haarProb d))
      = LinearMap.trace ℂ (TensV d k) (Y ∘ₗ momentOp P) := by
  simp_rw [trace_comp_eq_sum_toEndMatrix]
  rw [integral_finsetSum _ fun I _ => integrable_finsetSum _ fun J _ =>
    (integrable_actOn_entry P J I).const_mul _]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [integral_finsetSum _ fun J _ => (integrable_actOn_entry P J I).const_mul _]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [integral_const_mul, toEndMatrix_momentOp]
  rfl

end QML

end
