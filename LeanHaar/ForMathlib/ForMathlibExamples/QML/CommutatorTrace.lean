import LeanHaar.ForMathlib.ForMathlibExamples.QML.HaarMoments

/-!
# Traces of squared commutators and their Haar averages

The barren plateau result rests on the trace of `[H, U† O U]²`. This file proves the purely
algebraic swap trick `Tr([A,B]²) = 2 Tr(ABAB) - 2 Tr(A²B²)` and then averages it over the Haar
measure: the two quartic traces become contractions of `(U† O U)^{⊗2}` against the fixed
operators `𝔽 (H ⊗ H)` and `𝔽 (H² ⊗ 1)`, which the second Haar moment evaluates.

## Main declarations

* `QML.trace_commutator_sq`: the swap trick.
* `QML.haar_integral_trace_commutator_sq`: the Haar average of `Tr([H, U† O U]²)`.
-/

noncomputable section

open Matrix MeasureTheory SchurWeyl

namespace QML

variable {d : ℕ}

/-- **Swap trick** (Lemma "swap trick" of the blueprint), in its purely algebraic form:
`Tr([A,B]²) = 2 Tr(ABAB) - 2 Tr(A²B²)`. -/
theorem trace_commutator_sq (A B : Matrix (Fin d) (Fin d) ℂ) :
    (⁅A, B⁆ * ⁅A, B⁆).trace = 2 * (A * B * (A * B)).trace - 2 * (A * A * (B * B)).trace := by
  have cycle : ∀ W X Y Z : Matrix (Fin d) (Fin d) ℂ,
      (W * X * (Y * Z)).trace = (Z * W * (X * Y)).trace := by
    intro W X Y Z
    have hassoc : W * X * (Y * Z) = W * X * Y * Z := by simp [Matrix.mul_assoc]
    rw [hassoc, Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  have h1 : (A * B * (B * A)).trace = (A * A * (B * B)).trace := cycle A B B A
  have h2 : (B * A * (A * B)).trace = (A * A * (B * B)).trace :=
    (Matrix.trace_mul_comm (B * A) (A * B)).trans h1
  have h3 : (B * A * (B * A)).trace = (A * B * (A * B)).trace := cycle B A B A
  rw [Ring.lie_def]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, h1, h2, h3]
  ring

/-- The trace of the commutator `[H, X]` vanishes. -/
theorem trace_commutator (H X : Matrix (Fin d) (Fin d) ℂ) : (⁅H, X⁆).trace = 0 := by
  rw [Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm]
  ring

/-- The Haar average of `Tr([H, U† O U]²)`, the key ingredient of the barren plateau result.

The swap trick turns the two quartic traces into contractions of `(U† O U)^{⊗2}` against the
fixed operators `𝔽 (H ⊗ H)` and `𝔽 (H² ⊗ 1)`, which the second Haar moment evaluates. -/
theorem haar_integral_trace_commutator_sq [NeZero d] [Fact (2 ≤ d)]
    (O H : Matrix (Fin d) (Fin d) ℂ) :
    (∫ UA, (⁅H, conjBy UA⁻¹ O⁆ * ⁅H, conjBy UA⁻¹ O⁆).trace ∂(haarProb d))
      = 2 * cSwap d O * ((H.trace) ^ 2 - d * (H * H).trace) := by
  have hconj : ∀ UA : Matrix.unitaryGroup (Fin d) ℂ,
      tensorPow d 2 (conjBy UA⁻¹ O) = actOn (tensorPow d 2 O) UA⁻¹ := by
    intro UA
    simp only [tensorPow, actOn_tensorOp]
    rfl
  have hpt : ∀ UA : Matrix.unitaryGroup (Fin d) ℂ,
      (⁅H, conjBy UA⁻¹ O⁆ * ⁅H, conjBy UA⁻¹ O⁆).trace
        = 2 * LinearMap.trace ℂ (TensV d 2)
            ((𝔽 d ∘ₗ tensorOp ![H, H]) ∘ₗ actOn (tensorPow d 2 O) UA⁻¹)
          - 2 * LinearMap.trace ℂ (TensV d 2)
            ((𝔽 d ∘ₗ tensorOp ![H * H, 1]) ∘ₗ actOn (tensorPow d 2 O) UA⁻¹) := by
    intro UA
    have h₁ : LinearMap.trace ℂ (TensV d 2)
        ((𝔽 d ∘ₗ tensorOp ![H, H]) ∘ₗ tensorPow d 2 (conjBy UA⁻¹ O))
          = (H * conjBy UA⁻¹ O * (H * conjBy UA⁻¹ O)).trace := by
      rw [tensorPow, LinearMap.comp_assoc, tensorOp_comp, trace_swap_comp_tensorOp]
      simp
    have h₂ : LinearMap.trace ℂ (TensV d 2)
        ((𝔽 d ∘ₗ tensorOp ![H * H, 1]) ∘ₗ tensorPow d 2 (conjBy UA⁻¹ O))
          = (H * H * (conjBy UA⁻¹ O * conjBy UA⁻¹ O)).trace := by
      rw [tensorPow, LinearMap.comp_assoc, tensorOp_comp, trace_swap_comp_tensorOp]
      simp [Matrix.mul_assoc]
    rw [trace_commutator_sq, ← hconj UA, h₁, h₂]
  simp_rw [hpt]
  rw [integral_sub
      (((integrable_trace_comp_actOn (𝔽 d ∘ₗ tensorOp ![H, H])
        (tensorPow d 2 O)).comp_inv).const_mul 2)
      (((integrable_trace_comp_actOn (𝔽 d ∘ₗ tensorOp ![H * H, 1])
        (tensorPow d 2 O)).comp_inv).const_mul 2),
    integral_const_mul, integral_const_mul,
    haar_integral_trace_comp_actOn_inv_tensorPow_two O (𝔽 d ∘ₗ tensorOp ![H, H]),
    haar_integral_trace_comp_actOn_inv_tensorPow_two O (𝔽 d ∘ₗ tensorOp ![H * H, 1])]
  have hY₁trace : LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ tensorOp ![H, H]) = (H * H).trace := by
    rw [trace_swap_comp_tensorOp]; simp
  have hY₁swap : LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ 𝔽 d ∘ₗ tensorOp ![H, H])
      = (H.trace) ^ 2 := by
    rw [← LinearMap.comp_assoc, swap_swap, LinearMap.id_comp, trace_tensorOp_two]
    simp [sq]
  have hY₂trace : LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ tensorOp ![H * H, 1])
      = (H * H).trace := by
    rw [trace_swap_comp_tensorOp]; simp
  have hY₂swap : LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ 𝔽 d ∘ₗ tensorOp ![H * H, 1])
      = d * (H * H).trace := by
    rw [← LinearMap.comp_assoc, swap_swap, LinearMap.id_comp, trace_tensorOp_two]
    simp [Matrix.trace_one, mul_comm]
  rw [hY₁trace, hY₁swap, hY₂trace, hY₂swap]
  ring

end QML

end
