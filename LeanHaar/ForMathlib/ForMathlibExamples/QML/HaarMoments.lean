import LeanHaar.ForMathlib.Examples.QML.HaarInvariance
import LeanHaar.ForMathlib.Examples.QML.MomentBridge

/-!
# The first two Haar moments of a conjugated matrix

Combining the bridge to the moment operator with the repository's moment computations
`SchurWeyl.k1_moment` and `SchurWeyl.k2_moment`, this file evaluates

* the first moment `∫ Tr[U ρ U† O] = Tr ρ · Tr O / d`, and
* the second moment `𝔼_U[(U M U†)^{⊗2}] = cId · 𝟙 + cSwap · 𝔽` together with its contracted
  form and the version where `U` is replaced by `U⁻¹` (legitimate by inversion invariance of the
  Haar measure).

## Main declarations

* `QML.haar_integral_trace_conj`: the first Haar moment.
* `QML.cId`, `QML.cSwap`: the Weingarten coefficients of the identity and of the swap.
* `QML.momentOp_tensorPow_two`, `QML.haar_integral_trace_comp_actOn_tensorPow_two`,
  `QML.haar_integral_trace_comp_actOn_inv_tensorPow_two`: the second Haar moment.
-/

noncomputable section

open Matrix MeasureTheory SchurWeyl

namespace QML

variable {d : ℕ}

/-- **First Haar moment.** For any matrices `ρ` and `O`, the Haar average of `Tr[U ρ U† O]` is
`Tr ρ · Tr O / d`. -/
theorem haar_integral_trace_conj [NeZero d] (ρ O : Matrix (Fin d) (Fin d) ℂ) :
    (∫ U, (conjBy U ρ * O).trace ∂(haarProb d)) = ρ.trace * O.trace / d := by
  have hpt : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (conjBy U ρ * O).trace
        = LinearMap.trace ℂ (TensV d 1) (tensorPow d 1 O ∘ₗ actOn (tensorPow d 1 ρ) U) := by
    intro U
    simp only [tensorPow, actOn_tensorOp, tensorOp_comp, trace_tensorOp]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
    exact Matrix.trace_mul_comm _ _
  simp_rw [hpt]
  rw [haar_integral_trace_comp_actOn, k1_moment]
  simp only [LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul, tensorPow,
    trace_tensorOp, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  rw [div_mul_eq_mul_div, mul_comm]

/-- The Weingarten coefficient of the identity in the second Haar moment of `M^{⊗2}`. -/
def cId (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ((M.trace) ^ 2 - (d : ℂ)⁻¹ * (M * M).trace) / ((d : ℂ) ^ 2 - 1)

/-- The Weingarten coefficient of the swap in the second Haar moment of `M^{⊗2}`. -/
def cSwap (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ((M * M).trace - (d : ℂ)⁻¹ * (M.trace) ^ 2) / ((d : ℂ) ^ 2 - 1)

/-- **Second Haar moment as an operator identity**:
`𝔼_U [(U M U†)^{⊗2}] = cId · 𝟙 + cSwap · 𝔽`. -/
theorem momentOp_tensorPow_two [NeZero d] [Fact (2 ≤ d)] (M : Matrix (Fin d) (Fin d) ℂ) :
    momentOp (tensorPow d 2 M) = cId d M • LinearMap.id + cSwap d M • 𝔽 d := by
  have hswap : LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ tensorPow d 2 M) = (M * M).trace := by
    rw [tensorPow, trace_swap_comp_tensorOp]
  have hid : LinearMap.trace ℂ (TensV d 2) (tensorPow d 2 M) = (M.trace) ^ 2 := by
    rw [tensorPow, trace_tensorOp_two, sq]
  rw [k2_moment d (tensorPow d 2 M)]
  have hsmul : (𝔽 d : Module.End ℂ (TensV d 2)) • tensorPow d 2 M = 𝔽 d ∘ₗ tensorPow d 2 M := rfl
  rw [hsmul, hswap, hid]
  simp only [cId, cSwap, smul_eq_mul]

/-- **Second Haar moment, contracted form.** For any operator `Y` on `TensV d 2`,
`𝔼_U Tr[Y (U M U†)^{⊗2}] = cId · Tr Y + cSwap · Tr(𝔽 Y)`. -/
theorem haar_integral_trace_comp_actOn_tensorPow_two [NeZero d] [Fact (2 ≤ d)]
    (M : Matrix (Fin d) (Fin d) ℂ) (Y : Module.End ℂ (TensV d 2)) :
    (∫ U, LinearMap.trace ℂ (TensV d 2) (Y ∘ₗ actOn (tensorPow d 2 M) U) ∂(haarProb d))
      = cId d M * LinearMap.trace ℂ (TensV d 2) Y
        + cSwap d M * LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ Y) := by
  rw [haar_integral_trace_comp_actOn, momentOp_tensorPow_two]
  have hcomm : LinearMap.trace ℂ (TensV d 2) (Y ∘ₗ 𝔽 d)
      = LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ Y) := LinearMap.trace_comp_comm' _ _
  simp [LinearMap.comp_add, LinearMap.comp_smul, hcomm]

/-- The same average, with `U` replaced by `U⁻¹`: this is legitimate because the Haar measure is
inversion invariant. -/
theorem haar_integral_trace_comp_actOn_inv_tensorPow_two [NeZero d] [Fact (2 ≤ d)]
    (M : Matrix (Fin d) (Fin d) ℂ) (Y : Module.End ℂ (TensV d 2)) :
    (∫ U, LinearMap.trace ℂ (TensV d 2) (Y ∘ₗ actOn (tensorPow d 2 M) U⁻¹) ∂(haarProb d))
      = cId d M * LinearMap.trace ℂ (TensV d 2) Y
        + cSwap d M * LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ Y) := by
  rw [integral_inv_eq_self
    (fun U => LinearMap.trace ℂ (TensV d 2) (Y ∘ₗ actOn (tensorPow d 2 M) U))]
  exact haar_integral_trace_comp_actOn_tensorPow_two M Y

end QML

end
