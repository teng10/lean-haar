import LeanHaar.ForMathlib.ForMathlibExamples.k1Moment
import LeanHaar.ForMathlib.ForMathlibExamples.k2Moment
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.HaarInvariance
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.HaarMomentBridge

/-!
# The first two Haar moments of a conjugated matrix

Combining the bridge to the moment operator with the repository's moment computations
`k1_moment` and `k2_moment`, this file evaluates

* the first moment `∫ Tr[U ρ U† O] = Tr ρ · Tr O / d`, and
* the second moment `𝔼_U[(U M U†)^{⊗2}] = cId · 𝟙 + cSwap · 𝔽` together with its contracted
  form and the version where `U` is replaced by `U⁻¹` (legitimate by inversion invariance of the
  Haar measure).

## Main declarations

* `SchurWeyl.haar_integral_trace_conj`: the first Haar moment.
* `SchurWeyl.cId`, `SchurWeyl.cSwap`: the Weingarten coefficients of the identity and of the swap.
* `SchurWeyl.momentOp_tensorPow_two`, `SchurWeyl.haar_integral_trace_comp_actOn_tensorPow_two`,
  `SchurWeyl.haar_integral_trace_comp_actOn_inv_tensorPow_two`: the second Haar moment.
* `SchurWeyl.haar_integral_trace_commutator_sq`: the resulting Haar average of a squared
  commutator trace.
-/

noncomputable section

open Matrix MeasureTheory

namespace SchurWeyl

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

/-! ### Commutator averages -/

/-- Expand the trace of a squared commutator using cyclicity of the matrix trace. -/
private theorem trace_commutator_sq (A B : Matrix (Fin d) (Fin d) ℂ) :
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

/-- The Haar average of `Tr([H, U† O U]²)` for arbitrary matrices `O` and `H`.

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

end SchurWeyl

end
