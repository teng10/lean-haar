import LeanHaar.ForMathlib.Examples.QML.CostFunction

/-!
# Observation 56: expectation and variance of the cost function

For `n ≥ 1` qubits, a state `ρ` and a traceless observable `O`, the Haar average of the cost
function `C(U) = Tr[U ρ U† O]` vanishes and its variance is
`(Tr ρ² - 2⁻ⁿ) / (2²ⁿ - 1) · Tr O²`.
-/

noncomputable section

open Matrix MeasureTheory SchurWeyl

namespace QML

/-- **Observation 56 (expectation and variance of the cost function).**

On `n ≥ 1` qubits, for a state `ρ` (`Tr ρ = 1`) and a traceless observable `O`, the Haar
average of the cost function vanishes and its variance is
`(Tr ρ² - 2⁻ⁿ) / (2²ⁿ - 1) · Tr O²`.

The blueprint writes the last factor as `Tr[O^{⊗2}]`, but its proof evaluates it through
`Tr(𝔽 O^{⊗2}) = Tr(O²)`, which is the factor appearing here; note that `Tr[O^{⊗2}] = (Tr O)²`
vanishes for traceless `O`. -/
theorem observation56 (n : ℕ) (hn : 1 ≤ n) (ρ O : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hρ : ρ.trace = 1) (hO : O.trace = 0) :
    haarExp (2 ^ n) (cost ρ O) = 0 ∧
      haarVar (2 ^ n) (cost ρ O)
        = ((ρ * ρ).trace - ((2 : ℂ) ^ n)⁻¹) / (((2 : ℂ) ^ n) ^ 2 - 1) * (O * O).trace := by
  have hd : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : NeZero (2 ^ n) := ⟨by omega⟩
  haveI : Fact (2 ≤ 2 ^ n) := ⟨hd⟩
  have hcast : (((2 ^ n : ℕ) : ℂ)) = (2 : ℂ) ^ n := by push_cast; ring
  have hmean : haarExp (2 ^ n) (cost ρ O) = 0 := by
    rw [haar_expectation_cost, hO, mul_zero, zero_div]
  refine ⟨hmean, ?_⟩
  rw [haarVar, hmean, haar_expectation_cost_sq, hO]
  simp only [cSwap, cId, hρ, hcast]
  ring

end QML

end
