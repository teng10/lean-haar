import LeanHaar.ForMathlib.Haar
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.Swap

/-!
# Example: Computing moments for k = 2

The shared swap and tensor identities reduce the Haar trace constraints to a
2 × 2 scalar system. Solving it gives the identity and swap coefficients below.
-/

open SchurWeyl

/-- Compute the k = 2nd order moment and obtain the coefficients.
-/
theorem k2_moment (d : ℕ) [NeZero d] [Fact (2 ≤ d)] (O : Module.End ℂ (TensV d 2)) :
  momentOp O = ((LinearMap.trace ℂ (TensV d 2) O - (d : ℂ)⁻¹ • LinearMap.trace ℂ (TensV d 2) (𝔽 d • O)) / (d^2 - 1)) • LinearMap.id + ((LinearMap.trace ℂ (TensV d 2) (𝔽 d • O) - (d : ℂ)⁻¹ • LinearMap.trace ℂ (TensV d 2) O) / (d^2 - 1)) • 𝔽 d
  := by
  obtain ⟨c, hmoment, hperm⟩ := weingarten_moment_haar O
  rw [sum_perm_k2_eq_set_id_swap] at hmoment
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at hmoment

  -- Define aliases
  let c_id := c (Equiv.refl (Fin 2))
  let c_swap := c (Equiv.swap (0 : Fin 2) (1 : Fin 2))

  -- Specialize hperm
  have h_trace_id : LinearMap.trace ℂ (TensV d 2) (permDual d (Equiv.refl (Fin 2)) ∘ₗ O) =
        c_id * LinearMap.trace ℂ (TensV d 2) (permDual d (Equiv.refl (Fin 2)) ∘ₗ permOp d (Equiv.refl (Fin 2))) +
        c_swap * LinearMap.trace ℂ (TensV d 2) (permDual d (Equiv.refl (Fin 2)) ∘ₗ permOp d (Equiv.swap (0 : Fin 2) (1 : Fin 2))) := by
      specialize hperm (Equiv.refl (Fin 2))
      rw [sum_perm_k2_eq_set_id_swap] at hperm
      rw [Finset.sum_insert (by decide), Finset.sum_singleton] at hperm
      exact hperm

  have h_trace_swap : LinearMap.trace ℂ (TensV d 2) (permDual d (Equiv.swap 0 1) ∘ₗ O) = c_id * (d : ℂ) + c_swap * (d : ℂ)^2 := by
      specialize hperm (Equiv.swap 0 1)
      rw [sum_perm_k2_eq_set_id_swap] at hperm
      rw [Finset.sum_insert (by decide), Finset.sum_singleton] at hperm
      -- Rewrite operator evaluations inside hperm
      rw [permDual_k2_swap, permOp_k2_id, permOp_k2_swap] at hperm
      rw [LinearMap.comp_id, swap_swap] at hperm
      -- Rewrite trace evaluations inside hperm
      rw [trace_k2_swap, trace_k2_id] at hperm
      exact hperm

  -- Clean up h_trace_id similarly to h_trace_swap
  rw [permDual_k2_id, permOp_k2_id, permOp_k2_swap] at h_trace_id
  simp only [LinearMap.id_comp, LinearMap.comp_id] at h_trace_id
  rw [trace_k2_id, trace_k2_swap] at h_trace_id

  rw [permDual_k2_swap] at h_trace_swap

  have hd2 : 2 ≤ d := Fact.out
  have hdiv : (d : ℂ)^2 - 1 ≠ 0 := by
    intro h
    norm_cast at h
    have h_int : (d : ℤ)^2 - 1 = 0 := by exact_mod_cast h
    have hd2_z : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd2
    nlinarith

  -- Solve for c_id and c_swap explicitly from the 2x2 system
  have hc_id : c_id = (LinearMap.trace ℂ (TensV d 2) O - (d : ℂ)⁻¹ * LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ O)) / ((d : ℂ)^2 - 1) := by
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    rw [eq_div_iff hdiv, inv_eq_one_div]
    field_simp [hd, hdiv]
    linear_combination h_trace_swap - (d : ℂ) * h_trace_id

  have hc_swap : c_swap = (LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ O) - (d : ℂ)⁻¹ * LinearMap.trace ℂ (TensV d 2) O) / ((d : ℂ)^2 - 1) := by
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    rw [eq_div_iff hdiv, inv_eq_one_div]
    field_simp [hd, hdiv]
    linear_combination h_trace_id - (d : ℂ) * h_trace_swap

  -- Substitute into hmoment, achieve goal
  rw [permOp_k2_id, permOp_k2_swap] at hmoment
  have h_goal : momentOp O = c_id • LinearMap.id + c_swap • 𝔽 d := hmoment
  rw [hc_id, hc_swap] at h_goal
  exact h_goal
