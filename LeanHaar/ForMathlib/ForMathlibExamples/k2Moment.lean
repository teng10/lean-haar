import LeanHaar.ForMathlib.Haar
import LeanHaar.ForMathlib.Defs
import LeanHaar.ForMathlib.DCT

import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Example: Computing moments for k = 2
-/

open SchurWeyl

variable {d : ℕ}

/-- The swap operator `𝔽 d` on the tensor space `TensV d 2` representing the transposition `(0 1)`. -/
noncomputable def 𝔽 (d : ℕ) : Module.End ℂ (TensV d 2) := permRep d 2 (Equiv.swap (0 : Fin 2) (1 : Fin 2))

/-- S_2 is composed of elements {id, SWAP}-/
lemma sum_perm_k2_eq_set_id_swap : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {Equiv.refl (Fin 2), Equiv.swap (0 : Fin 2) (1 : Fin 2)} := by
  decide

/-- The reflective permutation operator is the identity linear map. -/
lemma permOp_k2_id : permOp d (Equiv.refl (Fin 2)) = LinearMap.id := by
  change permMonoidHom d 2 1 = LinearMap.id
  exact (permMonoidHom d 2).map_one

/-- The SWAP permutation operator is the SWAP linear map (as defined above).-/
lemma permOp_k2_swap : permOp d (Equiv.swap 0 1) = 𝔽 d := by
  rfl

/-- The conjugate transpose of the identity is itself.-/
lemma permDual_k2_id : permDual d (Equiv.refl (Fin 2)) = LinearMap.id := by
  exact permOp_k2_id

/-- The conjugate transpose of the SWAP operator is itself.-/
lemma permDual_k2_swap : permDual d (Equiv.swap 0 1) = 𝔽 d := by
  unfold permDual
  rw [Equiv.swap_inv]
  exact permOp_k2_swap

/-- SWAP composed with SWAP is the identity.-/
lemma swap_swap : 𝔽 d ∘ₗ 𝔽 d = LinearMap.id := by
  change (permMonoidHom d 2 (Equiv.swap 0 1)) * (permMonoidHom d 2 (Equiv.swap 0 1)) = LinearMap.id
  rw [← (permMonoidHom d 2).map_mul, Equiv.swap_mul_self, (permMonoidHom d 2).map_one]
  rfl

/-- Calculate trace values for id. -/
lemma trace_k2_id : LinearMap.trace ℂ (TensV d 2) (LinearMap.id : Module.End ℂ (TensV d 2)) = (d : ℂ)^2 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d 2)]
  have hid : LinearMap.toMatrix (tensorBasis d 2) (tensorBasis d 2) LinearMap.id = 1 := by
    exact LinearMap.toMatrix_id (tensorBasis d 2)
  rw [hid, Matrix.trace_one]
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rfl

/-- Calculate trace values for SWAP. -/
lemma trace_k2_swap : LinearMap.trace ℂ (TensV d 2) (𝔽 d) = d := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d 2)]
  have hF : LinearMap.toMatrix (tensorBasis d 2) (tensorBasis d 2) (𝔽 d) = toEndMatrix d 2 ((permAction d (Equiv.swap 0 1)).toLinearMap) := rfl
  rw [hF]
  have htrace : Matrix.trace (toEndMatrix d 2 ((permAction d (Equiv.swap 0 1)).toLinearMap)) = ∑ I : Fin 2 → Fin d, toEndMatrix d 2 ((permAction d (Equiv.swap 0 1)).toLinearMap) I I := rfl
  rw [htrace]
  simp_rw [toEndMatrix_permAction]
  have hsum : (∑ I : Fin 2 → Fin d, if I = I ∘ (Equiv.swap (0 : Fin 2) (1 : Fin 2)).symm then (1 : ℂ) else 0) = d := by
    change (∑ I : Fin 2 → Fin d, if I = I ∘ Equiv.swap 0 1 then (1 : ℂ) else 0) = d
    have h_eq : ∀ I : Fin 2 → Fin d, (I = I ∘ Equiv.swap 0 1) ↔ I 0 = I 1 := by
      intro I
      constructor
      · intro h
        have h0 : I 0 = (I ∘ Equiv.swap 0 1) 0 := by rw [← h]
        simp only [Function.comp_apply, Equiv.swap_apply_left] at h0
        exact h0
      · intro h
        funext x
        fin_cases x <;> simp [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, h]
    simp_rw [h_eq]
    have h_bij : (∑ I : Fin 2 → Fin d, if I 0 = I 1 then (1 : ℂ) else 0) = ∑ a : Fin d, ∑ b : Fin d, if a = b then (1 : ℂ) else 0 := by
      have h_prod : (∑ I : Fin 2 → Fin d, if I 0 = I 1 then (1 : ℂ) else 0) = ∑ p : Fin d × Fin d, if p.1 = p.2 then (1 : ℂ) else 0 :=
        (Fintype.sum_equiv (finTwoArrowEquiv (Fin d)).symm (fun p => if p.1 = p.2 then (1 : ℂ) else 0) (fun I => if I 0 = I 1 then (1 : ℂ) else 0) (fun p => rfl)).symm
      rw [h_prod, Fintype.sum_prod_type]
    rw [h_bij]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.card_univ, Fintype.card_fin]
  exact hsum

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

  -- I couldn't quite figure out how to set up manual setting up of the linear system of equations.
  -- To be fully transparent, I relied heavily on LLMs to walk me through the process here.
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
