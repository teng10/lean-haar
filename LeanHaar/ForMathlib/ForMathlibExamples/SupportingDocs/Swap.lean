/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TensorPowerBasics

/-!
# The swap operator on two tensor factors

The operator `𝔽 d` exchanges the two factors of `(ℂ^d)^{⊗2}`. This file provides
its permutation and adjoint identities, its matrix entries, and the traces of
swap and identity. The second moment, tensor trace formulas, quantum machine
learning example, and classical shadows use this same operator.

These elementary identities do not depend on Haar integration or moment formulas.
-/

open SchurWeyl

variable {d : ℕ}

/-- The swap operator `𝔽 d` on the tensor space `TensV d 2` representing the transposition `(0 1)`. -/
noncomputable def 𝔽 (d : ℕ) : Module.End ℂ (TensV d 2) := permOp d (Equiv.swap (0 : Fin 2) (1 : Fin 2))

/-- S_2 is composed of elements {id, SWAP}-/
lemma sum_perm_k2_eq_set_id_swap : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {Equiv.refl (Fin 2), Equiv.swap (0 : Fin 2) (1 : Fin 2)} := by
  decide

/-- The reflective permutation operator is the identity linear map. -/
lemma permOp_k2_id : permOp d (Equiv.refl (Fin 2)) = LinearMap.id :=
  SchurWeyl.permOp_one d 2

/-- The SWAP permutation operator is the SWAP linear map (as defined above).-/
lemma permOp_k2_swap : permOp d (Equiv.swap 0 1) = 𝔽 d := by
  rfl

/-- The conjugate transpose of the identity is itself.-/
lemma permDual_k2_id : permDual d (Equiv.refl (Fin 2)) = LinearMap.id :=
  SchurWeyl.permDual_one d 2

/-- The conjugate transpose of the SWAP operator is itself.-/
lemma permDual_k2_swap : permDual d (Equiv.swap 0 1) = 𝔽 d := by
  unfold permDual
  rw [Equiv.swap_inv]
  exact permOp_k2_swap

/-- SWAP composed with SWAP is the identity.-/
lemma swap_swap : 𝔽 d ∘ₗ 𝔽 d = LinearMap.id := by
  unfold 𝔽
  rw [← SchurWeyl.permOp_mul, Equiv.swap_mul_self, SchurWeyl.permOp_one]

/-- Calculate trace values for id. -/
lemma trace_k2_id : LinearMap.trace ℂ (TensV d 2)
    (LinearMap.id : Module.End ℂ (TensV d 2)) = (d : ℂ)^2 :=
  SchurWeyl.trace_id_tensV d 2

/-- Calculate trace values for SWAP. -/
lemma trace_k2_swap : LinearMap.trace ℂ (TensV d 2) (𝔽 d) = d := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d 2)]
  have hF : LinearMap.toMatrix (tensorBasis d 2) (tensorBasis d 2) (𝔽 d) = toEndMatrix d 2 ((permAction d 2 (Equiv.swap 0 1)).toLinearMap) := rfl
  rw [hF]
  have htrace : Matrix.trace (toEndMatrix d 2 ((permAction d 2 (Equiv.swap 0 1)).toLinearMap)) = ∑ I : Fin 2 → Fin d, toEndMatrix d 2 ((permAction d 2 (Equiv.swap 0 1)).toLinearMap) I I := rfl
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

namespace SchurWeyl

/-- Matrix entries of the swap operator `𝔽 d` on `TensV d 2`. -/
theorem toEndMatrix_swap (I J : Fin 2 → Fin d) :
    toEndMatrix d 2 (𝔽 d) I J = if I = J ∘ (Equiv.swap 0 1) then 1 else 0 := by
  have h : toEndMatrix d 2 (𝔽 d) I J
      = toEndMatrix d 2 ((permAction d 2 (Equiv.swap (0 : Fin 2) 1)).toLinearMap) I J := rfl
  rw [h, toEndMatrix_permAction]
  simp

end SchurWeyl
