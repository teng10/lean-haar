import LeanHaar.ForMathlib.Haar
import LeanHaar.ForMathlib.Defs

import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Example: Computing moments for k = 1

We seek to use Antonio's notes to write an expression for the first order moment of the Haar measure.
-/

open SchurWeyl

variable (d : ℕ)

/-- `Equiv.Perm (Fin 1)` is a subsingleton, so a sum over it is just its value at `1`. -/
lemma sum_perm_k1 {M : Type*} [AddCommMonoid M] (f : Equiv.Perm (Fin 1) → M) :
    ∑ π, f π = f 1 :=
  Fintype.sum_subsingleton f 1

/-- Tr(Id) = d. The trace of the identity on `V^{⊗ 1} = ℂ^d` is `d`-/
lemma trace_id_k1 : LinearMap.trace ℂ (TensV d 1) LinearMap.id = d := by
  -- trace of the identity is the dimension of the space
  rw [LinearMap.trace_id, Module.finrank_eq_card_basis (tensorBasis d 1)]
  -- `Fintype.card (Fin 1 → Fin d) = d ^ 1 = d`
  simp

/-- The permutation operator attached to the identity permutation is the identity map. -/
lemma permOp_one (k : ℕ) : permOp d (1 : Equiv.Perm (Fin k)) = LinearMap.id := by
  -- `1 = Equiv.refl`, and reindexing along `Equiv.refl` is the identity
  simp [permOp, permAction, Equiv.Perm.one_def, PiTensorProduct.reindex_refl]

/-- The dual permutation operator attached to the identity permutation is the identity map. -/
lemma permDual_one (k : ℕ) : permDual d (1 : Equiv.Perm (Fin k)) = LinearMap.id := by
  rw [permDual, ← permOp, inv_one, permOp_one]

/-- The moment of a single operator O for tensor power k = 1 is Tr(O) / d • Id.-/
theorem k1_moment [NeZero d] (O : Module.End ℂ (TensV d 1)) :
    momentOp O = (LinearMap.trace ℂ (TensV d 1) O / (d : ℂ)) • LinearMap.id := by
  obtain ⟨c, hmoment, hperm⟩ := weingarten_moment_haar O
  specialize hperm 1
  -- Both sums collapse to their `π = 1` term, where `permOp d 1 = permDual d 1 = id`:
  -- `hmoment : momentOp O = c 1 • id` and `hperm : Tr O = c 1 * Tr id = c 1 * d`.
  simp only [sum_perm_k1, permDual_one, permOp_one, LinearMap.id_comp, trace_id_k1]
    at hmoment hperm
  -- `NeZero d` gives `(d : ℂ) ≠ 0`, so `c 1 * d / d = c 1`.
  rw [hmoment, hperm, mul_div_cancel_right₀ (c 1) (NeZero.natCast_ne d ℂ)]
