/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.Haar
import LeanHaar.ForMathlib.DCT

/-!
# Elementary identities on the tensor power `(ℂ^d)^{⊗k}`

The permutation operators `SchurWeyl.permOp` and their adjoints `SchurWeyl.permDual` form a
representation of the symmetric group. The moment computations for `k = 1, 2, 4` each need the
same consequences of that fact, together with the trace of the identity operator; they are
therefore proved here once, for every `k`.

## Main results

* `SchurWeyl.permOp_one`, `SchurWeyl.permDual_one`: the operators attached to the identity
  permutation are the identity map.
* `SchurWeyl.permOp_mul`: `V_d(σ π) = V_d(σ) V_d(π)`.
* `SchurWeyl.permDual_comp_permOp`: `V_d^†(σ) V_d(π) = V_d(σ⁻¹ π)`.
* `SchurWeyl.trace_id_tensV`: `Tr(id) = d^k` on `(ℂ^d)^{⊗k}`.
-/

noncomputable section

namespace SchurWeyl

variable (d : ℕ) {k : ℕ}

/-- The permutation operator is the value of the monoid homomorphism `permMonoidHom`. -/
theorem permOp_eq_permMonoidHom (σ : Equiv.Perm (Fin k)) :
    permOp d σ = permMonoidHom d k σ := rfl

/-- The permutation operator attached to the identity permutation is the identity map. -/
theorem permOp_one (k : ℕ) : permOp d (1 : Equiv.Perm (Fin k)) = LinearMap.id := by
  rw [permOp_eq_permMonoidHom, map_one]; rfl

/-- The dual permutation operator attached to the identity permutation is the identity map. -/
theorem permDual_one (k : ℕ) : permDual d (1 : Equiv.Perm (Fin k)) = LinearMap.id := by
  rw [permDual, ← permOp, inv_one, permOp_one]

/-- The permutation operators form a representation: `V_d(σ π) = V_d(σ) V_d(π)`. -/
theorem permOp_mul (σ π : Equiv.Perm (Fin k)) :
    permOp d (σ * π) = permOp d σ ∘ₗ permOp d π := by
  rw [permOp_eq_permMonoidHom, permOp_eq_permMonoidHom, permOp_eq_permMonoidHom, map_mul]; rfl

/-- `V_d^†(σ) V_d(π) = V_d(σ⁻¹ π)`: the permutation operators form a representation. -/
theorem permDual_comp_permOp (σ π : Equiv.Perm (Fin k)) :
    permDual d σ ∘ₗ permOp d π = permOp d (σ⁻¹ * π) := by
  rw [permOp_mul, permDual, ← permOp]

/-- The trace of the identity of `(ℂ^d)^{⊗k}` is the dimension `d^k` of that space. -/
theorem trace_id_tensV (d k : ℕ) :
    LinearMap.trace ℂ (TensV d k) LinearMap.id = (d : ℂ) ^ k := by
  rw [LinearMap.trace_id, Module.finrank_eq_card_basis (tensorBasis d k)]
  simp

end SchurWeyl

end
