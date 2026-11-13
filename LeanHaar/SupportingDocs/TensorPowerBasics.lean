/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Weingarten
import LeanHaar.TensorPower.Matrix

/-!
# Elementary identities on the tensor power `(ℂ^d)^{⊗k}`

The permutation operators `SchurWeyl.permOp` are the underlying linear maps of
`SchurWeyl.permAction`, and `SchurWeyl.permDual` uses inverse permutations. The
moment computations for `k = 1, 2, 4` share these identities and the trace of the
identity operator. They are proved here for every `k`, independently of Haar
integration and any particular moment formula. The computational matrix identities and
vectorization lemmas relate these operators to matrix multiplication and the Hilbert–Schmidt
inner product.

## Main results

* `SchurWeyl.permOp_one`, `SchurWeyl.permDual_one`: the operators attached to the identity
  permutation are the identity map.
* `SchurWeyl.permOp_mul`: `V_d(σ π) = V_d(σ) V_d(π)`.
* `SchurWeyl.permDual_comp_permOp`: `V_d^†(σ) V_d(π) = V_d(σ⁻¹ π)`.
* `SchurWeyl.trace_id_tensV`: `Tr(id) = d^k` on `(ℂ^d)^{⊗k}`.
* `SchurWeyl.endVec_apply`, `SchurWeyl.inner_endVec_endVec`: vectorization and its inner product.
* `SchurWeyl.toEndMatrix_one`, `SchurWeyl.toEndMatrix_mul`: matrix coordinates preserve identity
  and composition.
-/

noncomputable section

namespace SchurWeyl

/-! ### Permutation operators -/

section Permutations

variable (d : ℕ) {k : ℕ}

/-- The permutation operator attached to the identity permutation is the identity map. -/
theorem permOp_one (k : ℕ) : permOp d (1 : Equiv.Perm (Fin k)) = LinearMap.id := by
  exact congrArg (fun e : TensV d k ≃ₗ[ℂ] TensV d k => e.toLinearMap)
    (map_one (permAction d k))

/-- The dual permutation operator attached to the identity permutation is the identity map. -/
theorem permDual_one (k : ℕ) : permDual d (1 : Equiv.Perm (Fin k)) = LinearMap.id := by
  rw [permDual, inv_one]
  exact permOp_one d k

/-- The permutation operators form a representation: `V_d(σ π) = V_d(σ) V_d(π)`. -/
theorem permOp_mul (σ π : Equiv.Perm (Fin k)) :
    permOp d (σ * π) = permOp d σ ∘ₗ permOp d π := by
  exact congrArg (fun e : TensV d k ≃ₗ[ℂ] TensV d k => e.toLinearMap)
    (map_mul (permAction d k) σ π)

/-- `V_d^†(σ) V_d(π) = V_d(σ⁻¹ π)`: the permutation operators form a representation. -/
theorem permDual_comp_permOp (σ π : Equiv.Perm (Fin k)) :
    permDual d σ ∘ₗ permOp d π = permOp d (σ⁻¹ * π) := by
  rw [permDual, permOp_mul]

/-- The trace of the identity of `(ℂ^d)^{⊗k}` is the dimension `d^k` of that space. -/
theorem trace_id_tensV (d k : ℕ) :
    LinearMap.trace ℂ (TensV d k) LinearMap.id = (d : ℂ) ^ k := by
  rw [LinearMap.trace_id, Module.finrank_eq_card_basis (tensorBasis d k)]
  simp

end Permutations

open scoped InnerProductSpace Matrix

/-! ### Vectorization of operators

The vectorization `|A⟩⟩` is the repository's `SchurWeyl.endVec`; nothing new is defined. The
computation rule reads its matrix entries, and its Euclidean inner product is the
Hilbert–Schmidt one. -/

/-- Vectorization reads the operator's matrix in row-column order. -/
lemma endVec_apply {d k : ℕ} (O : Module.End ℂ (TensV d k))
    (p : (Fin k → Fin d) × (Fin k → Fin d)) :
    endVec O p = toEndMatrix d k O p.1 p.2 := rfl

/-- The vectorized inner product is the Hilbert–Schmidt inner product,
`⟨⟨A|B⟩⟩ = Tr(A† B)`, where `|·⟩⟩` is the repository's vectorization
`SchurWeyl.endVec` and `A†` is the conjugate transpose of the matrix of `A` in the
computational basis.

This extends the repository's trace bridge `SchurWeyl.inner_endVec_perm_eq_trace`, which is
the special case where the first argument is a permutation operator, to an arbitrary pair of
operators. -/
lemma inner_endVec_endVec {d k : ℕ} (X Y : Module.End ℂ (TensV d k)) :
    (inner ℂ (endVec X) (endVec Y) : ℂ)
      = ((toEndMatrix d k X)ᴴ * toEndMatrix d k Y).trace := by
  set A := toEndMatrix d k X with hA
  set B := toEndMatrix d k Y with hB
  -- The inner product of the two lists of matrix entries, ...
  have hlhs : (inner ℂ (endVec X) (endVec Y) : ℂ)
      = ∑ i, ∑ j, (starRingEnd ℂ) (A i j) * B i j := by
    simp only [endVec, hA, hB, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  -- ... and the trace of `A† B`, are the same double sum.
  have hrhs : (Aᴴ * B).trace = ∑ i, ∑ j, (starRingEnd ℂ) (A j i) * B j i := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diag, Matrix.conjTranspose_apply]
  rw [hlhs, hrhs, Finset.sum_comm]

/-! ### The matrix of an operator

Operators are described below by their matrices in the computational basis, through the
repository's `SchurWeyl.toEndMatrix`. Two compatibility lemmas are all that is needed. -/

/-- The matrix of the identity operator is the identity matrix. -/
lemma toEndMatrix_one {d k : ℕ} : toEndMatrix d k 1 = 1 :=
  LinearMap.toMatrix_one (tensorBasis d k)

/-- The matrix of a composition of operators is the product of their matrices. -/
lemma toEndMatrix_mul {d k : ℕ} (X Y : Module.End ℂ (TensV d k)) :
    toEndMatrix d k (X * Y) = toEndMatrix d k X * toEndMatrix d k Y :=
  LinearMap.toMatrix_mul (tensorBasis d k) X Y

end SchurWeyl

end
