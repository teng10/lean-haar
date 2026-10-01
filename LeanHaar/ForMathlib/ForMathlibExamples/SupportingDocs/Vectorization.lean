/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.Weingarten

/-!
# Vectorization and computational matrix coordinates

These application-level lemmas relate the core vectorization `SchurWeyl.endVec` to the
Hilbert–Schmidt inner product and record the identity and composition laws for the core
coordinate equivalence `SchurWeyl.toEndMatrix`. No vectorization or basis is redefined.
-/

noncomputable section

open scoped InnerProductSpace Matrix

namespace SchurWeyl

/-! ### Vectorization of operators

The vectorization `|A⟩⟩` is the repository's `SchurWeyl.endVec`; nothing new is defined. The
only fact needed about it is that it turns the Euclidean inner product into the
Hilbert–Schmidt one. -/

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
