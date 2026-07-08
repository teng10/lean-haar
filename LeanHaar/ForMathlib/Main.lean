/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

import LeanHaar.ForMathlib.Defs
import LeanHaar.ForMathlib.Commutation
import LeanHaar.ForMathlib.DirectProof

/-!
# Schur-Weyl Duality

This file proves the Schur-Weyl duality theorem: the centralizer of the diagonal
action of `End(V)` on `V^{⊗k}` equals the linear span of the permutation operators.

The hard direction is proved uniformly in `d` and `k` via the Double Commutant
Theorem (see `DirectProof.lean` and `SmallDim.lean`); there is no separate case
analysis on whether `k ≤ d`.

## Main results

* `SchurWeyl.schur_weyl` - The Schur-Weyl duality theorem

## References

* [J. Watrous, *The Theory of Quantum Information*][watrous2018]
-/

noncomputable section

open scoped TensorProduct

namespace SchurWeyl

variable {d k : ℕ}

/-! ### Easy direction -/

/-- The linear span of `permImage` is contained in the centralizer of `diagImage`
(easy direction of Schur-Weyl). -/
theorem span_permImage_le_centralizer_diagImage :
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) ⊆
    (diagImage d k).centralizer := by
  have hc : permImage d k ⊆ ↑(Subalgebra.centralizer ℂ (diagImage d k)).toSubmodule := by
    intro x hx
    simp only [Subalgebra.mem_toSubmodule, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    exact permImage_subset_centralizer_diagImage hx
  intro x hx
  have hx' := Submodule.span_le.mpr hc hx
  simp only [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hx'
  exact hx'

/-! ### Main theorem -/

/-- **Schur-Weyl Duality**.
The centralizer of `{g^{⊗k} | g ∈ End(V)}` in `End(V^{⊗k})` equals `Span{W_σ | σ ∈ S_k}`,
for all dimensions `d` and tensor powers `k`. -/
theorem schur_weyl :
    (diagImage d k).centralizer =
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) :=
  Set.Subset.antisymm centralizer_diagImage_le_span_permImage
    span_permImage_le_centralizer_diagImage

end SchurWeyl

end
