/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic

import LeanHaar.ForMathlib.TensorV2
import LeanHaar.ForMathlib.Commutation
import LeanHaar.ForMathlib.DirectProof
import LeanHaar.ForMathlib.SmallDim

/-!
# Schur-Weyl Duality

This file proves the Schur-Weyl duality theorem: the centralizer of the diagonal
action of `End(V)` on `V^{⊗k}` equals the linear span of the permutation operators.

This file acts as the top-level assembly for the duality, combining the cases
where `k ≤ d` (proven in `DirectProof.lean`) and `d < k` (proven in `SmallDim.lean`).

## Main results

* `SchurWeyl.schur_weyl` - The Schur-Weyl duality theorem
* `SchurWeyl.schur_weyl_of_le` - The theorem for `k ≤ d`

## References

* [J. Watrous, *The Theory of Quantum Information*][watrous2018]
-/

noncomputable section

open scoped TensorProduct

namespace ForMathlib.Tensor

open SchurWeyl

-- namespace SchurWeyl

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

/-! ### Hard direction case assembly -/

/-- **Hard direction of Schur-Weyl**: centralizer(diagImage) ⊆ Span(permImage).
This combines the diagonal constraint and coefficient constancy (for `k ≤ d`) and
the Double Commutant Theorem/First Fundamental Theorem (for `d < k`) to show every
operator commuting with all `g^{⊗k}` is a linear combination of `W_σ`. -/
theorem centralizer_diagImage_le_span_permImage :
    (diagImage d k).centralizer ⊆
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) := by
  by_cases hdk : k ≤ d
  · exact centralizer_diagImage_le_span_permImage_of_le hdk
  · exact centralizer_diagImage_le_span_permImage_small

/-! ### Main theorems -/

/-- **Schur-Weyl Duality** (for `k ≤ d`).
The centralizer of `{g^{⊗k} | g ∈ End(V)}` in `End(V^{⊗k})` equals `Span{W_σ | σ ∈ S_k}`. -/
theorem schur_weyl_of_le (hdk : k ≤ d) :
    (diagImage d k).centralizer =
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) :=
  Set.Subset.antisymm (centralizer_diagImage_le_span_permImage_of_le hdk)
    span_permImage_le_centralizer_diagImage

/-- **Schur-Weyl Duality** (general case).
The centralizer of `{g^{⊗k} | g ∈ End(V)}` in `End(V^{⊗k})` equals `Span{W_σ | σ ∈ S_k}`. -/
theorem schur_weyl :
    (diagImage d k).centralizer =
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) :=
  Set.Subset.antisymm centralizer_diagImage_le_span_permImage
    span_permImage_le_centralizer_diagImage

-- end SchurWeyl

end ForMathlib.Tensor
