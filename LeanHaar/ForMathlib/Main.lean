/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

import LeanHaar.ForMathlib.TensorPower
import LeanHaar.ForMathlib.Commutation
import LeanHaar.ForMathlib.DCT
import LeanHaar.ForMathlib.PermutationCentralizer

/-!
# Schur-Weyl Duality

This file proves the Schur-Weyl duality theorem: the centralizer of the diagonal
action of `End(V)` on `V^{⊗k}` equals the linear span of the permutation operators.

The proof is uniform in `d` and `k`. `PermutationCentralizer` proves the polynomial
span description of the permutation centralizer, and `DCT` proves the permutation
algebra double-centralizer theorem. This file combines them for the hard inclusion
and uses commutation for the reverse inclusion.

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

/-! ### Hard direction -/

/-- The hard direction of Schur–Weyl duality, for every `d` and `k`.
The polynomial description of the permutation centralizer places an operator
commuting with `diagImage` in the double centralizer of the permutation span;
the double-centralizer theorem then places it in the permutation span itself. -/
theorem centralizer_diagImage_le_span_permImage :
    (diagImage d k).centralizer ⊆
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) := by
  intro X hX
  have hX_in_A'' : X ∈ ((↑(Submodule.span ℂ (permImage d k)) : Set _).centralizer).centralizer := by
    intro Y hY
    have hY' : Y ∈ (permImage d k).centralizer := by
      intro z hz; exact hY z (Submodule.subset_span hz)
    have hY_diag := centralizer_permImage_le_span_diagImage hY'
    revert hY_diag
    apply Submodule.span_induction
    · intro y hy; obtain ⟨g, rfl⟩ := hy; exact hX _ ⟨g, rfl⟩
    · simp
    · intro a b _ _ ha hb; simp [mul_add, add_mul, ha, hb]
    · intro c a _ ha; simp [ha]
  exact double_centralizer_permImage hX_in_A''

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
