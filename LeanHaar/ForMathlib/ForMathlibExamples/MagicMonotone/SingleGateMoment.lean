/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.MagicMonotone.RankOneCalculus
import LeanHaar.ForMathlib.ForMathlibExamples.k4Moment

/-!
# The single-gate moment operator in vectorized (ket-bra) form

This file connects the vectorized calculus of `magic_monotones.pdf` to the Haar moment
operator that the repository actually constructs and computes:

* `SchurWeyl.momentOp X = 𝔼_{U∼μ_H}[U^{⊗k} X U^{†⊗k}]` (`LeanHaar/ForMathlib/Haar.lean`), the
  genuine Haar average over the unitary group; and
* `SchurWeyl.K4.k4_moment` (`LeanHaar/ForMathlib/ForMathlibExamples/k4Moment.lean`), which
  evaluates it for `k = 4` copies as a Weingarten combination of permutation operators.

A two-qubit gate is the case `d = 4`, and a fourth moment is the case `k = 4`, so the
two-qubit single-gate moment operator of Section III A of the source is exactly
`SchurWeyl.momentOp` with those parameters.

## Main definitions

* `MagicMonotone.vecMomentOp d`: the vectorized single-gate moment operator
  `∑_{σ,π} Wg(σ⁻¹π, d) |V_d(σ)⟩⟩⟨⟨V_d(π)|` of Eq. (17), built from the repository's
  permutation operators `SchurWeyl.permOp`, their vectorizations `SchurWeyl.endVec` and the
  Weingarten values `SchurWeyl.K4.wgVal`.

## Main results

* `MagicMonotone.momentOp_eq_weingarten_sum`: Eq. (14), the Haar moment operator of a
  `d`-dimensional gate acting on `k = 4` copies,
  `M(X) = ∑_{σ,π} Wg(σ⁻¹π, d) Tr(V_d(π)† X) V_d(σ)`. It is `SchurWeyl.K4.k4_moment` with the
  coefficient `SchurWeyl.K4.coeff` unfolded.
* `MagicMonotone.vecMomentOp_endVec`: **Eq. (17)**, `M|X⟩⟩ = |M(X)⟩⟩`: the ket-bra operator
  `vecMomentOp d` is the vectorization of the Haar moment operator. This is the identity that
  licenses all the vectorized manipulations of the source.
-/

noncomputable section

open scoped InnerProductSpace Matrix
open InnerProductSpace ContinuousLinearMap SchurWeyl SchurWeyl.K4

namespace MagicMonotone

variable {d : ℕ}

/-! ### Equation (14): the single-gate moment operator -/

/-- **Equation (14) of `magic_monotones.pdf`.** For `4 ≤ d`, the Haar moment operator of a
`d`-dimensional gate acting on `k = 4` copies is
`M(X) = ∑_{σ ∈ S₄} ∑_{π ∈ S₄} Wg(σ⁻¹π, d) · Tr(V_d(π)† X) · V_d(σ)`.

For `d = 4` this is the two-qubit gate of Section III A of the source. The statement is the
repository's `SchurWeyl.K4.k4_moment` with its coefficient
`c_σ(X) = ∑_π Wg(σ⁻¹π, d) Tr(V_d(π)† X)` written out; the Weingarten traces
`Tr(V_d(π)† X)` are the repository's `SchurWeyl.weingartenVec`. -/
theorem momentOp_eq_weingarten_sum (hd : 4 ≤ d) (X : Module.End ℂ (TensV d 4)) :
    momentOp X =
      ∑ σ : Equiv.Perm (Fin 4), ∑ π : Equiv.Perm (Fin 4),
        (wgVal (d : ℂ) (σ⁻¹ * π) * weingartenVec d 4 X π) • permOp d σ := by
  rw [k4_moment d hd X]
  exact Finset.sum_congr rfl fun σ _ => by rw [coeff, Finset.sum_smul]

/-! ### Equation (17): the vectorized form -/

/-- **The vectorized single-gate moment operator**, Eq. (17) of `magic_monotones.pdf`:
`M = ∑_{σ,π} Wg(σ⁻¹π, d) |V_d(σ)⟩⟩⟨⟨V_d(π)|`.

The kets `|V_d(σ)⟩⟩` are the vectorized permutation operators `SchurWeyl.endVec (permOp d σ)`
of the repository, and `|a⟩⟩⟨⟨b|` is Mathlib's rank-one operator. -/
def vecMomentOp (d : ℕ) :
    EuclideanSpace ℂ ((Fin 4 → Fin d) × (Fin 4 → Fin d)) →L[ℂ]
      EuclideanSpace ℂ ((Fin 4 → Fin d) × (Fin 4 → Fin d)) :=
  ∑ σ : Equiv.Perm (Fin 4), ∑ π : Equiv.Perm (Fin 4),
    wgVal (d : ℂ) (σ⁻¹ * π) • rankOne ℂ (endVec (permOp d σ)) (endVec (permOp d π))

/-- Applying the ket-bra operator to a vectorized operator: each bra `⟨⟨V_d(π)|` contracts
with `|X⟩⟩` into the Weingarten trace `Tr(V_d(π)† X)`, by the repository's trace bridge
`SchurWeyl.inner_endVec_perm_eq_trace`. -/
lemma vecMomentOp_apply (X : Module.End ℂ (TensV d 4)) :
    vecMomentOp d (endVec X) =
      ∑ σ : Equiv.Perm (Fin 4), ∑ π : Equiv.Perm (Fin 4),
        (wgVal (d : ℂ) (σ⁻¹ * π) * weingartenVec d 4 X π) • endVec (permOp d σ) := by
  simp only [vecMomentOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    rankOne_apply, smul_smul, inner_endVec_perm_eq_trace, weingartenVec]

/-- **Equation (17) of `magic_monotones.pdf`.** For `4 ≤ d`, the ket-bra operator
`M = ∑_{σ,π} Wg(σ⁻¹π, d) |V_d(σ)⟩⟩⟨⟨V_d(π)|` is the vectorization of the Haar moment
operator: `M|X⟩⟩ = |M(X)⟩⟩` for every operator `X`. -/
theorem vecMomentOp_endVec (hd : 4 ≤ d) (X : Module.End ℂ (TensV d 4)) :
    vecMomentOp d (endVec X) = endVec (momentOp X) := by
  -- Vectorization is linear, so it commutes with the Weingarten sum of Eq. (14).
  have hlin : endVec (momentOp X) =
      ∑ σ : Equiv.Perm (Fin 4), ∑ π : Equiv.Perm (Fin 4),
        (wgVal (d : ℂ) (σ⁻¹ * π) * weingartenVec d 4 X π) • endVec (permOp d σ) := by
    rw [← endVecₗ_apply, momentOp_eq_weingarten_sum hd X]
    simp only [map_sum, map_smul, endVecₗ_apply]
  rw [vecMomentOp_apply, hlin]

end MagicMonotone

end
