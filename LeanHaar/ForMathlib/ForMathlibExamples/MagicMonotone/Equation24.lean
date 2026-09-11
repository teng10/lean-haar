/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.MagicMonotone.BrickworkLayers

/-!
# Equation (24) of `magic_monotones.pdf`: the two-layer moment operator in kernel form

The two-layer ensemble of Section III C of `magic_monotones.pdf` applies independent Haar
gates on the qubit pairs `(1,2)`, `(3,4)` and then on `(2,3)`, `(4,1)`. Its moment operator is
therefore the composition of the two layer moment operators (Eq. (19) of the source),
`MagicMonotone.twoLayerMoment = layerA ∘ layerB`.

Composing the two layers contracts the bra of layer `A` against the ket of layer `B`
(Eq. (22)):
```
  M = ∑_{σ₁,σ₂,π₁,π₂} ∑_{γ₁,γ₂,τ₁,τ₂}
        Wg(σ₁⁻¹π₁,4) Wg(σ₂⁻¹π₂,4) · Wg(γ₁⁻¹τ₁,4) Wg(γ₂⁻¹τ₂,4)
        · ⟨⟨V^{(12)}(π₁)V^{(34)}(π₂)|V^{(23)}(γ₁)V^{(41)}(γ₂)⟩⟩
        · |V^{(12)}(σ₁)⟩⟩|V^{(34)}(σ₂)⟩⟩⟨⟨V^{(23)}(τ₁)|⟨⟨V^{(41)}(τ₂)| .
```
Summing the inner labels `π₁, π₂, γ₁, γ₂` first turns this into **Eq. (24)**,
```
  M = ∑_{σ₁,σ₂} ∑_{τ₁,τ₂} K_{(σ₁,σ₂),(τ₁,τ₂)}
        |V^{(12)}(σ₁)⟩⟩|V^{(34)}(σ₂)⟩⟩⟨⟨V^{(23)}(τ₁)|⟨⟨V^{(41)}(τ₂)| ,
```
with the two-layer kernel `K` of Eq. (25).

## Main definitions

* `MagicMonotone.twoLayerMoment`: the two-layer moment operator `layerA ∘ layerB`, Eq. (19).
* `MagicMonotone.twoLayerKernel`: the two-layer kernel `K_{(σ₁,σ₂),(τ₁,τ₂)}`, Eq. (25).

## Main results

* `MagicMonotone.twoLayerMoment_eq_contraction`: Eq. (22), the contraction of the two layers.
* `MagicMonotone.twoLayerMoment_eq_kernel_sum`: **Eq. (24)**, the same operator written as a
  sum over the outer labels only, weighted by the kernel of Eq. (25).

## Proof outline

Both statements are instances of the ket-bra calculus of `RankOneCalculus.lean`, applied to
the two layers written as double sums over *pairs* of permutations
(`layerA_eq_pairSum`, `layerB_eq_pairSum`):

* `sumRankOne_comp_sumRankOne` performs the contraction `⟨⟨·| · |·⟩⟩` and gives Eq. (22);
* `sumRankOne_comp_sumRankOne_kernel` performs the same contraction but sums the inner
  labels first, which is exactly Eqs. (24)–(25).

In both cases the only remaining step is to split each sum over a pair of permutations into
two sums over permutations (`Fintype.sum_prod_type`) and to identify the inner product of two
vectorized permutation operators with their Hilbert–Schmidt overlap (`inner_vecOp_vecOp`).
-/

noncomputable section

open scoped InnerProductSpace Matrix
open InnerProductSpace ContinuousLinearMap

namespace MagicMonotone

/-- **The two-layer moment operator**, Eq. (19) of `magic_monotones.pdf`: since all four gates
are drawn independently, the moment operator of the two-layer ensemble is the composition of
the two layer moment operators. -/
def twoLayerMoment : Vecs →L[ℂ] Vecs := layerA ∘L layerB

/-- **The two-layer kernel**, Eq. (25) of `magic_monotones.pdf`:
`K_{(σ₁,σ₂),(τ₁,τ₂)} = ∑_{π₁,π₂,γ₁,γ₂} Wg(σ₁⁻¹π₁,4) Wg(σ₂⁻¹π₂,4) · Wg(γ₁⁻¹τ₁,4) Wg(γ₂⁻¹τ₂,4)
· ⟨⟨V^{(12)}(π₁)V^{(34)}(π₂)|V^{(23)}(γ₁)V^{(41)}(γ₂)⟩⟩`.

It carries a Weingarten factor on both sides, one for each layer. -/
def twoLayerKernel (σ₁ σ₂ τ₁ τ₂ : Equiv.Perm Copies) : ℂ :=
  ∑ π₁, ∑ π₂, ∑ γ₁, ∑ γ₂,
    (wg (σ₁⁻¹ * π₁) * wg (σ₂⁻¹ * π₂)) * (wg (γ₁⁻¹ * τ₁) * wg (γ₂⁻¹ * τ₂)) *
      hsOverlap (V12 π₁ * V34 π₂) (V23 γ₁ * V41 γ₂)

/-- **Equation (22) of `magic_monotones.pdf`: contracting the two layers.** Composing the two
layer moment operators contracts the bra of layer `A` with the ket of layer `B`, leaving the
Hilbert–Schmidt overlap `⟨⟨V^{(12)}(π₁)V^{(34)}(π₂)|V^{(23)}(γ₁)V^{(41)}(γ₂)⟩⟩` as an interlayer
mixing factor. -/
theorem twoLayerMoment_eq_contraction :
    twoLayerMoment =
      ∑ σ₁, ∑ σ₂, ∑ π₁, ∑ π₂, ∑ γ₁, ∑ γ₂, ∑ τ₁, ∑ τ₂,
        ((wg (σ₁⁻¹ * π₁) * wg (σ₂⁻¹ * π₂)) * (wg (γ₁⁻¹ * τ₁) * wg (γ₂⁻¹ * τ₂)) *
            hsOverlap (V12 π₁ * V34 π₂) (V23 γ₁ * V41 γ₂)) •
          rankOne ℂ (layerAKet σ₁ σ₂) (layerBKet τ₁ τ₂) := by
  rw [twoLayerMoment, layerA_eq_pairSum, layerB_eq_pairSum,
    sumRankOne_comp_sumRankOne ketA ketA wgPair ketB ketB wgPair]
  simp only [Fintype.sum_prod_type, wgPair, ketA, ketB, inner_layerAKet_layerBKet]

/-- **Equation (24) of `magic_monotones.pdf`.** Summing the inner labels `π₁, π₂, γ₁, γ₂`
first, the two-layer moment operator is a sum over the outer labels only, with the two-layer
kernel `K` of Eq. (25) as coefficient:
`M = ∑_{σ₁,σ₂} ∑_{τ₁,τ₂} K_{(σ₁,σ₂),(τ₁,τ₂)}
      |V^{(12)}(σ₁)⟩⟩|V^{(34)}(σ₂)⟩⟩⟨⟨V^{(23)}(τ₁)|⟨⟨V^{(41)}(τ₂)|`. -/
theorem twoLayerMoment_eq_kernel_sum :
    twoLayerMoment =
      ∑ σ₁, ∑ σ₂, ∑ τ₁, ∑ τ₂,
        twoLayerKernel σ₁ σ₂ τ₁ τ₂ • rankOne ℂ (layerAKet σ₁ σ₂) (layerBKet τ₁ τ₂) := by
  rw [twoLayerMoment, layerA_eq_pairSum, layerB_eq_pairSum,
    sumRankOne_comp_sumRankOne_kernel ketA ketA wgPair ketB ketB wgPair]
  simp only [Fintype.sum_prod_type, twoLayerKernel, wgPair, ketA, ketB,
    inner_layerAKet_layerBKet]

end MagicMonotone

end
