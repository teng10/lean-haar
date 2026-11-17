/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Applications.MagicMonotone.BrickworkLayers
import LeanHaar.Applications.MagicMonotone.RankOneCalculus

/-!
# Equation (24) of `magic_monotones.pdf`: the two-layer moment operator in kernel form

This file composes the explicit algebraic layer sums from `BrickworkLayers`, following
Section III C of `magic_monotones.pdf`. The source uses the Heisenberg picture: the physical
circuit applies layer A and then B, while observables evolve backwards. Accordingly,
`MagicMonotone.twoLayerMoment = layerA ∘ layerB` applies B first to its argument.

The results below prove contraction formulas for this defined composition.
`MagicMonotone.integral_twoLayer_endVec` identifies its action with the Heisenberg average
over four independent embedded Haar gates. That proof specializes the shared circuit layer
formula in `HaarLayers`, using the four-copy inverse-Gram identity
`SchurWeyl.K4.inv_weingartenGram_four`; the algebraic proofs here remain independent of
Haar integration.

Composing the two layers contracts the bra of layer `A` against the ket of layer `B`
(Eq. (22)):
```
  M = ∑_{σ₁,σ₂,π₁,π₂} ∑_{γ₁,γ₂,τ₁,τ₂}
        Wg(σ₁⁻¹π₁,4) Wg(σ₂⁻¹π₂,4) · Wg(γ₁⁻¹τ₁,4) Wg(γ₂⁻¹τ₂,4)
        · ⟨⟨V^{(12)}(π₁)V^{(34)}(π₂)|V^{(23)}(γ₁)V^{(41)}(γ₂)⟩⟩
        · |V^{(12)}(σ₁) V^{(34)}(σ₂)⟩⟩⟨⟨V^{(23)}(τ₁) V^{(41)}(τ₂)| .
```
Summing the inner labels `π₁, π₂, γ₁, γ₂` first turns this into **Eq. (24)**,
```
  M = ∑_{σ₁,σ₂} ∑_{τ₁,τ₂} K_{(σ₁,σ₂),(τ₁,τ₂)}
        |V^{(12)}(σ₁) V^{(34)}(σ₂)⟩⟩⟨⟨V^{(23)}(τ₁) V^{(41)}(τ₂)| ,
```
with the two-layer kernel `K` of Eq. (25). The interlayer overlaps inside `K` are products
of entries of the repository's Weingarten Gram matrix, so Eq. (23) turns `K` into an explicit sum of
Weingarten values times powers of two (`MagicMonotone.twoLayerKernel_eq_two_pow_sum`).

## Main definitions

* `MagicMonotone.twoLayerMoment`: the defined composition `layerA ∘ layerB`, Eq. (19).
* `MagicMonotone.twoLayerKernel`: the two-layer kernel `K_{(σ₁,σ₂),(τ₁,τ₂)}`, Eq. (25).

## Main results

* `MagicMonotone.twoLayerMoment_eq_contraction`: Eq. (22), the contraction of the two layers.
* `MagicMonotone.twoLayerMoment_eq_kernel_sum`: **Eq. (24)**, the same operator written as a
  sum over the outer labels only, weighted by the kernel of Eq. (25).
* `MagicMonotone.twoLayerKernel_eq_two_pow_sum`: the kernel of Eq. (25) with its interlayer
  overlaps evaluated by Eq. (23), leaving only Weingarten values and powers of two.

## Proof outline

Both statements use the local ket-bra calculus of `Applications/MagicMonotone/RankOneCalculus.lean`, applied
to the two layers written as double sums over *pairs* of permutations
(`layerA_eq_pairSum`, `layerB_eq_pairSum`):

* `InnerProductSpace.sumRankOne_comp_sumRankOne` performs the contraction `⟨⟨·| · |·⟩⟩`
  and gives Eq. (22);
* `InnerProductSpace.sumRankOne_comp_sumRankOne_kernel` performs the same contraction but
  sums the inner labels first, which is exactly Eqs. (24)–(25).

In both cases the only remaining step is to split each sum over a pair of permutations into
two sums over permutations (`Fintype.sum_prod_type`) and to identify the inner product of two
vectorized permutation operators (`SchurWeyl.endVec`) with their Hilbert–Schmidt overlap
(`MagicMonotone.hsOverlap`, i.e. `SchurWeyl.inner_endVec_endVec`).
-/

noncomputable section

open scoped InnerProductSpace Matrix
open InnerProductSpace ContinuousLinearMap SchurWeyl SchurWeyl.K4

namespace MagicMonotone

/-- **The composition of the algebraic layer sums**, Eq. (19) of `magic_monotones.pdf`.
It applies B first to its argument, following the source's Heisenberg convention for a
physical circuit applying A then B. `MagicMonotone.integral_twoLayer_endVec` identifies
its action with the independent-gate Haar average. -/
def twoLayerMoment : Vecs →L[ℂ] Vecs := layerA ∘L layerB

/-- **The two-layer kernel**, Eq. (25) of `magic_monotones.pdf`:
`K_{(σ₁,σ₂),(τ₁,τ₂)} = ∑_{π₁,π₂,γ₁,γ₂} Wg(σ₁⁻¹π₁,4) Wg(σ₂⁻¹π₂,4) · Wg(γ₁⁻¹τ₁,4) Wg(γ₂⁻¹τ₂,4)
· ⟨⟨V^{(12)}(π₁)V^{(34)}(π₂)|V^{(23)}(γ₁)V^{(41)}(γ₂)⟩⟩`.

It carries a Weingarten factor on both sides, one for each layer. -/
def twoLayerKernel (σ₁ σ₂ τ₁ τ₂ : Equiv.Perm Copies) : ℂ :=
  ∑ π₁, ∑ π₂, ∑ γ₁, ∑ γ₂,
    (wg (σ₁⁻¹ * π₁) * wg (σ₂⁻¹ * π₂)) * (wg (γ₁⁻¹ * τ₁) * wg (γ₂⁻¹ * τ₂)) *
      hsOverlap (V12 π₁ * V34 π₂) (V23 γ₁ * V41 γ₂)

set_option maxRecDepth 1024 in
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
    sumRankOne_comp_sumRankOne
      (fun s : PermPair => layerAKet s.1 s.2) (fun s : PermPair => layerAKet s.1 s.2) wgPair
      (fun s : PermPair => layerBKet s.1 s.2) (fun s : PermPair => layerBKet s.1 s.2) wgPair]
  simp only [Fintype.sum_prod_type, wgPair, inner_layerAKet_layerBKet]

set_option maxRecDepth 1024 in
/-- **Equation (24) of `magic_monotones.pdf`.** Summing the inner labels `π₁, π₂, γ₁, γ₂`
first, the two-layer moment operator is a sum over the outer labels only, with the two-layer
kernel `K` of Eq. (25) as coefficient:
`M = ∑_{σ₁,σ₂} ∑_{τ₁,τ₂} K_{(σ₁,σ₂),(τ₁,τ₂)}
      |V^{(12)}(σ₁) V^{(34)}(σ₂)⟩⟩⟨⟨V^{(23)}(τ₁) V^{(41)}(τ₂)|`. -/
theorem twoLayerMoment_eq_kernel_sum :
    twoLayerMoment =
      ∑ σ₁, ∑ σ₂, ∑ τ₁, ∑ τ₂,
        twoLayerKernel σ₁ σ₂ τ₁ τ₂ • rankOne ℂ (layerAKet σ₁ σ₂) (layerBKet τ₁ τ₂) := by
  rw [twoLayerMoment, layerA_eq_pairSum, layerB_eq_pairSum,
    sumRankOne_comp_sumRankOne_kernel
      (fun s : PermPair => layerAKet s.1 s.2) (fun s : PermPair => layerAKet s.1 s.2) wgPair
      (fun s : PermPair => layerBKet s.1 s.2) (fun s : PermPair => layerBKet s.1 s.2) wgPair]
  simp only [Fintype.sum_prod_type, twoLayerKernel, wgPair, inner_layerAKet_layerBKet]

/-- **The two-layer kernel, made explicit.** Evaluating the interlayer overlaps of Eq. (25) by
Eq. (23) (`MagicMonotone.hsOverlap_layer_eq_two_pow`, which reads them off the repository's
Weingarten Gram matrix at local dimension `2`), the kernel involves nothing but the `k = 4`
Weingarten values `SchurWeyl.K4.wgVal` and powers of two:
`K = ∑_{π₁,π₂,γ₁,γ₂} Wg(σ₁⁻¹π₁,4) Wg(σ₂⁻¹π₂,4) Wg(γ₁⁻¹τ₁,4) Wg(γ₂⁻¹τ₂,4)
      · 2^{#(π₁⁻¹γ₁)+#(π₁⁻¹γ₂)+#(π₂⁻¹γ₁)+#(π₂⁻¹γ₂)}`. -/
theorem twoLayerKernel_eq_two_pow_sum (σ₁ σ₂ τ₁ τ₂ : Equiv.Perm Copies) :
    twoLayerKernel σ₁ σ₂ τ₁ τ₂ =
      ∑ π₁, ∑ π₂, ∑ γ₁, ∑ γ₂,
        (wg (σ₁⁻¹ * π₁) * wg (σ₂⁻¹ * π₂)) * (wg (γ₁⁻¹ * τ₁) * wg (γ₂⁻¹ * τ₂)) *
          2 ^ (numCyc (π₁⁻¹ * γ₁) + numCyc (π₁⁻¹ * γ₂) +
            numCyc (π₂⁻¹ * γ₁) + numCyc (π₂⁻¹ * γ₂)) := by
  simp only [twoLayerKernel, hsOverlap_layer_eq_two_pow]

end MagicMonotone

end
