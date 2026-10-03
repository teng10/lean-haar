/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring

/-!
# Composition of finite sums of rank-one operators

The contraction of two finite sums of rank-one operators is expressed first as a sum over
all four indices and then as a kernel over the two outer indices. These lemmas apply to any
complex inner product space and use Mathlib's `InnerProductSpace.rankOne` directly.
-/

noncomputable section

open scoped InnerProductSpace
open ContinuousLinearMap

namespace InnerProductSpace

/-! ### Reordering iterated sums

Two bookkeeping lemmas, used to move a summation index from the innermost to the outermost
position; they are the only content of the regrouping steps below. -/

/-- Move the innermost of three summations to the outside. -/
private lemma sum_rotate₃ {A α β γ : Type*} [AddCommMonoid A] [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → A) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ x, ∑ y, F x y z :=
  calc ∑ x, ∑ y, ∑ z, F x y z
      = ∑ x, ∑ z, ∑ y, F x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, F x y z := Finset.sum_comm

/-- Bring the two inner summations of a fourfold sum to the outside, keeping their order. -/
private lemma sum_rotate₄ {A α β : Type*} [AddCommMonoid A] [Fintype α] [Fintype β]
    (F : α → α → β → β → A) :
    ∑ g, ∑ t, ∑ s, ∑ p, F s p g t = ∑ s, ∑ p, ∑ g, ∑ t, F s p g t :=
  calc ∑ g, ∑ t, ∑ s, ∑ p, F s p g t
      = ∑ g, ∑ s, ∑ t, ∑ p, F s p g t := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ s, ∑ g, ∑ t, ∑ p, F s p g t := Finset.sum_comm
    _ = ∑ s, ∑ p, ∑ g, ∑ t, F s p g t :=
        Finset.sum_congr rfl fun s _ => sum_rotate₃ fun g t p => F s p g t

/-! ### Composing sums of ket-bra operators -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Contracting two sums of ket-bra operators.** Composing
`∑_{s,p} c(s,p) |a s⟩⟩⟨⟨b p|` with `∑_{g,t} c'(g,t) |u g⟩⟩⟨⟨v t|` replaces each pair of
neighbouring factors `⟨⟨b p| · |u g⟩⟩` by their overlap:
`∑_{s,p,g,t} c(s,p) c'(g,t) ⟨⟨b p|u g⟩⟩ |a s⟩⟩⟨⟨v t|`. -/
theorem sumRankOne_comp_sumRankOne {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ι → E) (c : ι → ι → ℂ) (u v : κ → E) (c' : κ → κ → ℂ) :
    (∑ s, ∑ p, c s p • rankOne ℂ (a s) (b p)) ∘L (∑ g, ∑ t, c' g t • rankOne ℂ (u g) (v t))
      = ∑ s, ∑ p, ∑ g, ∑ t,
          (c s p * c' g t * (inner ℂ (b p) (u g) : ℂ)) • rankOne ℂ (a s) (v t) := by
  -- Distribute the composition over the four sums, using
  -- `|a s⟩⟩⟨⟨b p| ∘ |u g⟩⟩⟨⟨v t| = ⟨⟨b p|u g⟩⟩ · |a s⟩⟩⟨⟨v t|`.
  have hdistrib :
      (∑ s, ∑ p, c s p • rankOne ℂ (a s) (b p)) ∘L (∑ g, ∑ t, c' g t • rankOne ℂ (u g) (v t))
        = ∑ g, ∑ t, ∑ s, ∑ p,
            (c s p * c' g t * (inner ℂ (b p) (u g) : ℂ)) • rankOne ℂ (a s) (v t) := by
    simp only [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, rankOne_comp_rankOne,
      smul_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf
  -- Then move the summations over the second layer, `g` and `t`, back inside.
  rw [hdistrib]
  exact sum_rotate₄ fun s p g t =>
    (c s p * c' g t * (inner ℂ (b p) (u g) : ℂ)) • rankOne ℂ (a s) (v t)

/-- **The same composition, regrouped into a kernel.** Summing the inner indices `p, g` first
turns the contraction of the previous lemma into a single sum over the outer indices `s, t`
whose coefficient is the kernel `∑_{p,g} c(s,p) c'(g,t) ⟨⟨b p|u g⟩⟩`. -/
theorem sumRankOne_comp_sumRankOne_kernel {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ι → E) (c : ι → ι → ℂ) (u v : κ → E) (c' : κ → κ → ℂ) :
    (∑ s, ∑ p, c s p • rankOne ℂ (a s) (b p)) ∘L (∑ g, ∑ t, c' g t • rankOne ℂ (u g) (v t))
      = ∑ s, ∑ t, (∑ p, ∑ g, c s p * c' g t * (inner ℂ (b p) (u g) : ℂ)) •
          rankOne ℂ (a s) (v t) := by
  rw [sumRankOne_comp_sumRankOne]
  refine Finset.sum_congr rfl fun s _ => ?_
  calc ∑ p, ∑ g, ∑ t,
        (c s p * c' g t * (inner ℂ (b p) (u g) : ℂ)) • rankOne ℂ (a s) (v t)
      -- move the summation over `t` to the outside ...
      = ∑ t, ∑ p, ∑ g,
          (c s p * c' g t * (inner ℂ (b p) (u g) : ℂ)) • rankOne ℂ (a s) (v t) :=
        sum_rotate₃ fun p g t =>
          (c s p * c' g t * (inner ℂ (b p) (u g) : ℂ)) • rankOne ℂ (a s) (v t)
      -- ... and collect the remaining coefficients into the kernel.
    _ = ∑ t, (∑ p, ∑ g, c s p * c' g t * (inner ℂ (b p) (u g) : ℂ)) •
          rankOne ℂ (a s) (v t) :=
        Finset.sum_congr rfl fun _ _ => by simp [Finset.sum_smul]

end InnerProductSpace

end
