/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Vectorized operators and the rank-one ("ket-bra") calculus

This file collects the small amount of linear algebra needed to read the vectorized
Weingarten computations of `magic_monotones.pdf` as statements about honest linear maps.

Two ingredients are formalized.

* **Vectorization.** The map `vec : L(ℂ^m) → (ℂ^m)^{⊗2}`, `vec(|i⟩⟨j|) = |i⟩ ⊗ |j⟩`, written
  `|A⟩⟩` in the source. Here it is `MagicMonotone.vecOp`, sending a matrix to the vector of
  its entries. Under it, the Hilbert–Schmidt inner product `⟨⟨A|B⟩⟩ = Tr(A† B)` of the source
  (its Eq. (11)) becomes the standard inner product of the two vectorizations
  (`MagicMonotone.inner_vecOp_vecOp`).

* **Ket-bra operators.** The vectorized moment operators of the source are sums of rank-one
  operators `|a⟩⟩⟨⟨b|`, which is Mathlib's `InnerProductSpace.rankOne ℂ a b : x ↦ ⟪b, x⟫ • a`.
  The computation that turns a composition of two such sums into a single sum is
  `MagicMonotone.sumRankOne_comp_sumRankOne` (the "contraction" step, Eq. (22) of the source)
  and `MagicMonotone.sumRankOne_comp_sumRankOne_kernel` (the same statement regrouped so that
  the inner summations become a kernel, Eqs. (24)–(25) of the source).
-/

noncomputable section

open scoped InnerProductSpace Matrix
open InnerProductSpace ContinuousLinearMap

namespace MagicMonotone

/-! ### Vectorization of operators -/

/-- **Vectorization.** `vec : L(ℂ^m) → (ℂ^m)^{⊗2}` with `vec(|i⟩⟨j|) = |i⟩ ⊗ |j⟩`, written
`|A⟩⟩` in `magic_monotones.pdf`. Concretely it lists the entries of the matrix `A`. -/
def vecOp {m : Type*} [Fintype m] (A : Matrix m m ℂ) : EuclideanSpace ℂ (m × m) :=
  WithLp.toLp 2 fun p => A p.1 p.2

/-- **The vectorized inner product is the Hilbert–Schmidt inner product**, Eq. (11) of
`magic_monotones.pdf`: `⟨⟨A|B⟩⟩ = Tr(A† B)`. -/
lemma inner_vecOp_vecOp {m : Type*} [Fintype m] (A B : Matrix m m ℂ) :
    (inner ℂ (vecOp A) (vecOp B) : ℂ) = (Aᴴ * B).trace := by
  have hlhs : (inner ℂ (vecOp A) (vecOp B) : ℂ)
      = ∑ i : m, ∑ j : m, (starRingEnd ℂ) (A i j) * B i j := by
    simp only [vecOp, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hrhs : (Aᴴ * B).trace = ∑ i : m, ∑ j : m, (starRingEnd ℂ) (A j i) * B j i := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diag, Matrix.conjTranspose_apply]
  rw [hlhs, hrhs, Finset.sum_comm]

/-! ### Reordering iterated sums

Two bookkeeping lemmas, used to move a summation index from the innermost to the outermost
position; they are the only content of the regrouping steps below. -/

/-- Move the innermost of three summations to the outside. -/
lemma sum_rotate₃ {A α β γ : Type*} [AddCommMonoid A] [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → A) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ x, ∑ y, F x y z :=
  calc ∑ x, ∑ y, ∑ z, F x y z
      = ∑ x, ∑ z, ∑ y, F x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, F x y z := Finset.sum_comm

/-- Bring the two inner summations of a fourfold sum to the outside, keeping their order. -/
lemma sum_rotate₄ {A α β : Type*} [AddCommMonoid A] [Fintype α] [Fintype β]
    (F : α → α → β → β → A) :
    ∑ g, ∑ t, ∑ s, ∑ p, F s p g t = ∑ s, ∑ p, ∑ g, ∑ t, F s p g t :=
  calc ∑ g, ∑ t, ∑ s, ∑ p, F s p g t
      = ∑ g, ∑ s, ∑ t, ∑ p, F s p g t := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ s, ∑ g, ∑ t, ∑ p, F s p g t := Finset.sum_comm
    _ = ∑ s, ∑ p, ∑ g, ∑ t, F s p g t :=
        Finset.sum_congr rfl fun s _ => sum_rotate₃ fun g t p => F s p g t

/-! ### Composing sums of ket-bra operators -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Composition on the right is additive: `(∑ i, f i) ∘ g = ∑ i, f i ∘ g`. -/
lemma sum_comp_eq {ι : Type*} [Fintype ι] (f : ι → E →L[ℂ] E) (g : E →L[ℂ] E) :
    (∑ i, f i) ∘L g = ∑ i, f i ∘L g := by
  ext x; simp

/-- Composition on the left is additive: `f ∘ (∑ i, g i) = ∑ i, f ∘ g i`. -/
lemma comp_sum_eq {ι : Type*} [Fintype ι] (f : E →L[ℂ] E) (g : ι → E →L[ℂ] E) :
    f ∘L (∑ i, g i) = ∑ i, f ∘L g i := by
  ext x; simp [map_sum]

/-- **Contracting two sums of ket-bra operators.** Composing
`∑_{s,p} c(s,p) |a s⟩⟩⟨⟨b p|` with `∑_{g,t} c'(g,t) |u g⟩⟩⟨⟨v t|` replaces each pair of
neighbouring factors `⟨⟨b p| · |u g⟩⟩` by their overlap:
`∑_{s,p,g,t} c(s,p) c'(g,t) ⟨⟨b p|u g⟩⟩ |a s⟩⟩⟨⟨v t|`.

This is the contraction step, Eq. (22) of `magic_monotones.pdf`. -/
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
    simp only [sum_comp_eq, comp_sum_eq, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, rankOne_comp_rankOne, smul_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf
  -- Then move the summations over the second layer, `g` and `t`, back inside.
  rw [hdistrib]
  exact sum_rotate₄ fun s p g t =>
    (c s p * c' g t * (inner ℂ (b p) (u g) : ℂ)) • rankOne ℂ (a s) (v t)

/-- **The same composition, regrouped into a kernel.** Summing the inner indices `p, g` first
turns the contraction of the previous lemma into a single sum over the outer indices `s, t`
whose coefficient is the kernel `∑_{p,g} c(s,p) c'(g,t) ⟨⟨b p|u g⟩⟩`.

This is the passage from Eq. (22) to Eqs. (24)–(25) of `magic_monotones.pdf`. -/
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

end MagicMonotone

end
