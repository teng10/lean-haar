/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.WeingartenInverse

import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Vectorized operators and the rank-one ("ket-bra") calculus

This file collects the small amount of linear algebra needed to read the vectorized
Weingarten computations of `magic_monotones.pdf` as statements about honest linear maps.
Everything here is built on the vectorization already used by the repository to set up the
Weingarten system, `SchurWeyl.endVec` of `LeanHaar/ForMathlib/Weingarten.lean`.

Two ingredients are formalized.

* **Vectorization.** The map `vec : L(V) → V ⊗ V`, `vec(|i⟩⟨j|) = |i⟩ ⊗ |j⟩`, written `|A⟩⟩`
  in the source, is *not* redefined here: it is the repository's `SchurWeyl.endVec`, which
  lists the entries of the matrix of an operator on `(ℂ^d)^{⊗k}` in the computational basis.
  The only thing that has to be added is that under it the Hilbert–Schmidt inner product
  `⟨⟨A|B⟩⟩ = Tr(A† B)` of the source (its Eq. (11)) is the standard inner product of the two
  vectorizations: this is `MagicMonotone.inner_endVec_endVec`, which generalizes the
  repository's trace bridge `SchurWeyl.inner_endVec_perm_eq_trace` from permutation
  operators to arbitrary operators.

* **Ket-bra operators.** The vectorized moment operators of the source are sums of rank-one
  operators `|a⟩⟩⟨⟨b|`, which is Mathlib's `InnerProductSpace.rankOne ℂ a b : x ↦ ⟪b, x⟫ • a`.
  The computation that turns a composition of two such sums into a single sum is
  `MagicMonotone.sumRankOne_comp_sumRankOne` (the "contraction" step, Eq. (22) of the source)
  and `MagicMonotone.sumRankOne_comp_sumRankOne_kernel` (the same statement regrouped so that
  the inner summations become a kernel, Eqs. (24)–(25) of the source).
-/

noncomputable section

open scoped InnerProductSpace Matrix
open InnerProductSpace ContinuousLinearMap SchurWeyl

namespace MagicMonotone

/-! ### Vectorization of operators

The vectorization `|A⟩⟩` is the repository's `SchurWeyl.endVec`; nothing new is defined. The
only fact needed about it is that it turns the Euclidean inner product into the
Hilbert–Schmidt one. -/

/-- **The vectorized inner product is the Hilbert–Schmidt inner product**, Eq. (11) of
`magic_monotones.pdf`: `⟨⟨A|B⟩⟩ = Tr(A† B)`, where `|·⟩⟩` is the repository's vectorization
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
