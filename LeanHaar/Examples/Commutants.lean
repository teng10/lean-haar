/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
import LeanHaar.HilbertSpace
import LeanHaar.SchurWeylAbstract
import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# Generalized Commutant of the $k$-th Order Unitary Group

This file formalizes the generalized commutant of the $k$-th order unitary group.
Specifically, it proves that the set of endomorphisms of the $k$-fold tensor product
space `⨂[ℂ]^k 𝓗[d]` that commute with the $k$-fold tensor power of all unitary operators
`glPow U.toLinearMap` consists exactly of the span of the permutation operators
`permSpan`.

When the dimension of the space is 2 (e.g. `card d = 2`), this corresponds to the
commutant of $\mathcal{U}(2)^{\otimes k}$ being the span of $V_d(\pi)$ for $\pi \in S_k$,
as described in `commutants.tex`.
-/

noncomputable section

namespace LeanHaar

open scoped TensorProduct
open SchurWeylAbstract

/-- The unitary group of the finite Hilbert space `𝓗[d]`. -/
abbrev UnitaryGroup (d : Type*) [Fintype d] [DecidableEq d] :=
  FiniteHilbertSpace d ≃ₗᵢ[ℂ] FiniteHilbertSpace d

/-- NOTE: THIS IS A REPEAT METHOD FROM COMMUTANTS1D. In order to make this a standalone document, I have left it here.
The centralizer of the span of a set of elements in an algebra equals the centralizer
of the set itself. This general property states that commuting with a set of generators is
equivalent to commuting with their linear span. -/
lemma centralizer_span {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (S : Set A) :
    Set.centralizer (Submodule.span R S : Set A) = Set.centralizer S := by
  ext x
  simp only [Set.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact h y (Submodule.subset_span hy)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => rw [zero_mul, mul_zero]
    | add y z _ _ hy hz => rw [add_mul, mul_add, hy, hz]
    | smul c y _ hy => rw [smul_mul_assoc, mul_smul_comm, hy]

/-- **Generalized Commutant of $k$-th Order Unitary Group** (Blueprint Theorem):
For any $k$-th order tensor power, the commutant of the unitary group representation
on `⨂[ℂ]^k 𝓗[d]` consists exactly of the span of the permutation operators `permSpan`. -/
theorem commutant_unitary_eq_permSpan (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    {M : (⨂[ℂ]^k (FiniteHilbertSpace d)) →ₗ[ℂ] (⨂[ℂ]^k (FiniteHilbertSpace d)) |
      ∀ U : UnitaryGroup d, M.comp (glPow U.toLinearMap) = (glPow U.toLinearMap).comp M} =
    ↑(permSpan (V := FiniteHilbertSpace d) (k := k)) := by
  ext M
  simp only [Set.mem_setOf_eq]
  -- Instantiate the abstract Schur-Weyl Duality for the given k and dimension d.
  have h_duality := permSpan_eq_centralizer_unitaryTensorSpan (W := FiniteHilbertSpace d) (k := k)
  -- Unfold the definition of unitaryTensorSpan and rewrite centralizer_span to shift the duality
  -- from the submodule span to the generating unitary tensor powers.
  rw [unitaryTensorSpan, centralizer_span] at h_duality
  -- Substitute the centralizer equivalence and apply Schur-Weyl duality to map to permSpan.
  rw [h_duality, Set.mem_centralizer_iff]
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact forall_congr' fun U ↦ eq_comm

end LeanHaar
