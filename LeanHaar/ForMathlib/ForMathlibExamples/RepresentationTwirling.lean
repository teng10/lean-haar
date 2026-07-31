import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral

/-!
# Representation-theoretic ingredients for group twirling

This file records the Schur-lemma step used in the complete group-twirling calculation.  Unlike an
assumption-heavy sector-average package, the hypotheses here are stated directly in terms of Mathlib's
`Representation.IsIrreducible` and `Representation.IntertwiningMap`.
-/

noncomputable section

open scoped MonoidAlgebra

namespace Representation

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]

/-- Schur's lemma over `ℂ`, in the form needed for twirling: every equivariant endomorphism of a
finite-dimensional irreducible representation is scalar. -/
theorem IsIrreducible.intertwiner_eq_scalar_identity (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] [FiniteDimensional ℂ V] (f : ρ.IntertwiningMap ρ) :
    ∃ c : ℂ, f.toLinearMap = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ) |>.2 f
  refine ⟨c, ?_⟩
  rw [← hc]
  rfl

/-- The scalar in Schur's lemma is determined by the trace.  This is the abstract source of the
factor `1 / dim(M_q)` in the depolarizing channel. -/
theorem IsIrreducible.intertwiner_eq_trace_over_dimension_identity
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] [FiniteDimensional ℂ V]
    (f : ρ.IntertwiningMap ρ) :
    f.toLinearMap =
      (LinearMap.trace ℂ V f.toLinearMap / (Module.finrank ℂ V : ℂ)) • LinearMap.id := by
  letI : Nontrivial V := by
    by_contra h
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp h
    have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply SetLike.ext
      intro x
      change x = 0 ↔ True
      simp [Subsingleton.elim x 0]
    exact bot_ne_top hbot_top
  obtain ⟨c, hc⟩ := IsIrreducible.intertwiner_eq_scalar_identity ρ f
  rw [hc, map_smul, LinearMap.trace_id]
  have hfinrank : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  change c • LinearMap.id =
    (c * (Module.finrank ℂ V : ℂ) / (Module.finrank ℂ V : ℂ)) • LinearMap.id
  rw [mul_div_cancel_right₀ c hfinrank]

/-- Schur orthogonality for inequivalent irreducibles: every intertwiner between them is zero.
This is the representation-theoretic reason that Haar twirling removes off-diagonal blocks between
distinct isotypic sectors. -/
theorem IsIrreducible.intertwiner_vanishes_between_inequivalent_irreps
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] [IsEmpty (Equiv ρ σ)]
    (f : ρ.IntertwiningMap σ) : f = 0 := by
  exact Subsingleton.elim f 0

/-- **Irreducible group-twirling theorem.**  If the group average of an operator is an
intertwiner and preserves its trace, then it is the completely depolarized operator
`Tr(A) / dim(V) • id`.

For Haar averaging, the intertwining hypothesis follows from invariance of Haar measure and the
trace hypothesis follows from cyclicity of trace.  Keeping those two analytic facts explicit makes
this theorem applicable to any normalized group average while all representation-theoretic content
is discharged by Mathlib's Schur lemma. -/
theorem IsIrreducible.irreducible_average_eq_depolarizing
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (average : ρ.IntertwiningMap ρ)
    (htrace : LinearMap.trace ℂ V average.toLinearMap = LinearMap.trace ℂ V A) :
    average.toLinearMap =
      (LinearMap.trace ℂ V A / (Module.finrank ℂ V : ℂ)) • LinearMap.id := by
  rw [IsIrreducible.intertwiner_eq_trace_over_dimension_identity ρ average, htrace]

/-- **Isotypic group-twirling theorem.**  Regard an operator on `M ⊗ N` as a matrix of
operators on the irreducible carrier `M`, with row and column indices in a basis of the
multiplicity space `N`.  Haar averaging makes every such matrix entry an intertwiner and preserves
its trace.  Schur's lemma therefore replaces each entry by its trace divided by `dim(M)`, times the
identity on `M`.  Entrywise, this is exactly `R_M ⊗ I_N`.

The index type is deliberately arbitrary: no basis, topology, or finite-dimensional assumption on
the multiplicity labels is needed for the representation-theoretic conclusion. -/
theorem IsIrreducible.multiplicity_matrix_average_eq_depolarizing
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] [FiniteDimensional ℂ V]
    {N : Type*} (A : N → N → Module.End ℂ V)
    (average : N → N → ρ.IntertwiningMap ρ)
    (htrace : ∀ i j,
      LinearMap.trace ℂ V (average i j).toLinearMap = LinearMap.trace ℂ V (A i j)) :
    ∀ i j, (average i j).toLinearMap =
      (LinearMap.trace ℂ V (A i j) / (Module.finrank ℂ V : ℂ)) • LinearMap.id := by
  intro i j
  exact IsIrreducible.irreducible_average_eq_depolarizing ρ (A i j) (average i j)
    (htrace i j)

end Representation
