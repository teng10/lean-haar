import LeanHaar.HilbertSpace
import LeanHaar.SchurWeylAbstract
import LeanHaar.Examples.«Commutants1D-SchursLemma»
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.FDRep
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Commutant of the first order unitary group on the 1-fold tensor power

This file formalizes the result stating that any endomorphism of the 1-fold tensor power
of the Hilbert space `⨂[ℂ]^1 𝓗[d]` that commutes with the 1-fold tensor representation of the
unitary group is a scalar multiple of the identity.

We prove this using the category-theoretic Schur's Lemma by showing that:
1. The natural unitary representation on `𝓗[d]` is a simple object in `FDRep`.
2. The 1-fold tensor representation is isomorphic to the natural unitary representation.
3. Therefore, the 1-fold tensor representation is also simple, so any equivariant map on it
   must be a scalar multiple of the identity.

## Main definitions

## Main statements

* `LeanHaar.commutant_unitary_eq_scalar_tensor` : the commutant of the 1-fold tensor representation
  consists exactly of scalar multiples of the identity.

## Tags

representation theory, Schur's Lemma, unitary group, tensor power, commutant
-/

noncomputable section


open CategoryTheory
open Module
open scoped TensorProduct
open LeanHaar.SchurWeylAbstract
open LeanHaar

variable {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]

/-- Schur's lemma -/
lemma endomorphism_is_scalar {G : Type*} [Group G] (V : FDRep ℂ G) [Simple V] (f : V ⟶ V) :
    ∃ scalar : ℂ, f = scalar • 𝟙 V := by
  have h_dim : finrank ℂ (V ⟶ V) = 1 := by
    -- Using the category theory version of Schur's lemma
    -- Show that the dimension of the space is 1
    have h_schur := FDRep.finrank_hom_simple_simple V V
    -- Iso.refl is the identity (reflective)
    rw [if_pos (Nonempty.intro (Iso.refl V))] at h_schur
    exact h_schur
  -- The identity is nonzero, and since the space as dimension one and is spanned by 𝟙,
  -- every element must be a scalar multiple of 𝟙
  have hid : 𝟙 V ≠ 0 := id_nonzero V
  obtain ⟨scalar, h_eq⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 V) hid).mp h_dim f
  use scalar
  exact h_eq.symm

/-- **Commutant of first order unitaries**:
The set of endomorphisms of `𝓗[d]` that commute with all unitaries consists exactly of
scalar multiples of the identity. -/
theorem commutant_unitary_eq_scalar :
    {M : FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d |
      ∀ U : UnitaryGroup d, M.comp U.toLinearMap = U.toLinearMap.comp M} =
    {M | ∃ (scalar : ℂ), M = scalar • LinearMap.id} := by
    sorry
