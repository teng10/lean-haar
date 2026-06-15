import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Basic definitions

This file defines `FiniteHilbertSpace n`, the finite-dimensional complex Hilbert space of
dimension `n`, as an abbreviation for `EuclideanSpace ℂ (Fin n)`.

For tensor powers we use Mathlib's `TensorPower` directly, written `⨂[ℂ]^k V`
(available after `open scoped TensorProduct`).
-/

namespace LeanHaar

-- /-- The finite-dimensional complex Hilbert space of dimension `n`,
-- realized as `EuclideanSpace ℂ (Fin n)`.
-- This is an abbreviation, so all instances on `EuclideanSpace` are inherited. -/
-- abbrev FiniteHilbertSpace (n : ℕ) : Type :=
--   EuclideanSpace ℂ (Fin n)


/-- The Hilbert space of a finite target quantum mechanical system whose target is
  a finite type `d` with decidable equality.

  It is defined as a structure with a single field `val`, wrapping an element of
  `EuclideanSpace ℂ d` — the space of functions `d → ℂ` carrying the `L²` inner
  product `⟪ψ, φ⟫ = ∑ i, conj (ψ i) * φ i`. We use the notation `𝓗[d]` to
  denote the Hilbert space corresponding to the type `d`.
-/
@[ext]
structure FiniteHilbertSpace (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The underlying element of `EuclideanSpace ℂ d`. -/
  val : EuclideanSpace ℂ d

@[inherit_doc FiniteHilbertSpace]
scoped notation "𝓗[" d "]" => FiniteHilbertSpace d


namespace FiniteHilbertSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d`
  given by `val`. -/
def equivEuclidean : FiniteHilbertSpace d ≃ EuclideanSpace ℂ d where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-!

## The vector space structure on `FiniteHilbertSpace d`

The vector space structure is transferred from `EuclideanSpace ℂ d`
along the equivalence `equivEuclidean`.

-/

noncomputable instance : AddCommGroup (FiniteHilbertSpace d) := equivEuclidean.addCommGroup

noncomputable instance : Module ℂ (FiniteHilbertSpace d) := equivEuclidean.module ℂ

@[simp]
lemma val_add (ψ φ : FiniteHilbertSpace d) : (ψ + φ).val = ψ.val + φ.val := rfl

@[simp]
lemma val_smul (c : ℂ) (ψ : FiniteHilbertSpace d) : (c • ψ).val = c • ψ.val := rfl

@[simp]
lemma val_zero : (0 : FiniteHilbertSpace d).val = 0 := rfl

/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d`
  as a `ℂ`-linear equivalence, upgrading `equivEuclidean`. -/
noncomputable def linearEquivEuclidean : FiniteHilbertSpace d ≃ₗ[ℂ] EuclideanSpace ℂ d :=
  { equivEuclidean with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-!

## The Hilbert space structure on `FiniteHilbertSpace d`

The norm and inner product are induced from `EuclideanSpace ℂ d` along
`linearEquivEuclidean`, making `FiniteHilbertSpace d` a finite dimensional
(and hence complete) inner product space, that is, a Hilbert space.

-/

noncomputable instance : NormedAddCommGroup (FiniteHilbertSpace d) :=
  NormedAddCommGroup.induced _ _ linearEquivEuclidean.toLinearMap linearEquivEuclidean.injective

@[simp]
lemma norm_eq_val (ψ : FiniteHilbertSpace d) : ‖ψ‖ = ‖ψ.val‖ := rfl

noncomputable instance : InnerProductSpace ℂ (FiniteHilbertSpace d) :=
  InnerProductSpace.induced linearEquivEuclidean.toLinearMap

@[simp]
lemma inner_eq_val (ψ φ : FiniteHilbertSpace d) : inner ℂ ψ φ = inner ℂ ψ.val φ.val := rfl

instance : FiniteDimensional ℂ (FiniteHilbertSpace d) :=
  Module.Finite.equiv linearEquivEuclidean.symm

-- Being finite dimensional, it is automatically a complete inner product space.
instance : CompleteSpace (FiniteHilbertSpace d) := FiniteDimensional.complete ℂ _

/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d`
  as a linear isometry equivalence, upgrading `linearEquivEuclidean`. -/
noncomputable def isometryEquivEuclidean : FiniteHilbertSpace d ≃ₗᵢ[ℂ] EuclideanSpace ℂ d where
  toLinearEquiv := linearEquivEuclidean
  norm_map' _ := rfl

/-!

## The standard orthonormal basis of `FiniteHilbertSpace d`

-/

/-- The standard orthonormal basis of `FiniteHilbertSpace d`, indexed by `d`. -/
noncomputable def basisFun (d : Type*) [Fintype d] [DecidableEq d] :
    OrthonormalBasis d ℂ (FiniteHilbertSpace d) :=
  (EuclideanSpace.basisFun d ℂ).map isometryEquivEuclidean.symm

lemma basisFun_apply (i : d) : basisFun d i = ⟨EuclideanSpace.single i 1⟩ := by
  rw [basisFun, OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply]; rfl

end FiniteHilbertSpace

end LeanHaar
