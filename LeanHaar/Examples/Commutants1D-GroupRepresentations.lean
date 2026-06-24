import LeanHaar.HilbertSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Commutant of the first order unitary group

Group Representation Theory Framework Approach

This file formalizes the result from the blueprint (subsections/examples/commutants.tex)
stating that any endomorphism of the Hilbert space `𝓗[d]` that commutes with all
unitaries is a scalar multiple of the identity.

This is the $k=1$ case of Schur–Weyl duality, but we deliberately avoid using the Schur-Weyl duality in this proof.

## Main results

* `LeanHaar.unitary_irreducible` : The natural representation of the unitary group on `𝓗[d]`
  is irreducible.
* `LeanHaar.unitary_rep_schur_lemma` : Schur's Lemma for endomorphisms of the natural unitary
  representation: any equivariant linear map is a scalar multiple of the identity.
* `LeanHaar.commutant_unitary_eq_scalar` : The commutant of the unitary group is the set of
  scalar multiples of the identity.
-/

noncomputable section

namespace LeanHaar

set_option allowUnsafeReducibility true
attribute [local reducible] Representation.asModule

open FiniteHilbertSpace
open scoped MonoidAlgebra

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The unitary group of the finite Hilbert space `𝓗[d]`. -/
abbrev UnitaryGroup (d : Type*) [Fintype d] [DecidableEq d] :=
  FiniteHilbertSpace d ≃ₗᵢ[ℂ] FiniteHilbertSpace d

/-- The natural representation of the unitary group on `𝓗[d]`. -/
def unitaryRep (d : Type*) [Fintype d] [DecidableEq d] :
    Representation ℂ (UnitaryGroup d) (FiniteHilbertSpace d) where
  toFun U := U.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Nonempty d] in -- do not consider the case d = 0
/-- Helper lemma: A singleton restriction of a unit vector is orthonormal.
Since a singleton set contains no distinct pairs of vectors, the orthogonality condition is vacuously satisfied. -/
lemma orthonormal_restrict_singleton (v : FiniteHilbertSpace d) (hv : ‖v‖ = 1) (idx : d) :
    Orthonormal ℂ (({idx} : Set d).restrict (fun _ ↦ v)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have : i = j := Subsingleton.elim i j
  subst this
  simp [inner_self_eq_norm_sq_to_K, hv]

/-- The unitary group acts transitively on the unit sphere of `𝓗[d]`.
This lemma proves that for any two unit vectors `v` and `w`, there exists a unitary `U`
such that `U v = w`. -/
lemma unitary_transitive_on_sphere (v w : FiniteHilbertSpace d)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ U : UnitaryGroup d, U v = w := by
  have idx : d := Classical.arbitrary d
  let s : Set d := {idx}
  have h_ortho_v := orthonormal_restrict_singleton v hv idx -- {v}^⟂
  have h_ortho_w := orthonormal_restrict_singleton w hw idx -- {w}^⟂
  have h_dim : Module.finrank ℂ (FiniteHilbertSpace d) = Fintype.card d := by
    rw [Module.finrank_eq_card_basis (FiniteHilbertSpace.basisFun d).toBasis]
  -- Extend both orthonormal families to full orthonormal bases of `𝓗[d]`.
  obtain ⟨bv, hbv⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq h_dim h_ortho_v
  obtain ⟨bw, hbw⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq h_dim h_ortho_w
  -- Define the unitary change-of-basis operator `U` mapping the first basis to the second.
  let U := bv.repr.trans bw.repr.symm
  use U
  rw [← hbv idx (Set.mem_singleton idx)]
  dsimp [U]
  simp [hbw idx (Set.mem_singleton idx)]

-- The local Module instance on `asModule` equips it with a module structure over `ℂ[UnitaryGroup d]`.
noncomputable local instance :
    Module ℂ[UnitaryGroup d] (unitaryRep d).asModule :=
  Representation.instModuleMonoidAlgebraAsModule (unitaryRep d)

-- The local IsScalarTower instance ensures compatibility between the complex scalars and the group algebra action.
noncomputable local instance :
    IsScalarTower ℂ ℂ[UnitaryGroup d] (unitaryRep d).asModule where
  smul_assoc c r v := by
    change (Representation.asAlgebraHom (unitaryRep d) (c • r)) v = c • (Representation.asAlgebraHom (unitaryRep d) r) v
    rw [map_smul]
    rfl

/-- The natural representation of the unitary group on `𝓗[d]` is irreducible. -/
instance unitary_irreducible : (unitaryRep d).IsIrreducible := by
  -- Convert representation irreducibility to simplicity of the associated group algebra module.
  refine (Representation.irreducible_iff_isSimpleModule_asModule (unitaryRep d)).mpr ?_
  rw [isSimpleModule_iff]
  -- A module is simple if it is non-trivial and any submodule `W` is either `⊥` or `⊤`.
  refine IsSimpleOrder.of_forall_eq_top (α := Submodule ℂ[UnitaryGroup d] (unitaryRep d).asModule) ?_
  intro W hW
  rw [Submodule.ne_bot_iff] at hW
  -- Obtain a non-zero vector `v ∈ W`.
  obtain ⟨v, hv_mem, hv_ne⟩ := hW
  ext w
  simp only [Submodule.mem_top, iff_true]
  by_cases hw0 : w = 0
  · rw [hw0]; exact W.zero_mem
  -- Normalize `v` and `w` to unit vectors and use transitivity of the unitary group action on the sphere.
  have hv_norm_ne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv_ne
  have hw_norm_ne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  let v0 := ((1 : ℂ) / (‖v‖ : ℂ)) • v
  let w0 := ((1 : ℂ) / (‖w‖ : ℂ)) • w
  have hv0 : ‖v0‖ = 1 := by
    simp [v0, norm_smul]
    exact inv_mul_cancel₀ hv_norm_ne
  have hw0' : ‖w0‖ = 1 := by
    simp [w0, norm_smul]
    exact inv_mul_cancel₀ hw_norm_ne
  obtain ⟨U, hU⟩ := unitary_transitive_on_sphere v0 w0 hv0 hw0'
  -- Show that `U v ∈ W` since `W` is invariant under the unitary group representation action.
  have memUv : U.toLinearMap v ∈ W := by
    have h := W.smul_mem (MonoidAlgebra.of ℂ (UnitaryGroup d) U) hv_mem
    change (Representation.asAlgebraHom (unitaryRep d) (MonoidAlgebra.of ℂ (UnitaryGroup d) U)) v ∈ W at h
    rwa [Representation.asAlgebraHom_of] at h
  have hv_complex : (‖v.val‖ : ℂ) ≠ 0 := by exact_mod_cast hv_norm_ne
  -- Verify the relation `U v = (‖v‖/‖w‖) • w`.
  have hcompute : U.toLinearMap v = ((‖v‖ : ℂ) / (‖w‖ : ℂ)) • w := by
    calc
      U.toLinearMap v = U.toLinearMap ((‖v‖ : ℂ) • v0) := by
        congr 1
        simp [v0, smul_smul, mul_inv_cancel₀ hv_complex]
      _ = (‖v‖ : ℂ) • U v0 := map_smul U.toLinearMap (‖v‖ : ℂ) v0
      _ = (‖v‖ : ℂ) • w0 := by rw [hU]
      _ = ((‖v‖ : ℂ) / (‖w‖ : ℂ)) • w := by simp [w0, smul_smul, div_eq_mul_inv]
  -- Rescale `U v` by `(‖w‖/‖v‖)` to reconstruct `w` and conclude `w ∈ W`.
  have h_scaled : (algebraMap ℂ (MonoidAlgebra ℂ (UnitaryGroup d)) ((‖w‖ : ℂ) / (‖v‖ : ℂ))) • U.toLinearMap v ∈ W :=
    W.smul_mem (algebraMap ℂ (MonoidAlgebra ℂ (UnitaryGroup d)) ((‖w‖ : ℂ) / (‖v‖ : ℂ))) memUv
  rw [IsScalarTower.algebraMap_smul] at h_scaled
  have h_eq : ((‖w‖ : ℂ) / (‖v‖ : ℂ)) • U.toLinearMap v = w := by
    rw [hcompute, ← mul_smul]
    have hv_complex : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hv_norm_ne
    have hw_complex : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hw_norm_ne
    field_simp
    rw [one_smul]
  rw [h_eq] at h_scaled
  exact h_scaled

/-- **Schur's Lemma** for endomorphisms of the natural unitary representation.
Any equivariant linear map is a scalar multiple of the identity. -/
lemma unitary_rep_schur_lemma (f : FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d)
    (hf : ∀ U : UnitaryGroup d, f.comp U.toLinearMap = U.toLinearMap.comp f) :
    ∃ (scalar : ℂ), f = scalar • LinearMap.id := by
  -- Construct the equivariant (intertwining) map `f_int` from the given linear map `f`.
  let f_int : Representation.IntertwiningMap (unitaryRep d) (unitaryRep d) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap
      (ρ := unitaryRep d) (σ := unitaryRep d) (f := f) (fun U v ↦ by
      have := LinearMap.congr_fun (hf U) v
      exact this)
  -- Obtain the scalar multiple from Schur's Lemma for algebraically closed fields,
  -- using the fact that the natural unitary representation is irreducible.
  obtain ⟨scalar, h⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.surjective f_int
  use scalar
  -- Extract the underlying linear maps of the intertwining map equation to prove `f = scalar • id`.
  have h_eq : (algebraMap ℂ (Representation.IntertwiningMap (unitaryRep d) (unitaryRep d)) scalar).toLinearMap = f_int.toLinearMap := by
    rw [h]
  rw [Representation.IntertwiningMap.algebraMap_apply] at h_eq
  rw [Representation.IntertwiningMap.toLinearMap_smul] at h_eq
  exact h_eq.symm

/-- **Commutant of first order unitaries** (Blueprint Theorem):
The set of endomorphisms of `𝓗[d]` that commute with all unitaries consists exactly of
scalar multiples of the identity. -/
theorem commutant_unitary_eq_scalar :
    {M : FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d |
      ∀ U : UnitaryGroup d, M.comp U.toLinearMap = U.toLinearMap.comp M} =
    {M | ∃ (scalar : ℂ), M = scalar • LinearMap.id} := by
  ext M
  simp only [Set.mem_setOf_eq]
  constructor
  · exact unitary_rep_schur_lemma M
  · rintro ⟨scalar, rfl⟩ U
    rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
end LeanHaar
