import LeanHaar.HilbertSpace
import LeanHaar.SchurWeylAbstract
-- import LeanHaar.Examples.«Commutants1D-GroupRepresentation»
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

* `LeanHaar.E` : the canonical linear equivalence between `⨂[ℂ]^1 𝓗[d]` and `𝓗[d]`.
* `LeanHaar.T1Rep` : the 1-fold tensor representation of the unitary group.
* `LeanHaar.V_rep` : the representation `T1Rep` bundled as an object in `FDRep`.
* `LeanHaar.iso_E` : the equivariant isomorphism between `V_rep` and `FDRep.of (unitaryRep d)`.

## Main statements

* `LeanHaar.simple_unitaryRep` : the natural unitary representation is simple in `FDRep`.
* `LeanHaar.commutant_unitary_eq_scalar_tensor` : the commutant of the 1-fold tensor representation
  consists exactly of scalar multiples of the identity.

## Tags

representation theory, Schur's Lemma, unitary group, tensor power, commutant
-/

noncomputable section

namespace LeanHaar

open CategoryTheory
open Module
open scoped TensorProduct
open LeanHaar.SchurWeylAbstract
open LeanHaar

variable {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The unitary group of the finite Hilbert space `𝓗[d]`. -/
abbrev UnitaryGroup (d : Type*) [Fintype d] [DecidableEq d] :=
  FiniteHilbertSpace d ≃ₗᵢ[ℂ] FiniteHilbertSpace d

/-- The natural representation of the unitary group on `𝓗[d]`. -/
def unitaryRep (d : Type*) [Fintype d] [DecidableEq d] :
    Representation ℂ (UnitaryGroup d) (FiniteHilbertSpace d) where
  toFun U := U.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Canonical linear equivalence between the 1-fold tensor power of `𝓗[d]` and `𝓗[d]`. -/
noncomputable def E :
    (⨂[ℂ]^1 (FiniteHilbertSpace d)) ≃ₗ[ℂ] FiniteHilbertSpace d :=
  PiTensorProduct.subsingletonEquiv (0 : Fin 1)

omit [Nonempty d] in
/-- Evaluating `E` on `E.symm` yields the identity. -/
lemma E_toLinearMap_comp_symm :
    E.toLinearMap.comp E.symm.toLinearMap = (LinearMap.id : FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d) := by
  ext; simp [E]

omit [Nonempty d] in
/-- Evaluating `E.symm` on `E` yields the identity. -/
lemma E_symm_toLinearMap_comp :
    E.symm.toLinearMap.comp E.toLinearMap = (LinearMap.id : (⨂[ℂ]^1 (FiniteHilbertSpace d)) →ₗ[ℂ] (⨂[ℂ]^1 (FiniteHilbertSpace d))) := by
  ext; simp [E]

omit [Nonempty d] in
/-- Evaluation of `E` on `glPow` of an operator. -/
lemma E_comp_glPow (A : Module.End ℂ (FiniteHilbertSpace d)) :
    E.toLinearMap.comp (glPow A : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))) = A.comp E.toLinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, glPow_tprod]
  unfold E
  simp only [PiTensorProduct.subsingletonEquiv_apply_tprod]

omit [Nonempty d] in
/-- Evaluation of `glPow` on `E.symm` of an operator. -/
lemma glPow_comp_E_symm (A : Module.End ℂ (FiniteHilbertSpace d)) :
    (glPow A : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))).comp E.symm.toLinearMap = E.symm.toLinearMap.comp A := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  unfold E
  rw [PiTensorProduct.subsingletonEquiv_symm_apply' (0 : Fin 1) x]
  simp only [glPow_tprod]
  rw [PiTensorProduct.subsingletonEquiv_symm_apply' (0 : Fin 1) (A x)]

/-- The 1-fold tensor representation of the unitary group. -/
noncomputable def T1Rep :
    Representation ℂ (UnitaryGroup d) (⨂[ℂ]^1 (FiniteHilbertSpace d)) where
  toFun U := glPow U.toLinearMap
  map_one' := by
    have h1 : (1 : UnitaryGroup d).toLinearMap = 1 := rfl
    rw [h1]
    exact PiTensorProduct.map_one
  map_mul' U₁ U₂ := by
    have h1 : (U₁ * U₂).toLinearMap = U₁.toLinearMap * U₂.toLinearMap := rfl
    rw [h1]
    exact PiTensorProduct.map_mul (fun _ ↦ U₁.toLinearMap) (fun _ ↦ U₂.toLinearMap)

/-- Bundling `T1Rep` into an object of the `FDRep` category. -/
noncomputable abbrev V_rep [Module.Finite ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))] :
    FDRep ℂ (UnitaryGroup d) :=
  FDRep.of T1Rep

/-- Equivariant isomorphism between `V_rep` and `FDRep.of (unitaryRep d)`. -/
noncomputable def iso_E
    [Module.Finite ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))] :
    V_rep ≅ FDRep.of (unitaryRep d) where
  hom := {
    hom := ⟨ModuleCat.ofHom E.toLinearMap⟩
    comm := fun U ↦ by
      apply InducedCategory.hom_ext
      apply ModuleCat.Hom.ext
      exact E_comp_glPow U.toLinearMap
  }
  inv := {
    hom := ⟨ModuleCat.ofHom E.symm.toLinearMap⟩
    comm := fun U ↦ by
      apply InducedCategory.hom_ext
      apply ModuleCat.Hom.ext
      exact (glPow_comp_E_symm U.toLinearMap).symm
  }
  hom_inv_id := by
    apply Action.Hom.ext
    apply InducedCategory.hom_ext
    apply ModuleCat.Hom.ext
    exact E_symm_toLinearMap_comp
  inv_hom_id := by
    apply Action.Hom.ext
    apply InducedCategory.hom_ext
    apply ModuleCat.Hom.ext
    exact E_toLinearMap_comp_symm

/-- An isomorphism of finite-dimensional representations is an isomorphism in the category `FDRep`
if and only if its underlying linear map is bijective. -/
lemma isIso_iff_bijective_FDRep {G : Type*} [Group G] (Y X : FDRep ℂ G) (f : Y ⟶ X) :
    IsIso f ↔ Function.Bijective f.hom.hom.hom' := by
  have h1 : IsIso f ↔ IsIso f.hom := by
    constructor
    · intro h
      have : IsIso ((Action.forget (FGModuleCat ℂ) G).map f) := by infer_instance
      exact this
    · intro h
      exact Action.isIso_of_hom_isIso f
  rw [h1]
  have h_fully_faithful : (forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  have h_iso_iff : IsIso f.hom ↔ IsIso ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map f.hom) := by
    constructor
    · intro h; infer_instance
    · intro h; exact h_fully_faithful.isIso_of_isIso_map f.hom
  rw [h_iso_iff]
  rw [ConcreteCategory.isIso_iff_bijective]
  rfl

/-- Construct the range of a morphism in `FDRep` as a subrepresentation of the target representation. -/
noncomputable def rangeSubrepresentation (Y : FDRep ℂ (UnitaryGroup d)) (f : Y ⟶ FDRep.of (unitaryRep d)) :
    Subrepresentation (unitaryRep d) where
  toSubmodule := LinearMap.range f.hom.hom.hom'
  apply_mem_toSubmodule g v hv := by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hv
    have h_comm_map : f.hom.hom.hom'.comp (Y.ρ g) = (unitaryRep d) g ∘ₗ f.hom.hom.hom' := by
      have h_comm_morphism_1 := congr_arg (fun F : Y.V ⟶ (FDRep.of (unitaryRep d)).V ↦ F.hom) (f.comm g)
      exact congr_arg (fun F : ModuleCat.of ℂ Y.V ⟶ ModuleCat.of ℂ (FiniteHilbertSpace d) ↦ F.hom') h_comm_morphism_1
    have h_comm : (unitaryRep d) g (f.hom.hom.hom' x) = f.hom.hom.hom' (Y.ρ g x) := by
      exact (LinearMap.congr_fun h_comm_map x).symm
    exact_mod_cast LinearMap.mem_range.mpr ⟨Y.ρ g x, h_comm.symm⟩

/-- The natural unitary representation on `𝓗[d]` is a simple object in the category `FDRep`. -/
noncomputable instance simple_unitaryRep : Simple (FDRep.of (unitaryRep d)) where
  mono_isIso_iff_nonzero {Y} f mono_f := by
    constructor
    · intro hf_iso hf_zero
      have h_id : (𝟙 (FDRep.of (unitaryRep d)) : FDRep.of (unitaryRep d) ⟶ FDRep.of (unitaryRep d)) = 0 := by
        have h_eq : inv f ≫ f = inv f ≫ 0 := congr_arg (fun g ↦ inv f ≫ g) hf_zero
        rw [IsIso.inv_hom_id f] at h_eq
        exact h_eq
      have h_id_zero : (𝟙 (FDRep.of (unitaryRep d)) : FDRep.of (unitaryRep d) ⟶ FDRep.of (unitaryRep d)).hom.hom.hom' = 0 := by
        rw [h_id]
        rfl
      have h_id_id : (𝟙 (FDRep.of (unitaryRep d)) : FDRep.of (unitaryRep d) ⟶ FDRep.of (unitaryRep d)).hom.hom.hom' = LinearMap.id := rfl
      rw [h_id_id] at h_id_zero
      obtain ⟨x, y, hxy⟩ := (exists_pair_ne (FiniteHilbertSpace d))
      have h_eq : x = y := by
        have hx : x = 0 := by
          calc
            x = (LinearMap.id : FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d) x := rfl
            _ = 0 := by rw [h_id_zero]; rfl
        have hy : y = 0 := by
          calc
            y = (LinearMap.id : FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d) y := rfl
            _ = 0 := by rw [h_id_zero]; rfl
        rw [hx, hy]
      exact hxy h_eq
    · intro hf_nonzero
      have h_inj : Function.Injective f.hom.hom.hom' := by
        have : Mono ((forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map f) := inferInstance
        have h2 : Mono ((forget₂ (Rep ℂ (UnitaryGroup d)) (ModuleCat ℂ)).map ((forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map f)) := inferInstance
        exact (ModuleCat.mono_iff_injective _).1 h2
      have h_simple : IsSimpleOrder (Subrepresentation (unitaryRep d)) := unitary_irreducible
      obtain h_bot | h_top := h_simple.eq_bot_or_eq_top (rangeSubrepresentation Y f)
      · have h_range : (rangeSubrepresentation Y f).toSubmodule = ⊥ := congr_arg Subrepresentation.toSubmodule h_bot
        change LinearMap.range f.hom.hom.hom' = ⊥ at h_range
        have h_zero : f = 0 := by
          apply Action.Hom.ext
          change f.hom = 0
          have h_ext : f.hom = 0 ↔ f.hom.hom.hom' = 0 := by
            constructor
            · intro h; ext; rw [h]; rfl
            · intro h
              exact InducedCategory.hom_ext (ModuleCat.Hom.ext h)
          rw [h_ext]
          apply LinearMap.ext
          intro x
          have h_mem : f.hom.hom.hom' x ∈ LinearMap.range f.hom.hom.hom' := LinearMap.mem_range_self f.hom.hom.hom' x
          rw [h_range, Submodule.mem_bot] at h_mem
          exact h_mem
        contradiction
      · have h_range : (rangeSubrepresentation Y f).toSubmodule = ⊤ := congr_arg Subrepresentation.toSubmodule h_top
        change LinearMap.range f.hom.hom.hom' = ⊤ at h_range
        have h_surj : Function.Surjective f.hom.hom.hom' := by
          rw [LinearMap.range_eq_top] at h_range
          exact h_range
        rw [isIso_iff_bijective_FDRep]
        exact ⟨h_inj, h_surj⟩

/-- Simplicity of `V_rep` is transferred from `FDRep.of (unitaryRep d)` along `iso_E`. -/
noncomputable instance simple_V_rep [Module.Finite ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))] :
    Simple (V_rep : FDRep ℂ (UnitaryGroup d)) :=
  Simple.of_iso iso_E

/-- Schur's Lemma for endomorphisms of a simple representation. -/
lemma endomorphism_is_scalar {G : Type} [Group G] (V : FDRep ℂ G) [Simple V] (f : V ⟶ V) : ∃ scalar : ℂ, f = scalar • 𝟙 V := by
  obtain ⟨scalar, h_eq⟩ := endomorphism_simple_eq_smul_id ℂ f
  use scalar
  exact h_eq.symm

/-- **Commutant of first order unitaries on the 1-fold tensor power** (Blueprint Theorem):
The set of endomorphisms of the 1-fold tensor power `⨂[ℂ]^1 𝓗[d]` that commute with the 1-fold
tensor representation of the unitary group consists exactly of scalar multiples of the identity. -/
theorem commutant_unitary_eq_scalar_tensor
    [Module.Finite ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))] :
    {M : (⨂[ℂ]^1 (FiniteHilbertSpace d)) →ₗ[ℂ] (⨂[ℂ]^1 (FiniteHilbertSpace d)) |
      ∀ U : UnitaryGroup d, M.comp (glPow U.toLinearMap) = (glPow U.toLinearMap).comp M} =
    {M | ∃ (scalar : ℂ), M = scalar • LinearMap.id} := by
  ext M
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h_comm
    let f_hom : V_rep ⟶ V_rep := {
      hom := ⟨ModuleCat.ofHom M⟩
      comm := fun U ↦ by
        apply InducedCategory.hom_ext
        apply ModuleCat.Hom.ext
        exact h_comm U
    }
    obtain ⟨scalar, h_eq⟩ := endomorphism_is_scalar V_rep f_hom
    use scalar
    have h_eq_map : f_hom.hom.hom.hom' = (scalar • 𝟙 V_rep).hom.hom.hom' := by
      rw [h_eq]
    exact h_eq_map
  · rintro ⟨scalar, rfl⟩ U
    rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]

end LeanHaar
