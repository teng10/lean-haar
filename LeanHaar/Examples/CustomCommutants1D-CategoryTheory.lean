import LeanHaar.HilbertSpace
import LeanHaar.SchurWeylAbstract
import LeanHaar.Examples.«Commutants1D-GroupRepresentations»
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.FDRep
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Commutant of the first order unitary group on the 1-fold tensor power — category theory version

This file formalizes the result stating that any endomorphism of the 1-fold tensor power
of the Hilbert space `⨂[ℂ]^1 𝓗[d]` that commutes with the 1-fold tensor representation of the
unitary group is a scalar multiple of the identity.

We prove this using the category-theoretic Schur's Lemma:
1. Show that the natural unitary representation on `𝓗[d]` is a simple object in `FDRep`.
2. Using the canonical isomorphism between the 1-fold tensor representation and the natural representation,
   any equivariant map on the 1-fold tensor representation corresponds to an endomorphism of the simple representation.
3. Apply the category-theoretic Schur's Lemma to conclude that the endomorphism (and thus the original map)
   is a scalar multiple of the identity.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Representation
open Module
open scoped TensorProduct
open LeanHaar.SchurWeylAbstract
open LeanHaar

variable {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The natural representation of the unitary group on `𝓗[d]` is a simple object in the category `FDRep`. -/
noncomputable instance simple_unitaryRep : Simple (FDRep.of (unitaryRep d)) where
  mono_isIso_iff_nonzero {Y} f h_mono := by
    constructor
    · intro h_iso h_zero
      have h_comp : inv f ≫ f = 0 := by
        have h_congr := congrArg (fun g => inv f ≫ g) h_zero
        dsimp only at h_congr
        have h_zero_comp : inv f ≫ (0 : Y ⟶ FDRep.of (unitaryRep d)) = 0 := Limits.comp_zero
        rw [h_zero_comp] at h_congr
        exact h_congr
      have h_inv := IsIso.inv_hom_id f
      rw [h_comp] at h_inv
      have h_id : 𝟙 (FDRep.of (unitaryRep d)) = 0 := h_inv.symm
      have h_id_zero : (forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map (𝟙 (FDRep.of (unitaryRep d))) = 0 := by
        rw [h_id, Functor.map_zero]
      have h_id_zero_hom : ((forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map (𝟙 (FDRep.of (unitaryRep d)))).hom = 0 := by
        rw [h_id_zero]
        rfl
      obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (FiniteHilbertSpace d))
      have h_apply := congrArg (fun (f_map : Representation.IntertwiningMap (unitaryRep d) (unitaryRep d)) => f_map (x - y)) h_id_zero_hom
      dsimp only at h_apply
      have h_lhs : ((forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map (𝟙 (FDRep.of (unitaryRep d)))).hom (x - y) = x - y := rfl
      have h_rhs : (0 : Representation.IntertwiningMap (unitaryRep d) (unitaryRep d)) (x - y) = 0 := rfl
      have h_apply' : x - y = 0 := Eq.trans h_lhs.symm (Eq.trans h_apply h_rhs)
      exact hxy (sub_eq_zero.mp h_apply')
    · intro h_nz
      let Y_rep := (forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).obj Y
      let f_rep := (forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map f
      have h_mono_rep : Mono f_rep := Functor.map_mono (forget₂ _ _) f
      have h_inj : Function.Injective f_rep.hom := (Rep.mono_iff_injective f_rep).mp h_mono_rep
      let sub_rep : Subrepresentation (unitaryRep d) := f_rep.hom.range
      letI : IsSimpleOrder (Subrepresentation (unitaryRep d)) := unitary_irreducible
      obtain (h_bot | h_top) := IsSimpleOrder.eq_bot_or_eq_top sub_rep
      · exfalso
        have h_zero : f_rep = 0 := by
          ext y
          let v : FiniteHilbertSpace d := f_rep.hom y
          have h_mem : v ∈ sub_rep := ⟨y, rfl⟩
          have h_mem_sub : v ∈ sub_rep.toSubmodule := h_mem
          have h_bot_sub : sub_rep.toSubmodule = ⊥ := by
            rw [h_bot]
            rfl
          rw [h_bot_sub] at h_mem_sub
          rw [Submodule.mem_bot] at h_mem_sub
          have h1 : f_rep.hom.toLinearMap y = v := rfl
          have h2 : v = 0 := h_mem_sub
          have h3 : (0 : FiniteHilbertSpace d) = (0 : (forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).obj Y ⟶ (forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).obj (FDRep.of (unitaryRep d))).hom.toLinearMap y := rfl
          exact Eq.trans h1 (Eq.trans h2 h3)
        have h_f_zero : f = 0 := by
          apply (forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map_injective
          exact h_zero
        exact h_nz h_f_zero
      · have h_surj : Function.Surjective f_rep.hom.toLinearMap := by
          intro (x : FiniteHilbertSpace d)
          have h_mem : x ∈ sub_rep := by
            rw [h_top]
            exact Submodule.mem_top
          exact h_mem
        have h_bij : Function.Bijective f_rep.hom.toLinearMap := ⟨h_inj, h_surj⟩
        let e_linear := LinearEquiv.ofBijective f_rep.hom.toLinearMap h_bij
        have he (g : UnitaryGroup d) : e_linear.toLinearMap.comp (Y_rep.ρ g) = (unitaryRep d g).comp e_linear.toLinearMap := by
          ext y
          simp only [LinearMap.coe_comp, Function.comp_apply]
          change f_rep.hom (Y_rep.ρ g y) = unitaryRep d g (f_rep.hom y)
          exact Rep.hom_comm_apply f_rep g y
        let e_equiv : Y_rep.ρ.Equiv (unitaryRep d) := Representation.Equiv.mk e_linear he
        let i_iso : Y_rep ≅ Rep.of (unitaryRep d) := Rep.mkIso e_equiv
        have h_eq : i_iso.hom = f_rep := by
          ext
          rfl
        haveI : IsIso f_rep := by
          rw [← h_eq]
          infer_instance
        exact isIso_of_fully_faithful (forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))) f

/-- Schur's lemma in category theory: any endomorphism of a simple object is a scalar multiple of the identity. -/
lemma endomorphism_is_scalar {G : Type*} [Group G] (V : FDRep ℂ G) [Simple V] (f : V ⟶ V) :
    ∃ scalar : ℂ, f = scalar • 𝟙 V := by
  have h_dim : finrank ℂ (V ⟶ V) = 1 := by
    have h_schur := FDRep.finrank_hom_simple_simple V V
    rw [if_pos (Nonempty.intro (Iso.refl V))] at h_schur
    exact h_schur
  have hid : 𝟙 V ≠ 0 := id_nonzero V
  obtain ⟨scalar, h_eq⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 V) hid).mp h_dim f
  use scalar
  exact h_eq.symm

/-- Canonical linear equivalence between the 1-fold tensor power of `𝓗[d]` and `𝓗[d]`. -/
noncomputable def E :
    (⨂[ℂ]^1 (FiniteHilbertSpace d)) ≃ₗ[ℂ] FiniteHilbertSpace d :=
  PiTensorProduct.subsingletonEquiv (0 : Fin 1)

omit [Nonempty d] in
lemma E_toLinearMap_comp_symm :
    E.toLinearMap.comp E.symm.toLinearMap = (LinearMap.id : FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d) := by
  ext; simp [E]

omit [Nonempty d] in
lemma E_symm_toLinearMap_comp :
    E.symm.toLinearMap.comp E.toLinearMap = (LinearMap.id : (⨂[ℂ]^1 (FiniteHilbertSpace d)) →ₗ[ℂ] (⨂[ℂ]^1 (FiniteHilbertSpace d))) := by
  ext; simp [E]

omit [Nonempty d] in
lemma E_comp_glPow (A : Module.End ℂ (FiniteHilbertSpace d)) :
    E.toLinearMap.comp (glPow A : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))) = A.comp E.toLinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, glPow_tprod]
  unfold E
  simp only [PiTensorProduct.subsingletonEquiv_apply_tprod]

omit [Nonempty d] in
lemma glPow_comp_E_symm (A : Module.End ℂ (FiniteHilbertSpace d)) :
    (glPow A : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))).comp E.symm.toLinearMap = E.symm.toLinearMap.comp A := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  unfold E
  rw [PiTensorProduct.subsingletonEquiv_symm_apply' (0 : Fin 1) x]
  simp only [glPow_tprod]
  rw [PiTensorProduct.subsingletonEquiv_symm_apply' (0 : Fin 1) (A x)]

/-- **Commutant of first order unitaries on the 1-fold tensor power** (proven via the Category Theory framework):
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
    -- Define the 1D operator corresponding to M
    let M_1D := E.toLinearMap.comp (M.comp E.symm.toLinearMap)
    -- Prove that M_1D commutes with U.toLinearMap
    have h_comm_1D (U : UnitaryGroup d) : M_1D.comp U.toLinearMap = U.toLinearMap.comp M_1D := by
      ext x
      simp only [M_1D, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      have h1 := LinearMap.congr_fun (glPow_comp_E_symm U.toLinearMap) x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h1
      rw [← h1]
      have h_comm_val := LinearMap.congr_fun (h_comm U) (E.symm x)
      simp only [LinearMap.coe_comp, Function.comp_apply] at h_comm_val
      rw [h_comm_val]
      have h2 := LinearMap.congr_fun (E_comp_glPow U.toLinearMap) (M (E.symm x))
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h2
      rw [h2]
    -- Construct the morphism in FDRep
    let f_rep : Rep.of (unitaryRep d) ⟶ Rep.of (unitaryRep d) :=
      Rep.ofHom ⟨M_1D, h_comm_1D⟩
    let f : FDRep.of (unitaryRep d) ⟶ FDRep.of (unitaryRep d) :=
      FDRep.forget₂HomLinearEquiv _ _ f_rep
    -- Apply the category theory version of Schur's Lemma
    obtain ⟨scalar, h_eq⟩ := endomorphism_is_scalar (FDRep.of (unitaryRep d)) f
    use scalar
    -- Reconstruct M from M_1D and show it is a scalar multiple of the identity
    have h_M : M = E.symm.toLinearMap.comp (M_1D.comp E.toLinearMap) := by
      rw [← LinearMap.comp_assoc]
      dsimp [M_1D]
      rw [← LinearMap.comp_assoc, E_symm_toLinearMap_comp, LinearMap.id_comp,
        LinearMap.comp_assoc, E_symm_toLinearMap_comp, LinearMap.comp_id]
    rw [h_M]
    -- Extract M_1D = scalar • id from f = scalar • 𝟙 V
    have h_M_1D_eq : M_1D = scalar • LinearMap.id := by
      apply LinearMap.ext
      intro x
      have h1 : M_1D x = f_rep.hom x := rfl
      have h2 : f_rep.hom x = ((forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map f).hom x := rfl
      have h3 : ((forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map f).hom x = ((forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map (scalar • 𝟙 (FDRep.of (unitaryRep d)))).hom x := by rw [h_eq]
      have h4 : ((forget₂ (FDRep ℂ (UnitaryGroup d)) (Rep ℂ (UnitaryGroup d))).map (scalar • 𝟙 (FDRep.of (unitaryRep d)))).hom x = scalar • x := rfl
      rw [h1, h2, h3, h4]
      rfl
    rw [h_M_1D_eq]
    simp only [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp]
    rw [E_symm_toLinearMap_comp]
  · rintro ⟨scalar, rfl⟩ U
    rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
