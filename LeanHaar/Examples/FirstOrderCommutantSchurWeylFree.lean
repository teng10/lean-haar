import LeanHaar.HilbertSpace
import LeanHaar.UnitaryPower
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Abstract proof of the commutant of the first-order unitary group

This file provides a Schur-Weyl-free proof that the commutant of the first-order unitary group
acting on a finite Hilbert space consists only of scalar multiples of the identity.

The proof proceeds by showing that the natural representation of the unitary group is irreducible,
and then applying Schur's Lemma.

Irreducibility is proven by showing that unitaries act transitively on the unit sphere, which
implies that any non-zero invariant subspace must be the entire space.
-/

namespace LeanHaar

open Representation Matrix FiniteDimensional Module RCLike

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The natural representation of the unitary group on the finite Hilbert space. -/
noncomputable def unitaryRep (d : Type*) [Fintype d] [DecidableEq d] :
    Representation ℂ (Matrix.unitaryGroup d ℂ) (FiniteHilbertSpace d) where
  toFun U := Matrix.toLin (FiniteHilbertSpace.basisFun d).toBasis (FiniteHilbertSpace.basisFun d).toBasis (U : Matrix d d ℂ)
  map_one' := by
    apply LinearMap.ext; intro v
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, Matrix.toLin_one, LinearMap.id_apply]
    rfl
  map_mul' U V := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.comp_apply, MonoidHom.toFun_eq_coe, Matrix.toLin_mul (FiniteHilbertSpace.basisFun d).toBasis, LinearMap.comp_apply]
    rfl

/-- Unitary matrices act transitively on vectors of the same norm in a finite Hilbert space. -/
lemma exists_unitary_apply_eq (x y : FiniteHilbertSpace d) (h : ‖x‖ = ‖y‖) :
    ∃ U : Matrix.unitaryGroup d ℂ, unitaryRep d U x = y := by
  by_cases hx : x = 0
  · use 1
    have hy : y = 0 := by
      rw [hx] at h
      simp only [norm_zero] at h
      exact norm_eq_zero.mp h.symm
    simp [hx, hy]
  · have hy : y ≠ 0 := by
      intro hy
      rw [hy] at h
      simp only [norm_zero] at h
      exact hx (norm_eq_zero.mp h)
    let cx : ℂ := (‖x‖ : ℂ)⁻¹
    let cy : ℂ := (‖y‖ : ℂ)⁻¹
    let x' := cx • x
    let y' := cy • y
    have hx' : ‖x'‖ = 1 := by
      rw [norm_smul, norm_inv]
      have : ‖(‖x‖ : ℂ)‖ = ‖x‖ := by rw [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]
      rw [this, inv_mul_cancel (norm_ne_zero_iff.mpr hx)]
    have hy' : ‖y'‖ = 1 := by
      rw [norm_smul, norm_inv]
      have : ‖(‖y‖ : ℂ)‖ = ‖y‖ := by rw [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg y)]
      rw [this, inv_mul_cancel (norm_ne_zero_iff.mpr hy)]
    let sx : Set (FiniteHilbertSpace d) := {x'}
    let sy : Set (FiniteHilbertSpace d) := {y'}
    have hsx : Orthonormal ℂ ((↑) : sx → FiniteHilbertSpace d) := by
      constructor
      · rintro ⟨v, hv⟩; simp at hv; rw [hv]; exact hx'
      · rintro ⟨v1, hv1⟩ ⟨v2, hv2⟩ h; simp at hv1 hv2; exact (h (by rw [hv1, hv2])).elim
    have hsy : Orthonormal ℂ ((↑) : sy → FiniteHilbertSpace d) := by
      constructor
      · rintro ⟨v, hv⟩; simp at hv; rw [hv]; exact hy'
      · rintro ⟨v1, hv1⟩ ⟨v2, hv2⟩ h; simp at hv1 hv2; exact (h (by rw [hv1, hv2])).elim
    let n := finrank ℂ (FiniteHilbertSpace d)
    haveI : Nontrivial (FiniteHilbertSpace d) := nontrivial_iff_exists_ne 0 |>.mpr ⟨x, hx⟩
    obtain ⟨ux, Bx, hsux, hBx⟩ := hsx.exists_orthonormalBasis_extension
    obtain ⟨uy, By, hsuy, hBy⟩ := hsy.exists_orthonormalBasis_extension
    let ex : ux ≃ d := Fintype.equivOfCardEq (by rw [Bx.finrank, ← FiniteHilbertSpace.linearEquivEuclidean.finrank_eq, finrank_euclideanSpace])
    let ey : uy ≃ d := Fintype.equivOfCardEq (by rw [By.finrank, ← FiniteHilbertSpace.linearEquivEuclidean.finrank_eq, finrank_euclideanSpace])
    let Bx' := Bx.reindex ex
    let By' := By.reindex ey
    let kx : ux := ⟨x', hsux (Set.mem_singleton x')⟩
    let ky : uy := ⟨y', hsuy (Set.mem_singleton y')⟩
    let σ := Equiv.swap (ex kx) (ey ky)
    let Bx'' := Bx'.reindex σ
    let f := Bx''.repr.trans By'.repr.symm
    let M := LinearMap.toMatrix (FiniteHilbertSpace.basisFun d).toBasis (FiniteHilbertSpace.basisFun d).toBasis f.toLinearMap
    have hM : M ∈ Matrix.unitaryGroup d ℂ := by
      rw [Matrix.mem_unitaryGroup_iff']
      let f_equiv : FiniteHilbertSpace d ≃ₗᵢ[ℂ] FiniteHilbertSpace d := f
      exact LinearIsometryEquiv.toMatrix_mem_unitaryGroup f_equiv (FiniteHilbertSpace.basisFun d) (FiniteHilbertSpace.basisFun d)
    use ⟨M, hM⟩
    dsimp [unitaryRep]
    rw [toLin_toMatrix]
    have hfx : f x' = y' := by
      apply By'.repr.injective
      simp only [f, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
      rw [OrthonormalBasis.repr_self By' ky]
      have : Bx''.repr x' = EuclideanSpace.single (ey ky) 1 := by
        apply Bx''.repr.injective
        simp only [LinearIsometryEquiv.apply_symm_apply, Bx'', OrthonormalBasis.reindex_apply,
          Equiv.swap_apply_right, Bx', OrthonormalBasis.repr_self]
        congr
        simp [kx]
        rw [hBx]
        rfl
      rw [this]
    calc
      f x = f (‖x‖ • x') := by
        congr
        simp [x', smul_inv_smul₀ (norm_ne_zero_iff.mpr hx)]
      _ = ‖x‖ • f x' := by rw [map_smul]
      _ = ‖x‖ • y' := by rw [hfx]
      _ = ‖y‖ • (‖y‖⁻¹ • y) := by
        congr
        · exact h
        · simp [y', smul_inv_smul₀ (norm_ne_zero_iff.mpr hy)]
      _ = y := by rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr hy)]

/-- The natural representation is irreducible if the dimension is at least 1. -/
theorem unitaryRep_irreducible [Nonempty d] :
    IsIrreducible (unitaryRep d) := by
  let ρ := unitaryRep d
  rw [irreducible_iff_isSimpleModule_asModule]
  letI : Module (MonoidAlgebra ℂ ↥(Matrix.unitaryGroup d ℂ)) ρ.asModule :=
    Representation.asModule.module ρ
  refine' { nontrivial := _, simple := { nontrivial := _, eq_bot_or_eq_top := _ } }
  · rw [asModule_top_eq_top]
    infer_instance
  · rw [asModule_bot_eq_bot, asModule_top_eq_top]
    intro h
    have : finrank ℂ (FiniteHilbertSpace d) > 0 := by
      simp [FiniteHilbertSpace.linearEquivEuclidean.finrank_eq, finrank_euclideanSpace, Fintype.card_pos]
    have : finrank ℂ (⊥ : Submodule ℂ (FiniteHilbertSpace d)) = 0 := by
      simp [Submodule.finrank_bot]
    rw [← h] at this
    linarith
  · intro W
    by_cases hW0 : W = ⊥
    · left; exact hW0
    · right
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      apply Submodule.eq_top_iff'.mpr
      intro v
      by_cases hv0 : v = 0
      · rw [hv0]; exact W.zero_mem
      · let c : ℂ := ‖v‖ / ‖w‖
        let w' := c • w
        have hnorm : ‖w'‖ = ‖v‖ := by
          rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
          field_simp [norm_ne_zero_iff.mpr hw0]
        obtain ⟨U, hU⟩ := exists_unitary_apply_eq w' v hnorm
        have hw'W : w' ∈ W := Submodule.smul_mem W c hwW
        have h_smul : (MonoidAlgebra.of ℂ _ U) • (w' : ρ.asModule) = (ρ U w' : ρ.asModule) := rfl
        rw [← h_smul, hU]
        exact Submodule.smul_mem W (MonoidAlgebra.of ℂ _ U) hw'W

/-- The commutant of the first-order unitary group consists of scalar multiples of the identity. -/
theorem commutant_unitary_eq_scalars [Nonempty d] (M : Matrix d d ℂ) :
    (∀ U : Matrix d d ℂ, U ∈ Matrix.unitaryGroup d ℂ → M * U = U * M) ↔
    ∃ (s : ℂ), M = s • (1 : Matrix d d ℂ) := by
  let ρ := unitaryRep d
  let B := (FiniteHilbertSpace.basisFun d).toBasis

  have h_comm : (∀ U : Matrix d d ℂ, U ∈ Matrix.unitaryGroup d ℂ → M * U = U * M) ↔
      ∃ f : IntertwiningMap ρ ρ, f.toLinearMap = Matrix.toLin B B M := by
    constructor
    · intro h
      let f_lin : FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d := Matrix.toLin B B M
      use { toLinearMap := f_lin,
            isIntertwining' := fun U => by
              apply LinearMap.ext; intro v
              simp only [LinearMap.comp_apply]
              let U_mat := (U : Matrix d d ℂ)
              have h_mat := h U_mat U.prop
              have h1 := Matrix.toLin_mul B B B M U_mat
              have h2 := Matrix.toLin_mul B B B U_mat M
              dsimp [unitaryRep] at *
              rw [← h1, ← h2, h_mat]
          }
      rfl
    · rintro ⟨f, hf⟩ U hU
      apply (Matrix.toLin B B).injective
      rw [Matrix.toLin_mul B B B, Matrix.toLin_mul B B B]
      rw [← hf]
      apply LinearMap.ext; intro v
      exact f.isIntertwining ⟨U, hU⟩ v

  rw [h_comm]
  haveI : IsIrreducible ρ := unitaryRep_irreducible
  let Schur := IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨s, hs⟩ := Schur.2 f
    use s
    apply (Matrix.toLin B B).injective
    rw [hf, ← hs]
    simp only [IntertwiningMap.algebraMap_apply,
      IntertwiningMap.id_toLinearMap, LinearMap.toMatrix_id,
      LinearMap.smul_apply, IntertwiningMap.smul_toLinearMap,
      IntertwiningMap.id_apply, LinearMap.id_apply, Matrix.toLin_one]
    rw [(Matrix.toLin B B).map_smul]
    rfl
  · rintro ⟨s, hs⟩
    use s • IntertwiningMap.id ρ
    simp only [hs, IntertwiningMap.smul_toLinearMap, IntertwiningMap.id_toLinearMap,
      Matrix.toLin_one]
    rw [(Matrix.toLin B B).map_smul]

end LeanHaar
