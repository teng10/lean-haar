import LeanHaar.HilbertSpace
import LeanHaar.SchurWeylAbstract
import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# Commutant of the first order unitary group via Schur–Weyl Duality

This file proves the 1D commutant theorem: any endomorphism of the finite-dimensional
Hilbert space `𝓗[d]` that commutes with all unitary operators is a scalar multiple of the identity.

Unlike `Commutants1D.lean`, which uses the irreducibility of the unitary group representation
and Schur's Lemma directly, this file derives the result as the $k=1$ case of the abstract
Schur–Weyl duality formalized in `SchurWeylAbstract.lean`.

## Main results

* `LeanHaar.commutant_unitary_eq_scalar` : The commutant of the unitary group is the set of
  scalar multiples of the identity.
-/

noncomputable section

namespace LeanHaar

open scoped TensorProduct
open SchurWeylAbstract

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The symmetric group on `Fin 1` is a subsingleton. -/
instance : Subsingleton (Equiv.Perm (Fin 1)) := by
  constructor
  intro f g
  ext x
  have h1 : f x = (0 : Fin 1) := Subsingleton.elim (f x) 0
  have h2 : g x = (0 : Fin 1) := Subsingleton.elim (g x) 0
  rw [h1, h2]

/-- Canonical linear equivalence between the 1-fold tensor power of `𝓗[d]` and `𝓗[d]`. -/
def E (d : Type*) [Fintype d] [DecidableEq d] :
    (⨂[ℂ]^1 (FiniteHilbertSpace d)) ≃ₗ[ℂ] FiniteHilbertSpace d :=
  PiTensorProduct.subsingletonEquiv (0 : Fin 1)

/-- Evaluating `E` on `E.symm` yields the identity. -/
lemma E_toLinearMap_comp_symm :
    (E d).toLinearMap.comp (E d).symm.toLinearMap = LinearMap.id := by
  ext; simp [E]

/-- Evaluating `E.symm` on `E` yields the identity. -/
lemma E_symm_toLinearMap_comp :
    (E d).symm.toLinearMap.comp (E d).toLinearMap = LinearMap.id := by
  ext; simp [E]

/-- Associativity relation for composition of `E` and `E.symm`. -/
lemma E_toLinearMap_comp_symm_assoc (f : Module.End ℂ (FiniteHilbertSpace d)) :
    (E d).toLinearMap ∘ₗ ((E d).symm.toLinearMap ∘ₗ f) = f := by
  rw [← LinearMap.comp_assoc, E_toLinearMap_comp_symm, LinearMap.id_comp]

/-- Associativity relation for composition of `E.symm` and `E`. -/
lemma E_symm_toLinearMap_comp_assoc (f : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))) :
    (E d).symm.toLinearMap ∘ₗ ((E d).toLinearMap ∘ₗ f) = f := by
  rw [← LinearMap.comp_assoc, E_symm_toLinearMap_comp, LinearMap.id_comp]

/-- Conjugation map taking an operator on `𝓗[d]` to the 1-fold tensor power. -/
def conjSymm (M : Module.End ℂ (FiniteHilbertSpace d)) :
    Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d)) :=
  (E d).symm.toLinearMap.comp (M.comp (E d).toLinearMap)

/-- Inverse conjugation map taking an operator on the 1-fold tensor power to `𝓗[d]`. -/
def conj (M : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))) :
    Module.End ℂ (FiniteHilbertSpace d) :=
  (E d).toLinearMap.comp (M.comp (E d).symm.toLinearMap)

/-- Conjugation cancels `conjSymm`. -/
lemma conj_conjSymm (M : Module.End ℂ (FiniteHilbertSpace d)) : conj (conjSymm M) = M := by
  simp only [conj, conjSymm, LinearMap.comp_assoc]
  rw [E_toLinearMap_comp_symm_assoc, E_toLinearMap_comp_symm]
  simp only [LinearMap.comp_id]

/-- `conjSymm` cancels conjugation. -/
lemma conjSymm_conj (M : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))) : conjSymm (conj M) = M := by
  simp only [conj, conjSymm, LinearMap.comp_assoc]
  rw [E_symm_toLinearMap_comp_assoc, E_symm_toLinearMap_comp]
  simp only [LinearMap.comp_id]

/-- Evaluation of `E` on `glPow` of an operator. -/
lemma E_comp_glPow (A : Module.End ℂ (FiniteHilbertSpace d)) :
    (E d).toLinearMap.comp (glPow A) = A.comp (E d).toLinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, glPow_tprod]
  unfold E
  simp only [PiTensorProduct.subsingletonEquiv_apply_tprod]

/-- Evaluation of `glPow` on `E.symm` of an operator. -/
lemma glPow_comp_E_symm (A : Module.End ℂ (FiniteHilbertSpace d)) :
    (glPow A).comp (E d).symm.toLinearMap = (E d).symm.toLinearMap.comp A := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  unfold E
  rw [PiTensorProduct.subsingletonEquiv_symm_apply' (0 : Fin 1) x]
  simp only [glPow_tprod]
  rw [PiTensorProduct.subsingletonEquiv_symm_apply' (0 : Fin 1) (A x)]

/-- Left conjugation of `glPow` by `conjSymm`. -/
lemma conjSymm_comp_glPow (M : Module.End ℂ (FiniteHilbertSpace d))
    (A : Module.End ℂ (FiniteHilbertSpace d)) :
    (conjSymm M).comp (glPow A) =
      (E d).symm.toLinearMap.comp ((M.comp A).comp (E d).toLinearMap) := by
  simp only [conjSymm, LinearMap.comp_assoc]
  rw [E_comp_glPow]

/-- Right conjugation of `glPow` by `conjSymm`. -/
lemma glPow_comp_conjSymm (M : Module.End ℂ (FiniteHilbertSpace d))
    (A : Module.End ℂ (FiniteHilbertSpace d)) :
    (glPow A).comp (conjSymm M) =
      (E d).symm.toLinearMap.comp ((A.comp M).comp (E d).toLinearMap) := by
  simp only [conjSymm, ← LinearMap.comp_assoc]
  rw [glPow_comp_E_symm]

/-- The unitary group of the finite Hilbert space `𝓗[d]`. -/
abbrev UnitaryGroup (d : Type*) [Fintype d] [DecidableEq d] :=
  FiniteHilbertSpace d ≃ₗᵢ[ℂ] FiniteHilbertSpace d

/-- Equivariance is preserved under conjugation. -/
lemma conjSymm_commute (M : Module.End ℂ (FiniteHilbertSpace d)) (U : UnitaryGroup d) :
    (conjSymm M).comp (glPow U.toLinearMap) = (glPow U.toLinearMap).comp (conjSymm M) ↔
      M.comp U.toLinearMap = U.toLinearMap.comp M := by
  constructor
  · intro h
    -- Take the conjugation of both sides
    have h_conj : conj ((conjSymm M).comp (glPow U.toLinearMap)) =
                  conj ((glPow U.toLinearMap).comp (conjSymm M)) := by rw [h]
    -- Rewrite the inner terms using the E-glPow conjugation lemmas
    rw [conjSymm_comp_glPow, glPow_comp_conjSymm] at h_conj
    simp only [conj, LinearMap.comp_assoc] at h_conj
    -- Apply the associativity helper lemmas to cancel E and E.symm on the left
    rw [E_toLinearMap_comp_symm_assoc, E_toLinearMap_comp_symm_assoc] at h_conj
    -- Cancel E and E.symm on the right
    rw [E_toLinearMap_comp_symm] at h_conj
    simp only [LinearMap.comp_id] at h_conj
    exact h_conj
  · intro h
    rw [conjSymm_comp_glPow, glPow_comp_conjSymm, h]

/-- The permutation algebra for `k = 1` is spanned by the identity operator. -/
lemma permSpan_one :
    permSpan (V := FiniteHilbertSpace d) (k := 1) =
      Submodule.span ℂ {(LinearMap.id : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d)))} := by
  simp only [permSpan]
  congr 1
  ext f
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨π, rfl⟩
    -- The symmetric group on 1 element contains only the identity permutation
    have : π = 1 := Subsingleton.elim π 1
    rw [this]
    exact map_one permRep
  · rintro rfl
    refine ⟨1, ?_⟩
    exact map_one permRep

/-- The centralizer of a submodule span is the centralizer of its generators. -/
lemma centralizer_span (S : Set (Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d)))) :
    Set.centralizer (Submodule.span ℂ S : Set (Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d)))) =
      Set.centralizer S := by
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

/-- Conjugation maps scalar multiples of the identity to scalar multiples of the identity. -/
lemma conjSymm_eq_smul_id_iff (M : Module.End ℂ (FiniteHilbertSpace d)) (scalar : ℂ) :
    conjSymm M = scalar • (LinearMap.id : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))) ↔
      M = scalar • (LinearMap.id : Module.End ℂ (FiniteHilbertSpace d)) := by
  constructor
  · intro h
    have h_conj : conj (conjSymm M) =
      conj (scalar • (LinearMap.id : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d)))) := by rw [h]
    rw [conj_conjSymm] at h_conj
    rw [h_conj]
    simp only [conj, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp,
      E_toLinearMap_comp_symm]
  · rintro rfl
    simp only [conjSymm, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp,
      E_symm_toLinearMap_comp]


/-- **Commutant of first order unitaries** (Blueprint Theorem):
The set of endomorphisms of `𝓗[d]` that commute with all unitaries consists exactly of
scalar multiples of the identity. -/
theorem commutant_unitary_eq_scalar :
    {M : FiniteHilbertSpace d →ₗ[ℂ] FiniteHilbertSpace d |
      ∀ U : UnitaryGroup d, M.comp U.toLinearMap = U.toLinearMap.comp M} =
    {M | ∃ (scalar : ℂ), M = scalar • LinearMap.id} := by
  ext M
  simp only [Set.mem_setOf_eq]
  -- Instantiate the abstract Schur-Weyl Duality for k = 1.
  -- This equates permSpan and the centralizer of unitaryTensorSpan.
  have h_duality := permSpan_eq_centralizer_unitaryTensorSpan (W := FiniteHilbertSpace d) (k := 1)

  -- Rewrite using the k = 1 identifications.
  -- permSpan is span(id), and the centralizer of unitaryTensorSpan is the centralizer of the range of glPow.
  rw [permSpan_one, unitaryTensorSpan, centralizer_span] at h_duality

  -- Establish that M commutes with all U iff conjSymm M commutes with all glPow U.
  have h_comm : (∀ U : UnitaryGroup d, M.comp U.toLinearMap = U.toLinearMap.comp M) ↔
                (∀ U : UnitaryGroup d,
                  (conjSymm M).comp (glPow U.toLinearMap) =
                    (glPow U.toLinearMap).comp (conjSymm M)) := by
    constructor
    · intro h U
      rw [conjSymm_commute]
      exact h U
    · intro h U
      rw [← conjSymm_commute]
      exact h U
  rw [h_comm]

  -- Express the commutation relation as membership in the centralizer set.
  have h_cent : (∀ U : UnitaryGroup d,
                  (conjSymm M).comp (glPow U.toLinearMap) =
                    (glPow U.toLinearMap).comp (conjSymm M)) ↔
                (conjSymm M ∈ Set.centralizer
                  (Set.range (fun U : UnitaryGroup d => glPow U.toLinearMap))) := by
    simp only [Set.mem_centralizer_iff, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    constructor
    · intro h U
      have hU := h U
      exact hU.symm
    · intro h U
      have hU := h U
      exact hU.symm
  rw [h_cent]

  -- Apply Schur-Weyl duality to transition from the centralizer to the permutation span.
  have h_mem : conjSymm M ∈ Set.centralizer
                 (Set.range (fun U : UnitaryGroup d => glPow U.toLinearMap)) ↔
               conjSymm M ∈ ↑(Submodule.span ℂ
                 {(LinearMap.id : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d)))}) := by
    rw [← h_duality]
    rfl
  rw [h_mem]

  -- Bridge the span of id on the 1-fold power to the scalar multiples on H[d].
  have h_span : (conjSymm M ∈ ↑(Submodule.span ℂ
                  {(LinearMap.id : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d)))})) ↔
                (∃ scalar : ℂ, M = scalar • LinearMap.id) := by
    have h_def : (conjSymm M ∈ ↑(Submodule.span ℂ
                   {(LinearMap.id : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d)))})) ↔
                 (conjSymm M ∈ (Submodule.span ℂ
                   {(LinearMap.id : Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d)))} :
                     Submodule ℂ (Module.End ℂ (⨂[ℂ]^1 (FiniteHilbertSpace d))))) := Iff.rfl
    rw [h_def, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨scalar, h⟩
      use scalar
      have h_symm := h.symm
      rwa [conjSymm_eq_smul_id_iff] at h_symm
    · rintro ⟨scalar, rfl⟩
      refine ⟨scalar, ?_⟩
      symm
      rw [conjSymm_eq_smul_id_iff]
  rw [h_span]

end LeanHaar
