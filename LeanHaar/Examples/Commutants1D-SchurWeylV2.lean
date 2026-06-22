import LeanHaar.HilbertSpace
import LeanHaar.SchurWeylAbstract
import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# Commutant of the first order unitary group via Schur–Weyl Duality with prior assumptions

This file proves the theorem "Assume Tensor Power of 1 is Known" from the blueprint
(subsections/examples/commutants.tex).

It states that the commutant of the 1-fold tensor power of unitaries `glPow U.toLinearMap`
on `⨂[ℂ]^1 𝓗[d]` consists exactly of the scalar multiples of the identity operator.
This file is added to compare the difference between having to prove that $MU = MU^{⊗1}$ and already going into the proof with this assumption.
This specific file is more representative of the expected steps for proving the claim holds true for any tensor power $k$.


Unlike `Commutants1D-SchurWeyl.lean`, this proof lives entirely on the 1-fold tensor power space
and does not require translating the result back to the base Hilbert space `𝓗[d]`.

## Main results

* `LeanHaar.commutant_unitary_eq_scalar` : The commutant of the 1-fold tensor power of unitaries
  on the tensor power space is the set of scalar multiples of the identity.
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

/-- The unitary group of the finite Hilbert space `𝓗[d]`. -/
abbrev UnitaryGroup (d : Type*) [Fintype d] [DecidableEq d] :=
  FiniteHilbertSpace d ≃ₗᵢ[ℂ] FiniteHilbertSpace d

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

/-- **Assume Tensor Power of 1 is Known** (Blueprint Theorem):
The set of endomorphisms of `⨂[ℂ]^1 𝓗[d]` that commute with the 1-fold tensor power of all
unitaries consists exactly of scalar multiples of the identity. -/
theorem commutant_unitary_eq_scalar :
    {M : (⨂[ℂ]^1 (FiniteHilbertSpace d)) →ₗ[ℂ] (⨂[ℂ]^1 (FiniteHilbertSpace d)) |
      ∀ U : UnitaryGroup d, M.comp (glPow U.toLinearMap) = (glPow U.toLinearMap).comp M} =
    {M | ∃ (scalar : ℂ), M = scalar • LinearMap.id} := by
  ext M
  simp only [Set.mem_setOf_eq]
  -- Instantiate the abstract Schur-Weyl Duality for k = 1.
  have h_duality := permSpan_eq_centralizer_unitaryTensorSpan (W := FiniteHilbertSpace d) (k := 1)
  -- Rewrite using the k = 1 identifications.
  rw [permSpan_one, unitaryTensorSpan, centralizer_span] at h_duality
  -- Express the commutation relation as membership in the centralizer set.
  have h_cent : (∀ U : UnitaryGroup d, M.comp (glPow U.toLinearMap) = (glPow U.toLinearMap).comp M) ↔
                M ∈ Set.centralizer (Set.range (fun U : UnitaryGroup d => glPow U.toLinearMap)) := by
    simp only [Set.mem_centralizer_iff, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact forall_congr' fun U ↦ eq_comm
  rw [h_cent, ← h_duality]
  -- Unfold the definition of span to get scalar multiples of the identity.
  change M ∈ Submodule.span ℂ {LinearMap.id} ↔ ∃ scalar, M = scalar • LinearMap.id
  rw [Submodule.mem_span_singleton]
  constructor <;> rintro ⟨c, rfl⟩ <;> exact ⟨c, rfl⟩

end LeanHaar
