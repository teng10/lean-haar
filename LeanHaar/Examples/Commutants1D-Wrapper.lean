import LeanHaar.UnitaryCommutants
import LeanHaar.HilbertSpace
import LeanHaar.SchurWeylAbstract
import Mathlib.LinearAlgebra.PiTensorProduct

namespace LeanHaar

open scoped TensorProduct
open SchurWeylAbstract

variable {d : Type*} [Fintype d] [DecidableEq d]

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

/-- **Commutant of Unitary Raised to Tensor Power 1** -/
theorem commutant_unitary_eq_id (d : Type*) [Fintype d] [DecidableEq d] :
  {M : (⨂[ℂ]^1 (FiniteHilbertSpace d)) →ₗ[ℂ] (⨂[ℂ]^1 (FiniteHilbertSpace d)) | ∀ U : UnitaryGroup d, M.comp (glPow U.toLinearMap) = (glPow U.toLinearMap).comp M}
  = {M | ∃ (scalar : ℂ), M = scalar • LinearMap.id } := by
  -- Use the equivalence from the wrapper for k = 1
  rw [commutant_unitary_eq_permSpan d 1]
  -- change RHS to match permutation span is id
  rw [permSpan_one]
  -- element-wise equivalence
  ext M
  -- remove set coercion from commutant_unitary_eq_scalar
  simp only [SetLike.mem_coe, Submodule.mem_span_singleton, Set.mem_setOf_eq]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, ha.symm⟩, fun ⟨a, ha⟩ ↦ ⟨a, ha.symm⟩⟩

end LeanHaar
