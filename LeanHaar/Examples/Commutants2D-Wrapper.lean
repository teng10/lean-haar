import LeanHaar.UnitaryCommutants
import LeanHaar.HilbertSpace
import LeanHaar.SchurWeylAbstract
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Perm

/-!
# Commutant of the Second-Order Unitary Group ($k=2$)

This file formalizes the commutant of the second-order unitary group representation
on `⨂[ℂ]^2 𝓗[d]`. Specifically, it shows that any endomorphism that commutes with all
second-order unitary tensor powers is in the span of the identity operator and the SWAP operator.

## Main results

* `LeanHaar.perm_fin2_eq` : Every permutation on `Fin 2` is either the identity or the swap transposition.
* `LeanHaar.permSpan_two` : The permutation algebra `permSpan` for `k=2` is spanned by the identity and the SWAP operator.
* `LeanHaar.commutant_unitary_eq_span_id_swap` : The commutant of second-order unitaries is the span of the identity and SWAP.
-/

namespace LeanHaar

open scoped TensorProduct
open SchurWeylAbstract

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Every permutation on `Fin 2` is either the identity or the SWAP operator (swapping 0 and 1). -/
lemma perm_fin2_eq (π : Equiv.Perm (Fin 2)) :
    π = 1 ∨ π = Equiv.swap (0 : Fin 2) (1 : Fin 2) := by
  fin_cases π <;> decide

/-- The permutation algebra for `k = 2` is spanned by the identity and the SWAP operator. -/
lemma permSpan_two :
    permSpan (V := FiniteHilbertSpace d) (k := 2) =
      Submodule.span ℂ {(LinearMap.id : Module.End ℂ (⨂[ℂ]^2 (FiniteHilbertSpace d))),
                        permRep (Equiv.swap (0 : Fin 2) (1 : Fin 2))} := by
  simp only [permSpan] -- substitute definition
  congr 1
  ext f -- f ∈ A ↔ f ∈ B
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨π, rfl⟩
    rcases perm_fin2_eq π with rfl | rfl
    · left; exact map_one permRep
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨1, map_one permRep⟩
    · exact ⟨_, rfl⟩

/-- **Commutant of the 2-fold Tensor Unitary Group** (Blueprint Theorem):
The commutant of second-order unitaries is exactly the span of the identity and the SWAP operator. -/
theorem commutant_unitary_eq_span_id_swap (d : Type*) [Fintype d] [DecidableEq d] :
  {M : (⨂[ℂ]^2 (FiniteHilbertSpace d)) →ₗ[ℂ] (⨂[ℂ]^2 (FiniteHilbertSpace d)) |
    ∀ U : UnitaryGroup d, M.comp (glPow U.toLinearMap) = (glPow U.toLinearMap).comp M}
  = ↑(Submodule.span ℂ {(LinearMap.id : Module.End ℂ (⨂[ℂ]^2 (FiniteHilbertSpace d))),
                        permRep (Equiv.swap (0 : Fin 2) (1 : Fin 2))}) := by
  rw [commutant_unitary_eq_permSpan d 2]
  rw [permSpan_two]

end LeanHaar
