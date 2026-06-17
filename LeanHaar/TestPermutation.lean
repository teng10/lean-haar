import LeanHaar.Permutation
import LeanHaar.TensorPower
import Mathlib.Tactic.FinCases

/-!
# Demonstration of permutation operators on tensor products of operators

This file demonstrates the action of the permutation operator `W_π` on the tensor product
of three operators in the space `ℂ² ⊗ ℂ² ⊗ ℂ²` (represented as `𝓗⊗[Fin 2, 3]`).

The main result demonstrated is that $W_\pi$ permutes the factors in a tensor product of
operators: $W_\pi (A_1 \otimes A_2 \otimes A_3) = (A_{\pi^{-1}(1)} \otimes A_{\pi^{-1}(2)} \otimes A_{\pi^{-1}(3)}) W_\pi$.
-/

namespace LeanHaar

open HilbertTensorPower
open scoped TensorProduct

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-- Specific demonstration for 3 qubits (`ℂ² ⊗ ℂ² ⊗ ℂ²`). -/
example (π : Equiv.Perm (Fin 3))
    (A B C : FiniteHilbertSpace (Fin 2) →ₗ[ℂ] FiniteHilbertSpace (Fin 2)) :
    let f : Fin 3 → (FiniteHilbertSpace (Fin 2) →ₗ[ℂ] FiniteHilbertSpace (Fin 2)) :=
      ![A, B, C]
    W π ∘ₗ map_tprod f = map_tprod (f ∘ π.symm) ∘ₗ W π := by
  apply W_map_tprod_comm

end LeanHaar
