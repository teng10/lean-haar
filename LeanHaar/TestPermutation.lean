import LeanHaar.Permutation
import LeanHaar.TensorPower
import Mathlib.Tactic.FinCases

/-!
# Demonstration of permutation operators on tensor products of operators

This file demonstrates the action of the permutation operator `W_π` on the tensor product
of operators. The main result demonstrated is the commutation relation:
$W_\pi (A_1 \otimes \dots \otimes A_k) = (A_{\pi^{-1}(1)} \otimes \dots \otimes A_{\pi^{-1}(k)}) W_\pi$.

## Results

* `LeanHaar.commutation_example` — a specific demonstration for 3 qubits (`ℂ² ⊗ ℂ² ⊗ ℂ²`).
-/

namespace LeanHaar

open HilbertTensorPower
open scoped TensorProduct

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-- Specific demonstration for the permutation of 3 qubits (`ℂ² ⊗ ℂ² ⊗ ℂ²`) using some π. -/
example (π : Equiv.Perm (Fin 3))
    (A B C : FiniteHilbertSpace (Fin 2) →ₗ[ℂ] FiniteHilbertSpace (Fin 2)) :
    let f : Fin 3 → (FiniteHilbertSpace (Fin 2) →ₗ[ℂ] FiniteHilbertSpace (Fin 2)) :=
      ![A, B, C]
    W π ∘ₗ map_tprod f = map_tprod (f ∘ π.symm) ∘ₗ W π := by
  apply W_map_tprod_comm

end LeanHaar
