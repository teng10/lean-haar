import LeanHaar.TensorPower
import LeanHaar.Permutation
import LeanHaar.TensorPower
import Mathlib.Tactic.FinCases

-- Test file

open LeanHaar
open HilbertTensorPower

/- ## Test Hilbert and tensor power space

This example demonstrates the action of the permutation operator `W_π` on the tensor product
of operators. The main result demonstrated is the commutation relation:
$W_\pi (A_1 \otimes \dots \otimes A_k) = (A_{\pi^{-1}(1)} \otimes \dots \otimes A_{\pi^{-1}(k)}) W_\pi$.

-/

-- The `k`-fold tensor power of `ℂ²` (i.e. `ℂ² ⊗ ℂ² ⊗ ℂ²`), as our wrapper type `𝓗⊗[Fin 2, 3]`.
#check (𝓗⊗[Fin 2, 3] : Type)

-- It is a finite-dimensional `ℂ`-vector space (instances synthesize).
#synth Module ℂ 𝓗⊗[Fin 2, 3]
#synth FiniteDimensional ℂ 𝓗⊗[Fin 2, 3]

/- ## Test permutation operators on tensor products of operators-/

open scoped TensorProduct
variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-- Specific demonstration for the permutation of 3 qubits (`ℂ² ⊗ ℂ² ⊗ ℂ²`) using some π. -/
example (π : Equiv.Perm (Fin 3))
    (A B C : FiniteHilbertSpace (Fin 2) →ₗ[ℂ] FiniteHilbertSpace (Fin 2)) :
    let f : Fin 3 → (FiniteHilbertSpace (Fin 2) →ₗ[ℂ] FiniteHilbertSpace (Fin 2)) :=
      ![A, B, C]
    W π ∘ₗ map_tprod f = map_tprod (f ∘ π.symm) ∘ₗ W π := by
  apply W_map_tprod_comm
