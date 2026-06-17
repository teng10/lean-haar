# General Checklist

## Definitions
* [x] Add permutation operator definitions
* [ ] Define the kth-order commutant
  * [ ] Prove the space becomes a Lie algebra.
* [ ] Define or identify methods for span
* [ ] Define the expectation value E[UOU^{\dagger}]
* [ ] Define the Haar measure, general probability measure
* [ ] Define the moment operator
* [ ] Define symmetric subspace over tensor product
* [ ] Define vec function and corresponding characteristics $W_{\pi} \otimes W_{\pi} vec(X) = vec(W_{\pi} X W_{\pi}^{T})$
* [ ] Define or identify methods for projection operators

## Major Results
* [ ] (Insert supporting theorems here, depending on the preferred proof)
* [ ] Double Commutant Theorem
* [ ] Schur-Weyl Duality
* [ ] Computation of first and second moments

# Potential TODOs

* Add `Qubit.X`/`Y`/`Z` entry-value simp lemmas (e.g. `Qubit.X.val = !![0, 1; 1, 0]`) to physlib's `QuantumInfo/States/Pure/Qubit.lean`. The bundled Pauli unitaries are opaque to `simp`, so downstream proofs (e.g. `Twirling.Physlib`) currently need local `X_val`/`Y_val`/`Z_val` rfl lemmas to unfold them; upstreaming these would remove that boilerplate.
* Add an identity to QuantumInfo
* Add BlochState to QuantumInfo
