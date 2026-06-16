# General Checklist

* [ ] Add permutation operator definitions
* [ ] Clean up and move written proof sketch into blueprint
* [ ]




# Potential TODOs

* Add `Qubit.X`/`Y`/`Z` entry-value simp lemmas (e.g. `Qubit.X.val = !![0, 1; 1, 0]`) to physlib's `QuantumInfo/States/Pure/Qubit.lean`. The bundled Pauli unitaries are opaque to `simp`, so downstream proofs (e.g. `Twirling.Physlib`) currently need local `X_val`/`Y_val`/`Z_val` rfl lemmas to unfold them; upstreaming these would remove that boilerplate.
* Add an identity to QuantumInfo
* Add BlochState to QuantumInfo
