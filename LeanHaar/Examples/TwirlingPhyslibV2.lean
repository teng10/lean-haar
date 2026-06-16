import QuantumInfo.States.Pure.Qubit

namespace Twirling.Physlib

open Matrix

/-- The **Pauli twirl** of a single-qubit state `ρ`: the group average of `ρ` over the
single-qubit Pauli group. Because the phases `±1, ±i` cancel under the conjugation
`U * ρ * Uᴴ`, only the four effective operators `I, X, Y, Z` contribute, giving
`pauliTwirl ρ = ¼ • (X * ρ * X + Y * ρ * Y + Z * ρ * Z + I * ρ * I)`.

The final `1` is the identity matrix `(1 : Matrix (Fin 2) (Fin 2) ℂ)`; its type is
inferred from the surrounding multiplication, so the verbose ascription is unnecessary. -/
noncomputable def pauliTwirl (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 4 : ℝ) • (Qubit.X.val * ρ * Qubit.X.val + Qubit.Y.val * ρ * Qubit.Y.val
  + Qubit.Z.val * ρ * Qubit.Z.val + 1 * ρ * 1)


/-- The single-qubit density matrix with Bloch vector `(rx, ry, rz) ∈ ℝ³`:
`blochState r = ½ • (I + rx • X + ry • Y + rz • Z)`.

The `: ℝ` ascription on `1 / 2` is **load-bearing**: without it the literal defaults to `ℕ`,
where `1 / 2 = 0`, silently collapsing the whole matrix to `0`. Unlike a bare `1` — whose
type is forced by an adjacent `*` — the scalar of a `•` is not pinned down by the matrix
operand, so it needs the annotation. -/
noncomputable def blochState (rx ry rz : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℝ) • (1 + rx • Qubit.X.val + ry • Qubit.Y.val + rz • Qubit.Z.val)


/-- The underlying matrices of the bundled Pauli unitaries, exposed as `rfl` lemmas. -/
lemma X_val : Qubit.X.val = ![![0, 1], ![1, 0]] := rfl
lemma Y_val : Qubit.Y.val = ![![0, -Complex.I], ![Complex.I, 0]] := rfl
lemma Z_val : Qubit.Z.val = ![![1, 0], ![0, -1]] := rfl

/-- **Pauli twirling of a single qubit.** Twirling any single-qubit state over the
Pauli group collapses it to the maximally mixed state `I / 2`, independently of the
Bloch vector `(rx, ry, rz)`. -/
theorem twirl_single_qubit (rx ry rz : ℝ) :
    pauliTwirl (blochState rx ry rz) = (1 / 2 : ℝ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  -- expand the Paulis and the twirl, and turn the ℝ-`smul` on ℂ into multiplication,
  simp [pauliTwirl, blochState, X_val, Y_val, Z_val,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        Complex.real_smul] <;>
  ring_nf <;>
  simp [Complex.I_sq] <;>
  ring

end Twirling.Physlib
