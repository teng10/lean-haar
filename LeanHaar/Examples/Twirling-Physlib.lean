import QuantumInfo.States.Pure.Qubit
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

open Matrix Complex

-- The identity matrix does not appear to exist in Qubit.lean
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, 1]]

-- Extract the underlying matrices to avoid exposing the unitarity proofs to `simp`
-- Doing so prevents an infinite loop
lemma X_val : Qubit.X.val = ![![0, 1], ![1, 0]] := rfl
lemma Y_val : Qubit.Y.val = ![![0, -I], ![I, 0]] := rfl
lemma Z_val : Qubit.Z.val = ![![1, 0], ![0, -1]] := rfl

-- Definition 1 (Group average) Pauli twirling:
noncomputable def pauliTwirl (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 4 : ℂ) • (Qubit.X.val * ρ * Qubit.X.val + Qubit.Y.val * ρ * Qubit.Y.val + Qubit.Z.val * ρ * Qubit.Z.val + pauliI * ρ * pauliI)

-- ρ = 1/2 (I + rx*X + ry*Y + rz*Z)
noncomputable def blochState (rx ry rz : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (pauliI + rx • Qubit.X.val + ry • Qubit.Y.val + rz • Qubit.Z.val)

-- Theorem 1 (Pauli twirling of a single qubit):
-- set_option maxHeartbeats 1000000 in
theorem twirl_single_qubit (rx ry rz : ℂ) :
    pauliTwirl (blochState rx ry rz) = (1 / 2 : ℂ) • pauliI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliTwirl, blochState, pauliI, X_val, Y_val, Z_val,
        Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;>
  ring_nf <;>
  simp [Complex.I_sq] <;>
  ring
