import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

open Matrix Complex


-- Remark 2 (Pauli groups):
-- We define the 2x2 Pauli matrices σ₀ (I), σ₁ (X), σ₂ (Y), and σ₃ (Z) below.
-- These form the basis of the single-qubit Pauli group.
-- Identity matrix I (σ₀)
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, 1]]

-- Pauli-X matrix (σ₁)
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := ![![0, 1], ![1, 0]]

-- Pauli-Y matrix (σ₂)
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := ![![0, -I], ![I, 0]]

-- Pauli-Z matrix (σ₃)
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, -1]]


-- Definition 1 (Group average) Pauli twirling:
-- We seek to apply Pauli twirling to a single qubit state ρ.
-- We average over the 4 effective Pauli operators since the phase factors (±1, ±i)
-- cancel out in the conjugation U ρ U†.
noncomputable def pauliTwirl (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 4 : ℂ) • (pauliX * ρ * pauliX + pauliY * ρ * pauliY + pauliZ * ρ * pauliZ + pauliI * ρ * pauliI)

-- Remark 3 (Bloch vectors):
-- Any single qubit state ρ parameterized by its Bloch vector components (rx, ry, rz).
-- ρ = 1/2 (I + rx*X + ry*Y + rz*Z)
noncomputable def blochState (rx ry rz : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (pauliI + rx • pauliX + ry • pauliY + rz • pauliZ)

-- Theorem 1 (Pauli twirling of a single qubit):
-- For an arbitrary single-qubit state ρ, its Pauli twirl yields the maximally mixed state I / 2.
-- Note that the theorem relies on noncomputable definitions; otherwise will throw error.
-- So #evaluate can not be called on the theorem.
theorem twirl_single_qubit (rx ry rz : ℂ) :
    pauliTwirl (blochState rx ry rz) = (1 / 2 : ℂ) • pauliI := by
  -- We prove matrix equality by showing that each of the elements match.
  ext i j
  -- Iterate over each i and j over Fin 2 (0 and 1)
  fin_cases i <;> fin_cases j <;>
  -- We expand the definitions of Pauli matrices, Twirling, and the Bloch state.
  -- Then simplify matrix multiplication and addition.
  simp [pauliTwirl, blochState, pauliI, pauliX, pauliY, pauliZ,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
  -- ring_nf rearranges variables and groups the separated imaginary units 'I' into 'I ^ 2'
  ring_nf <;>
  -- simp then reduces those 'I ^ 2' terms into '-1'
  simp [Complex.I_sq] <;>
  -- Using ring to simplify the complex algebraic expressions
  ring
