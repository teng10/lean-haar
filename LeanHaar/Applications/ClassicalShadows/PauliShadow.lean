/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.SupportingDocs.POVM
import QuantumInfo.States.Pure.Qubit

/-!
# Pauli classical-shadow samples

`pauliShadow axis bit` reconstructs one qubit from a measured Pauli axis and its outcome.
`pauliShadow_unbiased` proves correctness for uniform axis sampling and Physlib's Born
probabilities. The estimator depends only on the experimental record, not the unknown state.

`localPauliShadow axes bits` forms the tensor product for a finite set of qubits. Its matrix
indices are bitstrings. The intended protocol chooses axes uniformly and independently;
measurement outcomes have the joint Born distribution and can be correlated for entangled
states. This file establishes the tensor construction, not its multi-qubit unbiasedness theorem.
-/

noncomputable section
open scoped BigOperators
namespace ClassicalShadows
/-- The three Pauli measurement bases of a qubit. -/
inductive PauliAxis
  | x | y | z
  deriving DecidableEq, Fintype

/-- Apply this unitary before computational-basis measurement to measure the chosen Pauli
axis. Outcome `0` is the `+1` eigenvalue and outcome `1` is the `-1` eigenvalue. -/
def pauliBasisRotation : PauliAxis → Matrix.unitaryGroup (Fin 2) ℂ
  | .x => Qubit.H
  | .y => Qubit.H * star Qubit.S
  | .z => 1

/-- The reconstructed single-qubit sample `3S - I`, where `S` is the measured Pauli
eigenprojector. It is Hermitian but need not be positive. -/
def pauliShadow (axis : PauliAxis) (b : Fin 2) : HermitianMat (Fin 2) ℂ :=
  (3 : ℝ) • (POVM.unitaryBasis (pauliBasisRotation axis)).mats b - 1

/-- The tensor product of the reconstructed samples, one for each qubit. The recorded
settings and outcomes are functions on the qubit labels; matrix indices are bitstrings. -/
def localPauliShadow {Q : Type*} [Fintype Q] [DecidableEq Q]
    (axes : Q → PauliAxis) (bits : Q → Fin 2) : HermitianMat (Q → Fin 2) ℂ :=
  ⟨Matrix.piProd (fun q => (pauliShadow (axes q) (bits q)).mat),
    Matrix.IsHermitian.piProd (fun q => (pauliShadow (axes q) (bits q)).H)⟩

private lemma sum_pauliAxis {α : Type*} [AddCommMonoid α] (f : PauliAxis → α) :
    ∑ a, f a = f .x + f .y + f .z := by
  rw [show (Finset.univ : Finset PauliAxis) = {.x, .y, .z} by decide]
  simp [add_assoc]

private lemma unitaryBasis_mats_apply (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (b i j : Fin 2) :
    ((POVM.unitaryBasis U).mats b).mat i j = star (U b i) * U b j := by
  change ((U : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose * Matrix.single b b 1 *
    (U : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose.conjTranspose : Matrix (Fin 2) (Fin 2) ℂ) i j = _
  rw [Matrix.conjTranspose_conjTranspose]
  fin_cases b <;> simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply]

private lemma pauliEffect_matrix (a : PauliAxis) (b : Fin 2) :
    ((POVM.unitaryBasis (pauliBasisRotation a)).mats b).mat =
      match a with
      | .x => if b = 0 then !![1/2, 1/2; 1/2, 1/2] else !![1/2, -1/2; -1/2, 1/2]
      | .y => if b = 0 then !![1/2, -Complex.I/2; Complex.I/2, 1/2]
                       else !![1/2, Complex.I/2; -Complex.I/2, 1/2]
      | .z => if b = 0 then !![1, 0; 0, 0] else !![0, 0; 0, 1] := by
  ext i j
  rw [unitaryBasis_mats_apply]
  cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j
  <;> simp [pauliBasisRotation, Qubit.H, Qubit.S, Matrix.mul_apply,
    Complex.ext_iff, field]

-- The six effects form an informationally complete measurement frame. This identity
-- holds for arbitrary matrices, so the Born-probability interpretation is a separate step.
private theorem reconstruction_matrix (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (3 : ℂ)⁻¹ • (∑ a, ∑ b, Matrix.trace (A *
      ((POVM.unitaryBasis (pauliBasisRotation a)).mats b).mat) •
        (pauliShadow a b).mat) = A := by
  simp only [pauliShadow, HermitianMat.mat_sub, HermitianMat.mat_smul, HermitianMat.mat_one,
    pauliEffect_matrix]
  rw [sum_pauliAxis]
  ext i j
  fin_cases i <;> fin_cases j
  <;> simp [Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two,
      Matrix.smul_apply, Complex.ext_iff, field]
  <;> norm_num
  <;> ring_nf
  <;> simp

/-- For a uniformly sampled Pauli axis and a Born-distributed outcome, the reconstructed
single-qubit snapshot has expectation equal to the input state. -/
theorem pauliShadow_unbiased (ρ : MState (Fin 2)) :
    (3 : ℝ)⁻¹ • (∑ axis : PauliAxis, ∑ b : Fin 2,
      ((POVM.unitaryBasis (pauliBasisRotation axis)).measure ρ b : ℝ) •
        pauliShadow axis b) = ρ.M := by
  apply HermitianMat.ext
  ext i j
  simpa only [HermitianMat.mat_smul, HermitianMat.mat_finset_sum, Matrix.smul_apply,
    Matrix.sum_apply, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    POVM.measure_eq_trace, smul_eq_mul, MState.mat_M] using
    congrFun (congrFun (reconstruction_matrix ρ.m) i) j

/-- The local reconstruction is the tensor product of the single-qubit reconstructions,
written using bitstring row and column indices. -/
@[simp] theorem localPauliShadow_apply {Q : Type*} [Fintype Q] [DecidableEq Q]
    (axes : Q → PauliAxis) (bits i j : Q → Fin 2) :
    (localPauliShadow axes bits).mat i j =
      ∏ q, (pauliShadow (axes q) (bits q)).mat (i q) (j q) := rfl

end ClassicalShadows
