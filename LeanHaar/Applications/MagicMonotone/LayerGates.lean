/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Applications.MagicMonotone.BrickworkLayers
import LeanHaar.SupportingDocs.UnitaryTensor

/-!
# Independent two-qubit gates in the four-qubit brickwork layers

The register decompositions record the input order of each gate: layer A uses
`(0,1)` and `(2,3)`, while layer B uses `(1,2)` and `(3,0)`. The two sampled
unitaries therefore act on ordered two-qubit spaces, including the wraparound gate.

## Main definitions

* `MagicMonotone.layerUnitaryA` and `MagicMonotone.layerUnitaryB`: the sampled gates
  used by the calculation.
* `MagicMonotone.layerIndexA` and `MagicMonotone.layerIndexB`: their ordered coordinate
  decompositions, used to relate these gates to the existing permutation operators.

## Main results

* `MagicMonotone.continuous_layerUnitaryA` and `MagicMonotone.continuous_layerUnitaryB`:
  continuity needed for Haar integration.
* `MagicMonotone.toEndMatrix_layerA_perm` and `MagicMonotone.toEndMatrix_layerB_perm`:
  the coordinate identities connecting the placed permutations to the layer kets.
-/
noncomputable section
open scoped Matrix Kronecker
open SchurWeyl
namespace MagicMonotone

/-- A two-qubit basis index, with the first and second input bit in that order. -/
private def pairBitsEquiv : Fin 4 ≃ (Fin 2 → Fin 2) :=
  (finCongr (show (4 : ℕ) = 2 ^ 2 by norm_num)).trans finFunctionFinEquiv.symm

/-- Ordered register decomposition for gates on `(0,1)` and `(2,3)`. -/
def layerIndexA : Fin 16 ≃ Fin 4 × Fin 4 where
  toFun i := (pairBitsEquiv.symm ![bitsEquiv i 0, bitsEquiv i 1],
    pairBitsEquiv.symm ![bitsEquiv i 2, bitsEquiv i 3])
  invFun p := bitsEquiv.symm ![pairBitsEquiv p.1 0, pairBitsEquiv p.1 1,
    pairBitsEquiv p.2 0, pairBitsEquiv p.2 1]
  left_inv i := by
    apply bitsEquiv.injective
    simp only [Equiv.apply_symm_apply]
    ext j
    fin_cases j <;> simp
  right_inv p := by
    apply Prod.ext <;> apply pairBitsEquiv.injective
    all_goals
      simp only [Equiv.apply_symm_apply]
      ext j
      fin_cases j <;> simp

/-- Ordered register decomposition for gates on `(1,2)` and `(3,0)`. -/
def layerIndexB : Fin 16 ≃ Fin 4 × Fin 4 where
  toFun i := (pairBitsEquiv.symm ![bitsEquiv i 1, bitsEquiv i 2],
    pairBitsEquiv.symm ![bitsEquiv i 3, bitsEquiv i 0])
  invFun p := bitsEquiv.symm ![pairBitsEquiv p.2 1, pairBitsEquiv p.1 0,
    pairBitsEquiv p.1 1, pairBitsEquiv p.2 0]
  left_inv i := by
    apply bitsEquiv.injective
    simp only [Equiv.apply_symm_apply]
    ext j
    fin_cases j <;> simp
  right_inv p := by
    apply Prod.ext <;> apply pairBitsEquiv.injective
    all_goals
      simp only [Equiv.apply_symm_apply]
      ext j
      fin_cases j <;> simp

/-- Apply the two sampled gates on disjoint pairs `(0,1)` and `(2,3)`. -/
def layerUnitaryA (p : Matrix.unitaryGroup (Fin 4) ℂ × Matrix.unitaryGroup (Fin 4) ℂ) :
    Matrix.unitaryGroup (Fin 16) ℂ := tensorUnitary layerIndexA p.1 p.2

/-- Apply the two sampled gates on disjoint pairs `(1,2)` and `(3,0)`. -/
def layerUnitaryB (p : Matrix.unitaryGroup (Fin 4) ℂ × Matrix.unitaryGroup (Fin 4) ℂ) :
    Matrix.unitaryGroup (Fin 16) ℂ := tensorUnitary layerIndexB p.1 p.2

/-- Layer A depends continuously on its two sampled gates. -/
theorem continuous_layerUnitaryA : Continuous layerUnitaryA :=
  continuous_tensorUnitary layerIndexA

/-- Layer B depends continuously on its two sampled gates. -/
theorem continuous_layerUnitaryB : Continuous layerUnitaryB :=
  continuous_tensorUnitary layerIndexB

/-- The two local permutation operators are the existing layer-A permutation product. -/
theorem toEndMatrix_layerA_perm (σ τ : Equiv.Perm Copies) :
    toEndMatrix 16 4 (V12 σ * V34 τ) =
      (toEndMatrix 4 4 (permOp 4 σ) ⊗ₖ toEndMatrix 4 4 (permOp 4 τ)).submatrix
        (tensorCopiesEquiv layerIndexA 4) (tensorCopiesEquiv layerIndexA 4) := by
  rw [layerA_regPerm, toEndMatrix_regPerm]
  ext I J
  simp only [Matrix.submatrix_apply, regPermMat_apply, Matrix.kronecker_apply,
    permOp, toEndMatrix_permAction, tensorCopiesEquiv_apply]
  rw [ite_mul, one_mul, zero_mul, ← ite_and]
  apply if_congr ?_ rfl rfl
  change (∀ q, (fun c => bitsEquiv (I c) q) =
      (fun c => bitsEquiv (J ((![σ, σ, τ, τ] q).symm c)) q)) ↔
    ((fun c => pairBitsEquiv.symm ![bitsEquiv (I c) 0, bitsEquiv (I c) 1]) =
      (fun c => pairBitsEquiv.symm ![bitsEquiv (J (σ.symm c)) 0, bitsEquiv (J (σ.symm c)) 1])) ∧
    ((fun c => pairBitsEquiv.symm ![bitsEquiv (I c) 2, bitsEquiv (I c) 3]) =
      (fun c => pairBitsEquiv.symm ![bitsEquiv (J (τ.symm c)) 2, bitsEquiv (J (τ.symm c)) 3]))
  simp only [funext_iff, pairBitsEquiv.symm.injective.eq_iff]
  constructor
  · intro h
    constructor <;> intro c q <;> fin_cases q
    all_goals exact h _ c
  · rintro ⟨h₁, h₂⟩ q c
    fin_cases q
    · exact h₁ c 0
    · exact h₁ c 1
    · exact h₂ c 0
    · exact h₂ c 1

/-- The two local permutation operators are the existing layer-B permutation product. -/
theorem toEndMatrix_layerB_perm (σ τ : Equiv.Perm Copies) :
    toEndMatrix 16 4 (V23 σ * V41 τ) =
      (toEndMatrix 4 4 (permOp 4 σ) ⊗ₖ toEndMatrix 4 4 (permOp 4 τ)).submatrix
        (tensorCopiesEquiv layerIndexB 4) (tensorCopiesEquiv layerIndexB 4) := by
  rw [layerB_regPerm, toEndMatrix_regPerm]
  ext I J
  simp only [Matrix.submatrix_apply, regPermMat_apply, Matrix.kronecker_apply,
    permOp, toEndMatrix_permAction, tensorCopiesEquiv_apply]
  rw [ite_mul, one_mul, zero_mul, ← ite_and]
  apply if_congr ?_ rfl rfl
  change (∀ q, (fun c => bitsEquiv (I c) q) =
      (fun c => bitsEquiv (J ((![τ, σ, σ, τ] q).symm c)) q)) ↔
    ((fun c => pairBitsEquiv.symm ![bitsEquiv (I c) 1, bitsEquiv (I c) 2]) =
      (fun c => pairBitsEquiv.symm ![bitsEquiv (J (σ.symm c)) 1, bitsEquiv (J (σ.symm c)) 2])) ∧
    ((fun c => pairBitsEquiv.symm ![bitsEquiv (I c) 3, bitsEquiv (I c) 0]) =
      (fun c => pairBitsEquiv.symm ![bitsEquiv (J (τ.symm c)) 3, bitsEquiv (J (τ.symm c)) 0]))
  simp only [funext_iff, pairBitsEquiv.symm.injective.eq_iff]
  constructor
  · intro h
    constructor <;> intro c q <;> fin_cases q
    all_goals exact h _ c
  · rintro ⟨h₁, h₂⟩ q c
    fin_cases q
    · exact h₂ c 1
    · exact h₁ c 0
    · exact h₁ c 1
    · exact h₂ c 0

end MagicMonotone
