/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.ClassicalShadows.UnitarySnapshots
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TraceNotation

/-!
# Contracting the second Haar moment against a state

The second Haar moment of the classical-shadow ensemble is `(I + 𝔽)/(d + 1)`. This file
computes, entrywise, its contraction against a state `ρ` in the first tensor factor: the
identity part contributes `Tr(ρ) I` and the swap part contributes `ρ`.

## Main results

* `ClassicalShadows.toEndMatrix_id_pair`, `ClassicalShadows.toEndMatrix_swap_pair`: the matrix
  entries of the identity and of the swap operator at the index pairs used by the partial
  trace over the first factor.
* `ClassicalShadows.contract_unitarySnapshotMoment_two`: the contraction equals
  `(Tr(ρ) δᵢⱼ + ρᵢⱼ)/(d + 1)`.
-/

noncomputable section

namespace ClassicalShadows

open SchurWeyl

variable {d : ℕ}

/-- The matrix entries of the identity of `(ℂ^d)^{⊗2}` at the index pairs used by the partial
trace over the first factor. -/
theorem toEndMatrix_id_pair (p : Fin d × Fin d) (i j : Fin d) :
    toEndMatrix d 2 (LinearMap.id : Module.End ℂ (TensV d 2)) ![p.2, i] ![p.1, j] =
      (if p.2 = p.1 then (1 : ℂ) else 0) * (if i = j then 1 else 0) := by
  rw [show (toEndMatrix d 2) (LinearMap.id : Module.End ℂ (TensV d 2)) = 1 from
    LinearMap.toMatrix_id (tensorBasis d 2), Matrix.one_apply]
  have hpair : (![p.2, i] : Fin 2 → Fin d) = ![p.1, j] ↔ (p.2 = p.1 ∧ i = j) := by
    refine ⟨fun h => ⟨congrFun h 0, congrFun h 1⟩, fun ⟨h₁, h₂⟩ => ?_⟩
    funext m; fin_cases m <;> simpa
  rw [if_congr hpair rfl rfl]
  by_cases h : p.2 = p.1 <;> by_cases h' : i = j <;> simp [h, h']

/-- The matrix entries of the swap operator `𝔽` at the index pairs used by the partial trace
over the first factor. -/
theorem toEndMatrix_swap_pair (p : Fin d × Fin d) (i j : Fin d) :
    toEndMatrix d 2 (𝔽 d) ![p.2, i] ![p.1, j] =
      (if p.2 = j then (1 : ℂ) else 0) * (if i = p.1 then 1 else 0) := by
  rw [toEndMatrix_swap]
  have hpair : (![p.2, i] : Fin 2 → Fin d) = ![p.1, j] ∘ (Equiv.swap (0 : Fin 2) 1) ↔
      (p.2 = j ∧ i = p.1) := by
    refine ⟨fun h => ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩,
      fun ⟨h₁, h₂⟩ => ?_⟩
    funext m; fin_cases m <;> simp [h₁, h₂]
  rw [if_congr hpair rfl rfl]
  by_cases h : p.2 = j <;> by_cases h' : i = p.1 <;> simp [h, h']

/-- Contracting the second Haar moment `(I + 𝔽)/(d+1)` against `ρ` in the first tensor factor
produces `(Tr(ρ) I + ρ)/(d+1)`, entrywise. -/
theorem contract_unitarySnapshotMoment_two [NeZero d] [Fact (2 ≤ d)]
    (ρ : Module.End ℂ (Fin d → ℂ)) (i j : Fin d) :
    ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
        toEndMatrix d 2 (unitarySnapshotMoment d 2) ![p.2, i] ![p.1, j] =
      ((d : ℂ) + 1)⁻¹ * (Tr[ρ] * (if i = j then 1 else 0) + matrixOf ρ i j) := by
  rw [unitarySnapshotMoment_two]
  simp only [_root_.map_smul, _root_.map_add, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    toEndMatrix_id_pair, toEndMatrix_swap_pair]
  -- the identity contributes `Tr(ρ) δᵢⱼ`, the swap contributes `ρᵢⱼ`
  have h₁ : ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
      ((if p.2 = p.1 then (1 : ℂ) else 0) * (if i = j then 1 else 0)) =
      Tr[ρ] * (if i = j then 1 else 0) := by
    rw [trace_eq_sum_diag, Finset.sum_mul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a] <;> simp +contextual [eq_comm]
  have h₂ : ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
      ((if p.2 = j then (1 : ℂ) else 0) * (if i = p.1 then 1 else 0)) = matrixOf ρ i j := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j] <;> simp +contextual
    · intro a _ ha; simp [Ne.symm ha]
    · simp
  calc ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 * (((d : ℂ) + 1)⁻¹ *
        ((if p.2 = p.1 then (1 : ℂ) else 0) * (if i = j then 1 else 0) +
          (if p.2 = j then (1 : ℂ) else 0) * (if i = p.1 then 1 else 0)))
      = ((d : ℂ) + 1)⁻¹ * ((∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
          ((if p.2 = p.1 then (1 : ℂ) else 0) * (if i = j then 1 else 0))) +
          ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
          ((if p.2 = j then (1 : ℂ) else 0) * (if i = p.1 then 1 else 0))) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = _ := by rw [h₁, h₂]

end ClassicalShadows
