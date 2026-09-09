/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic
import LeanHaar.ForMathlib.ForMathlibExamples.SupportingDocs.TraceNotation

/-!
# Trace contractions of tensors of operators

The tensor-moment formulas of the classical-shadow protocol contract the tensor powers
`Sₓ^{⊗2}` and `Sₓ^{⊗3}` against operators through traces. This file provides the required
contraction maps, built compositionally from `TensorProduct.map` and `TensorProduct.lid`.

## Main definitions

* `ClassicalShadows.traceMulLeft`: the linear functional `X ↦ Tr(A X)`.
* `ClassicalShadows.partialTraceFirst`: the partial trace `A ⊗ B ↦ Tr(ρ A) • B` against `ρ`
  in the first tensor factor.
* `ClassicalShadows.doubleTraceContract`, `ClassicalShadows.tripleTraceContract`: the scalar
  contractions `X ⊗ Y ↦ Tr(A X) Tr(B Y)` and `X ⊗ Y ⊗ Z ↦ Tr(A X) Tr(B Y) Tr(C Z)`.
-/

noncomputable section

namespace ClassicalShadows

open scoped TensorProduct

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The linear functional `X ↦ Tr(A X)`. -/
def traceMulLeft (A : Module.End 𝕜 V) : Module.End 𝕜 V →ₗ[𝕜] 𝕜 where
  toFun X := Tr[A ∘ₗ X]
  map_add' X Y := by simp only [LinearMap.comp_add, map_add]
  map_smul' c X := by simp only [LinearMap.comp_smul, map_smul, RingHom.id_apply]

@[simp] theorem traceMulLeft_apply (A X : Module.End 𝕜 V) :
    traceMulLeft A X = Tr[A ∘ₗ X] := rfl

/-- Partial trace against `ρ` in the first tensor factor, `A ⊗ B ↦ Tr(ρ A) • B`. It
implements `Y ↦ Tr₁((ρ ⊗ I) Y)`. -/
def partialTraceFirst (ρ : Module.End 𝕜 V) :
    Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V :=
  (TensorProduct.lid 𝕜 (Module.End 𝕜 V)).toLinearMap ∘ₗ
    TensorProduct.map (traceMulLeft ρ) LinearMap.id

@[simp] theorem partialTraceFirst_tmul (ρ A B : Module.End 𝕜 V) :
    partialTraceFirst ρ (A ⊗ₜ[𝕜] B) = Tr[ρ ∘ₗ A] • B := by
  simp [partialTraceFirst]

/-- Contraction of a twofold tensor of operators, `X ⊗ Y ↦ Tr(A X) Tr(B Y)`. -/
def doubleTraceContract (A B : Module.End 𝕜 V) :
    Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V →ₗ[𝕜] 𝕜 :=
  (TensorProduct.lid 𝕜 𝕜).toLinearMap ∘ₗ TensorProduct.map (traceMulLeft A) (traceMulLeft B)

@[simp] theorem doubleTraceContract_tmul (A B X Y : Module.End 𝕜 V) :
    doubleTraceContract A B (X ⊗ₜ[𝕜] Y) = Tr[A ∘ₗ X] * Tr[B ∘ₗ Y] := by
  simp [doubleTraceContract, smul_eq_mul]

/-- Contraction of a threefold tensor of operators, `X ⊗ Y ⊗ Z ↦ Tr(A X) Tr(B Y) Tr(C Z)`.
It implements `W ↦ Tr((A ⊗ B ⊗ C) W)`. -/
def tripleTraceContract (A B C : Module.End 𝕜 V) :
    Module.End 𝕜 V ⊗[𝕜] (Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V) →ₗ[𝕜] 𝕜 :=
  (TensorProduct.lid 𝕜 𝕜).toLinearMap ∘ₗ
    TensorProduct.map (traceMulLeft A) (doubleTraceContract B C)

@[simp] theorem tripleTraceContract_tmul (A B C X Y Z : Module.End 𝕜 V) :
    tripleTraceContract A B C (X ⊗ₜ[𝕜] (Y ⊗ₜ[𝕜] Z)) =
      Tr[A ∘ₗ X] * Tr[B ∘ₗ Y] * Tr[C ∘ₗ Z] := by
  simp [tripleTraceContract, smul_eq_mul, mul_assoc]

end ClassicalShadows
