/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Trace contractions of tensors of operators

These linear maps contract tensors of endomorphisms against fixed operators through
traces. They are built from `LinearMap.trace`, `LinearMap.mulLeft`, `TensorProduct.map`,
and `TensorProduct.lid`, over an arbitrary field.

The domains are algebraic tensor products of endomorphism spaces, such as
`Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V`. They are not defined here as endomorphisms of
`V ⊗[𝕜] V`; no identification between those spaces is assumed or constructed.

## Main definitions

* `LinearMap.traceMulLeft`: the linear functional `X ↦ Tr(A X)`.
* `LinearMap.partialTraceFirst`: the partial trace `A ⊗ B ↦ Tr(ρ A) • B` against `ρ`
  in the first tensor factor.
* `LinearMap.doubleTraceContract`, `LinearMap.tripleTraceContract`: the scalar
  contractions `X ⊗ Y ↦ Tr(A X) Tr(B Y)` and `X ⊗ Y ⊗ Z ↦ Tr(A X) Tr(B Y) Tr(C Z)`.
-/

noncomputable section

namespace LinearMap

open scoped TensorProduct

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The linear functional `X ↦ Tr(A X)`. -/
def traceMulLeft (A : Module.End 𝕜 V) : Module.End 𝕜 V →ₗ[𝕜] 𝕜 :=
  (LinearMap.trace 𝕜 V) ∘ₗ LinearMap.mulLeft 𝕜 A

@[simp] theorem traceMulLeft_apply (A X : Module.End 𝕜 V) :
    traceMulLeft A X = LinearMap.trace 𝕜 V (A ∘ₗ X) := rfl

/-- Contract the first factor of an operator tensor against `ρ`,
`A ⊗ B ↦ Tr(ρ A) • B`. -/
def partialTraceFirst (ρ : Module.End 𝕜 V) :
    Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V :=
  (TensorProduct.lid 𝕜 (Module.End 𝕜 V)).toLinearMap ∘ₗ
    TensorProduct.map (traceMulLeft ρ) LinearMap.id

@[simp] theorem partialTraceFirst_tmul (ρ A B : Module.End 𝕜 V) :
    partialTraceFirst ρ (A ⊗ₜ[𝕜] B) = LinearMap.trace 𝕜 V (ρ ∘ₗ A) • B := by
  simp [partialTraceFirst]

/-- Contraction of a twofold tensor of operators, `X ⊗ Y ↦ Tr(A X) Tr(B Y)`. -/
def doubleTraceContract (A B : Module.End 𝕜 V) :
    Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V →ₗ[𝕜] 𝕜 :=
  (TensorProduct.lid 𝕜 𝕜).toLinearMap ∘ₗ TensorProduct.map (traceMulLeft A) (traceMulLeft B)

@[simp] theorem doubleTraceContract_tmul (A B X Y : Module.End 𝕜 V) :
    doubleTraceContract A B (X ⊗ₜ[𝕜] Y) =
      LinearMap.trace 𝕜 V (A ∘ₗ X) * LinearMap.trace 𝕜 V (B ∘ₗ Y) := by
  simp [doubleTraceContract, smul_eq_mul]

/-- Contraction of a right-associated threefold tensor of operators,
`X ⊗ (Y ⊗ Z) ↦ Tr(A X) Tr(B Y) Tr(C Z)`. -/
def tripleTraceContract (A B C : Module.End 𝕜 V) :
    Module.End 𝕜 V ⊗[𝕜] (Module.End 𝕜 V ⊗[𝕜] Module.End 𝕜 V) →ₗ[𝕜] 𝕜 :=
  (TensorProduct.lid 𝕜 𝕜).toLinearMap ∘ₗ
    TensorProduct.map (traceMulLeft A) (doubleTraceContract B C)

@[simp] theorem tripleTraceContract_tmul (A B C X Y Z : Module.End 𝕜 V) :
    tripleTraceContract A B C (X ⊗ₜ[𝕜] (Y ⊗ₜ[𝕜] Z)) =
      LinearMap.trace 𝕜 V (A ∘ₗ X) * LinearMap.trace 𝕜 V (B ∘ₗ Y) *
        LinearMap.trace 𝕜 V (C ∘ₗ Z) := by
  simp [tripleTraceContract, smul_eq_mul, mul_assoc]

end LinearMap
