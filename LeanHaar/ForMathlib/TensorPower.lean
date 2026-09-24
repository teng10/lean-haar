/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# Tensor powers and their permutation and diagonal actions

This file constructs the tensor power `(ℂ^d)^{⊗k}`, the permutation action `permAction`,
and the diagonal action `diagAction`. Each action is accompanied by its elementary
computation rules and its image in the endomorphism algebra.

`diagImage` ranges over all endomorphisms, as used by the current polynomial proof.
Use the generic `map_one` and `map_pow` lemmas for identity and power preservation.
Commutation of the two actions is proved in `LeanHaar.ForMathlib.Commutation`.

Optional invertible and unitary wrappers and their conversion lemmas are commented out
below pending a concrete API consumer; see `TOOD.md`.
-/

noncomputable section

open scoped TensorProduct

namespace SchurWeyl

/-- The `k`-fold tensor power of `ℂ^d`, defined as `⨂[ℂ] (i : Fin k), (Fin d → ℂ)`. -/
abbrev TensV (d k : ℕ) : Type :=
  PiTensorProduct ℂ (fun (_ : Fin k) => (Fin d → ℂ))

/-! ### Permutation action -/

/-- The permutation operator `W_σ` on the tensor power `V^{⊗k}`.
Given `σ : Equiv.Perm (Fin k)`, this acts by permuting the tensor factors:
`W_σ (v₁ ⊗ ⋯ ⊗ vₖ) = v_{σ⁻¹(1)} ⊗ ⋯ ⊗ v_{σ⁻¹(k)}`. -/
noncomputable def permAction (d k : ℕ) :
    Equiv.Perm (Fin k) →* (TensV d k ≃ₗ[ℂ] TensV d k) where
    toFun σ := PiTensorProduct.reindex ℂ _ σ
    map_one' := PiTensorProduct.reindex_refl
    map_mul' σ τ := (PiTensorProduct.reindex_trans τ σ).symm

variable {d k : ℕ}

/-- Behavior of `permAction` on elementary tensors. -/
theorem permAction_tprod (σ : Equiv.Perm (Fin k)) (v : Fin k → (Fin d → ℂ)) :
    permAction d k σ (PiTensorProduct.tprod ℂ v) =
    PiTensorProduct.tprod ℂ (fun i => v (σ.symm i)) :=
  PiTensorProduct.reindex_tprod σ v

/-- The set of permutation operators in `End(V^{⊗k})`. -/
def permImage (d k : ℕ) : Set (Module.End ℂ (TensV d k)) :=
  Set.range (fun σ : Equiv.Perm (Fin k) => (permAction d k σ).toLinearMap)

/-! ### Diagonal action -/

/-- The diagonal action `g^{⊗k}` on the tensor power `V^{⊗k}`, as a monoid homomorphism of the
multiplicative monoid `End(V)`. Given `g : End(V)`, it acts as `g` on each tensor factor:
`g^{⊗k} (v₁ ⊗ ⋯ ⊗ vₖ) = g(v₁) ⊗ ⋯ ⊗ g(vₖ)`. -/
noncomputable def diagAction (d k : ℕ) : Module.End ℂ (Fin d → ℂ) →* Module.End ℂ (TensV d k) :=
  PiTensorProduct.mapMonoidHom.comp (Pi.constMonoidHom (Fin k) _)

/-- `diagAction g` is `PiTensorProduct.map` of the constant family at `g`. Deliberately not a
`simp` lemma: unfolding the bundled homomorphism hides the `diagAction`-level rewrites. -/
theorem diagAction_apply (g : Module.End ℂ (Fin d → ℂ)) :
    diagAction d k g = PiTensorProduct.map (fun _ : Fin k ↦ g) := rfl

/-- Behavior of `diagAction` on elementary tensors. -/
theorem diagAction_tprod (g : Module.End ℂ (Fin d → ℂ)) (v : Fin k → (Fin d → ℂ)) :
    diagAction d k g (PiTensorProduct.tprod ℂ v) =
    PiTensorProduct.tprod ℂ (fun i => g (v i)) :=
  PiTensorProduct.map_tprod _ v

/-- The diagonal action is multiplicative: `g^{⊗k} ∘ h^{⊗k} = (g ∘ h)^{⊗k}`. -/
theorem diagAction_comp (g h : Module.End ℂ (Fin d → ℂ)) :
    diagAction d k g ∘ₗ diagAction d k h = diagAction d k (g ∘ₗ h) :=
  (map_mul (diagAction d k) g h).symm

/-- The diagonal action is homogeneous of degree `k`: `(c • g)^{⊗k} = c ^ k • g^{⊗k}`.
It is not linear in `g` in general; for `k = 1` it is linear. -/
@[simp]
theorem diagAction_smul (c : ℂ) (g : Module.End ℂ (Fin d → ℂ)) :
    diagAction d k (c • g) = c ^ k • diagAction d k g := by
  ext x
  simp [diagAction_tprod, MultilinearMap.map_smul_univ (f := PiTensorProduct.tprod ℂ)]

/-- The set of diagonal operators `{g^{⊗k} | g ∈ End(V)}` in `End(V^{⊗k})`. -/
def diagImage (d k : ℕ) : Set (Module.End ℂ (TensV d k)) :=
  Set.range (fun g : Module.End ℂ (Fin d → ℂ) => diagAction d k g)

/-
Future API: bundled actions of invertible and unitary operators.
Restore in a focused module only when a consumer needs linear equivalences; see `TOOD.md`.
That module should import `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs` and
`Mathlib.LinearAlgebra.UnitaryGroup`. These wrappers package invertibility, not norm preservation.

/-- The diagonal action of an invertible operator on `V^{⊗k}`: an invertible `g : End(V)` acts as
the linear automorphism `g^{⊗k}`. -/
noncomputable def diagActionUnits (d k : ℕ) :
    LinearMap.GeneralLinearGroup ℂ (Fin d → ℂ) →* (TensV d k ≃ₗ[ℂ] TensV d k) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ (TensV d k)).toMonoidHom.comp
    (Units.map (diagAction d k))

-- /-- **The `GLₔ`-action** on `(ℂᵈ)^{⊗k}`, acting diagonally by `U ↦ U^{⊗k}`. -/
-- noncomputable def glAction (d k : ℕ) : GL (Fin d) ℂ →* (TensV d k ≃ₗ[ℂ] TensV d k) :=
--   (diagActionUnits d k).comp Matrix.GeneralLinearGroup.toLin.toMonoidHom

/-- **The unitary action** on `(ℂᵈ)^{⊗k}`, acting diagonally by `U ↦ U^{⊗k}`. -/
noncomputable def unitaryAction (d k : ℕ) :
    Matrix.unitaryGroup (Fin d) ℂ →* (TensV d k ≃ₗ[ℂ] TensV d k) :=
  (diagActionUnits d k).comp Matrix.UnitaryGroup.embeddingGL

-- Conversion lemmas for the optional wrappers.

-- @[simp]
-- theorem glAction_toLinearMap (U : GL (Fin d) ℂ) :
--     (glAction d k U).toLinearMap =
--     diagAction d k (Matrix.toLin' (U : Matrix (Fin d) (Fin d) ℂ)) :=
--   rfl

@[simp]
theorem unitaryAction_toLinearMap (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (unitaryAction d k U).toLinearMap =
    diagAction d k (Matrix.toLin' (U : Matrix (Fin d) (Fin d) ℂ)) :=
  rfl

@[simp]
theorem unitaryAction_symm_toLinearMap (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (unitaryAction d k U).symm.toLinearMap =
    diagAction d k (Matrix.toLin' (star (U : Matrix (Fin d) (Fin d) ℂ))) := by
  rw [← Matrix.UnitaryGroup.inv_val U, ← unitaryAction_toLinearMap, map_inv]
  rfl
-/

end SchurWeyl

end
