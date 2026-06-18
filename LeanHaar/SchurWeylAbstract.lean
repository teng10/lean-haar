import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Schur–Weyl duality — abstract (algebraic) version

Experimental, Mathlib-native development that deliberately avoids the inner-product / Hilbert-space
scaffolding of `TensorPowerV2.lean`, `Permutation.lean`, `Operator.lean`. Schur–Weyl duality is
purely *algebraic*: it concerns two subalgebras of `Module.End ℂ (⨂[ℂ]^k V)` for a
finite-dimensional `ℂ`-vector space `V`, and the claim that each is the other's centralizer. So we
work with Mathlib's `⨂[ℂ]^k V` (`PiTensorProduct`) **directly** — no wrapper structure, no inner
product, no unitaries.

## The two actions

* `permRep : Representation ℂ (Equiv.Perm (Fin k)) (⨂[ℂ]^k V)` — the symmetric group permuting tensor
  factors, via `PiTensorProduct.reindex`. As a `Representation` it is exactly the object Mathlib's
  semisimplicity/density machinery consumes (`Representation.asModule`).
* `glPow A = A^{⊗k}` — the diagonal action of `Module.End ℂ V`, via `PiTensorProduct.map`.

## The statement and proof strategy

`permSpan = Span{W_π}` and `glSpan = Span{A^{⊗k}}` inside `Module.End ℂ (⨂[ℂ]^k V)`, and Schur–Weyl
says each is the other's centralizer (`Set.centralizer`).

The intended proof uses Mathlib's engine, which we *do* have:
* **Maschke** ([`RepresentationTheory.Maschke`]) ⟹ `⨂[ℂ]^k V` is a *semisimple* `ℂ[S_k]`-module.
* **Jacobson density / double centralizer**
  (`Module.Finite.toModuleEnd_moduleEnd_surjective`, [`RingTheory.SimpleModule.Basic`]) ⟹ the
  bicommutant of the `S_k`-image is itself, i.e. `permSpan'' = permSpan`.
* The remaining, genuinely Schur–Weyl-specific input is the **bridge** `glSpan = permSpan'` (the
  commutant of `S_k` is spanned by the `A^{⊗k}`). Mathlib does *not* provide this; it is the heart of
  the theorem. It is left as `sorry` below.
-/

namespace LeanHaar.SchurWeylAbstract

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {k : ℕ}

/-!
## The symmetric-group action `permRep`
-/

/-- The diagonal action of the symmetric group `S_k = Equiv.Perm (Fin k)` on `⨂[ℂ]^k V`, permuting
tensor factors via `PiTensorProduct.reindex`. On pure tensors `W_π (⨂ᵢ fᵢ) = ⨂ᵢ f_{π⁻¹ i}`. -/
noncomputable def permRep : Representation ℂ (Equiv.Perm (Fin k)) (⨂[ℂ]^k V) where
  toFun π := (PiTensorProduct.reindex ℂ (fun _ : Fin k => V) π).toLinearMap
  map_one' := by
    ext x
    simp [Equiv.Perm.one_def, PiTensorProduct.reindex_refl]
  map_mul' π σ := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
    simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, LinearEquiv.coe_coe,
      PiTensorProduct.reindex_tprod, Equiv.Perm.mul_def, Equiv.symm_trans_apply]

@[simp] lemma permRep_tprod (π : Equiv.Perm (Fin k)) (f : Fin k → V) :
    permRep π (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (fun i => f (π⁻¹ i)) := by
  simp [permRep, PiTensorProduct.reindex_tprod, Equiv.Perm.inv_def]

/-!
## The general linear action `glPow`
-/

/-- The `k`-th tensor power `A^{⊗k}` of an operator `A : Module.End ℂ V`, acting on `⨂[ℂ]^k V` via
`PiTensorProduct.map`. On pure tensors `A^{⊗k} (⨂ᵢ fᵢ) = ⨂ᵢ A fᵢ`. -/
noncomputable def glPow (A : Module.End ℂ V) : Module.End ℂ (⨂[ℂ]^k V) :=
  PiTensorProduct.map fun _ : Fin k => A

@[simp] lemma glPow_tprod (A : Module.End ℂ V) (f : Fin k → V) :
    glPow A (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (fun i => A (f i)) := by
  simp only [glPow, PiTensorProduct.map_tprod]

/-!
## The two spans
-/

/-- `Span{W_π : π ∈ S_k}` inside `Module.End ℂ (⨂[ℂ]^k V)`. -/
noncomputable def permSpan : Submodule ℂ (Module.End ℂ (⨂[ℂ]^k V)) :=
  Submodule.span ℂ (Set.range fun π : Equiv.Perm (Fin k) => permRep π)

/-- `Span{A^{⊗k} : A ∈ End ℂ V}` inside `Module.End ℂ (⨂[ℂ]^k V)`. -/
noncomputable def glSpan : Submodule ℂ (Module.End ℂ (⨂[ℂ]^k V)) :=
  Submodule.span ℂ (Set.range fun A : Module.End ℂ V => glPow A)

/-!
## The easy direction: the two actions commute

Permuting the factors commutes with applying `A` to each factor, so each `A^{⊗k}` commutes with each
`W_π`. Extending by bilinearity gives `glSpan ⊆ (permSpan)'`, one of the two inclusions of the
duality. This needs no finite-dimensionality.
-/

/-- `A^{⊗k}` commutes with the permutation operator `W_π`: both send `⨂ᵢ fᵢ ↦ ⨂ᵢ A f_{π⁻¹ i}`. -/
lemma glPow_commute_permRep (A : Module.End ℂ V) (π : Equiv.Perm (Fin k)) :
    permRep π * glPow A = glPow A * permRep π := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, glPow_tprod, permRep_tprod]

/-- **Easy direction of Schur–Weyl duality**: the span of the tensor-power operators is contained in
the commutant of the permutation algebra. -/
lemma glSpan_subset_centralizer_permSpan :
    (↑(glSpan (V := V) (k := k)) : Set (Module.End ℂ (⨂[ℂ]^k V)))
      ⊆ Set.centralizer ↑(permSpan (V := V) (k := k)) := by
  -- each generator `A^{⊗k}` commutes with everything in `permSpan` (induct on `permSpan`)
  have hgen : ∀ A : Module.End ℂ V,
      glPow A ∈ Set.centralizer (↑(permSpan (V := V) (k := k)) :
        Set (Module.End ℂ (⨂[ℂ]^k V))) := by
    intro A
    rw [Set.mem_centralizer_iff]
    intro Y hY
    simp only [SetLike.mem_coe, permSpan] at hY
    induction hY using Submodule.span_induction with
    | mem Y h => obtain ⟨π, rfl⟩ := h; exact glPow_commute_permRep A π
    | zero => rw [zero_mul, mul_zero]
    | add Y Z _ _ hY hZ => rw [add_mul, mul_add, hY, hZ]
    | smul c Y _ hY => rw [smul_mul_assoc, mul_smul_comm, hY]
  -- extend from generators to all of `glSpan` (induct on `glSpan`); the centralizer is a submodule
  intro X hX
  simp only [SetLike.mem_coe, glSpan] at hX
  induction hX using Submodule.span_induction with
  | mem X h => obtain ⟨A, rfl⟩ := h; exact hgen A
  | zero => rw [Set.mem_centralizer_iff]; intro Z _; rw [mul_zero, zero_mul]
  | add X Y _ _ hX hY =>
      rw [Set.mem_centralizer_iff] at hX hY ⊢
      intro Z hZ; rw [mul_add, add_mul, hX Z hZ, hY Z hZ]
  | smul c X _ hX =>
      rw [Set.mem_centralizer_iff] at hX ⊢
      intro Z hZ; rw [mul_smul_comm, smul_mul_assoc, hX Z hZ]

/-!
## The Mathlib engine

The double-centralizer step rests on `⨂[ℂ]^k V` being a *semisimple* `ℂ[S_k]`-module. This is
supplied by Maschke's theorem (`RepresentationTheory.Maschke`): over `ℂ` the group algebra
`ℂ[S_k]` is a semisimple ring, so *every* `ℂ[S_k]`-module is semisimple — in particular the module
`permRep.asModule` carrying our `S_k`-action. Turning that into the statements below uses the
double-centralizer / Jacobson density theorem
(`Module.Finite.toModuleEnd_moduleEnd_surjective`), via `permRep.asModule`.
-/

/-!
## Schur–Weyl duality (commutant form)
-/

variable [Module.Finite ℂ V]

/-!
The whole duality reduces to **two irreducible inputs**, isolated as the two `sorry`s below:

1. the **double-centralizer theorem** `(permSpan)′′ = permSpan` (`centralizer_centralizer_permSpan`),
   the consequence of Maschke (semisimplicity) + Jacobson density;
2. the **bridge** `(permSpan)′ ⊆ glSpan` (inside `glSpan_eq_centralizer_permSpan`), the genuinely
   Schur–Weyl-specific fact that the commutant of `S_k` is spanned by the `A^{⊗k}`.

Everything else — both easy inclusions, and the *entire* permutation-side theorem — is derived from
these by general nonsense. Note no unitaries appear: we use *all* of `End ℂ V`, so the blueprint's
`Span{U^{⊗k} : U unitary} = Span{A^{⊗k}}` equivalence is not needed here (it would only be required to
re-express the statement over the unitary group).
-/

/-- **Double-centralizer / bicommutant theorem** for the permutation algebra: `(permSpan)′′ =
permSpan`. The easy inclusion `permSpan ⊆ (permSpan)′′` is general nonsense; the reverse is supplied
by Jacobson density (`Module.Finite.toModuleEnd_moduleEnd_surjective`) applied to the semisimple
`ℂ[S_k]`-module `permRep.asModule` (Maschke). -/
lemma centralizer_centralizer_permSpan :
    Set.centralizer (Set.centralizer
        (↑(permSpan (V := V) (k := k)) : Set (Module.End ℂ (⨂[ℂ]^k V))))
      = ↑(permSpan (V := V) (k := k)) := by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
  -- `(permSpan)′′ ⊆ permSpan` — Maschke + Jacobson density (`permRep.asModule`)
  sorry

/-- **Schur–Weyl duality** (algebraic, GL side): the commutant of the permutation algebra is the span
of the tensor-power operators. The easy inclusion is filled; the reverse is the **bridge**, the
substantive Schur–Weyl content. -/
theorem glSpan_eq_centralizer_permSpan :
    (↑(glSpan (V := V) (k := k)) : Set (Module.End ℂ (⨂[ℂ]^k V)))
      = Set.centralizer ↑(permSpan (V := V) (k := k)) :=
  Set.Subset.antisymm glSpan_subset_centralizer_permSpan (by
    -- bridge: `(permSpan)′ ⊆ glSpan`
    sorry)

/-- **Schur–Weyl duality** (algebraic, permutation side): the commutant of the tensor-power algebra
is the span of the permutation operators. This is *derived*, with no further input, from the GL-side
duality and the double-centralizer theorem:
`(glSpan)′ = ((permSpan)′)′ = (permSpan)′′ = permSpan`. -/
theorem permSpan_eq_centralizer_glSpan :
    (↑(permSpan (V := V) (k := k)) : Set (Module.End ℂ (⨂[ℂ]^k V)))
      = Set.centralizer ↑(glSpan (V := V) (k := k)) := by
  rw [glSpan_eq_centralizer_permSpan, centralizer_centralizer_permSpan]

/-!
## Unitary form

The form used in physics, `Comm(U(d), k) = Span{W_π}`: the commutant of the unitary tensor powers is
the span of the permutation operators. Unitaries require an inner product, so this lives over an
`InnerProductSpace` `W` (the unitary group is `W ≃ₗᵢ[ℂ] W`).

It follows from the all-operators duality (`permSpan_eq_centralizer_glSpan`) and one **intermediate
lemma**: the unitary and all-operator tensor powers span the *same* subspace — the symmetric subspace
`L(W)^{∨k}` (`unitaryTensorSpan_eq_glSpan`, blueprint thm 7.11). Its easy `≤` direction is proved
here; the `≥` direction (polarization: the unitaries span `End ℂ W`) is the only new `sorry`.
-/

section Unitary

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {k : ℕ}

/-- `Span{U^{⊗k} : U ∈ U(W)}`, the span of the `k`-th tensor powers of unitaries `U : W ≃ₗᵢ[ℂ] W`. -/
noncomputable def unitaryTensorSpan : Submodule ℂ (Module.End ℂ (⨂[ℂ]^k W)) :=
  Submodule.span ℂ (Set.range fun U : W ≃ₗᵢ[ℂ] W => glPow U.toLinearEquiv.toLinearMap)

omit [FiniteDimensional ℂ W] in
/-- The easy inclusion `unitaryTensorSpan ≤ glSpan`: every `U^{⊗k}` is an `A^{⊗k}` (take `A = U`), so
unitary tensor powers lie in the all-operator span. -/
lemma unitaryTensorSpan_le_glSpan :
    unitaryTensorSpan (W := W) (k := k) ≤ glSpan (V := W) (k := k) := by
  rw [unitaryTensorSpan]
  apply Submodule.span_le.2
  rintro _ ⟨U, rfl⟩
  exact Submodule.subset_span ⟨U.toLinearEquiv.toLinearMap, rfl⟩

/-- **The symmetric-subspace identity** (blueprint thm 7.11): the unitary tensor powers and the
all-operator tensor powers span the *same* subspace. That subspace is the symmetric subspace
`L(W)^{∨k} = (permSpan)′` (cf. `permSpan_eq_centralizer_glSpan`).

The `≤` direction is elementary (`unitaryTensorSpan_le_glSpan`). The `≥` direction —
`Span{A^{⊗k} : A ∈ End} ⊆ Span{U^{⊗k} : U unitary}` — is the substantive content, proved by
polarization once one knows the unitaries span `End ℂ W` over `ℂ`; it is left as `sorry`. -/
lemma unitaryTensorSpan_eq_glSpan :
    unitaryTensorSpan (W := W) (k := k) = glSpan (V := W) (k := k) := by
  refine le_antisymm unitaryTensorSpan_le_glSpan ?_
  -- `glSpan ≤ unitaryTensorSpan`: polarization; the unitaries span `End ℂ W`
  sorry

/-- **Schur–Weyl duality, unitary form.** The commutant of the unitary tensor powers
`{U^{⊗k} : U ∈ U(W)}` is the span of the permutation operators `Span{W_π : π ∈ S_k}`. Specialising to
`k = 1` (where `permSpan = ℂ • 1`) gives the twirl / `1`-design fact `Comm(U(W)) = ℂ • 1`. -/
theorem permSpan_eq_centralizer_unitaryTensorSpan :
    (↑(permSpan (V := W) (k := k)) : Set (Module.End ℂ (⨂[ℂ]^k W)))
      = Set.centralizer ↑(unitaryTensorSpan (W := W) (k := k)) := by
  rw [unitaryTensorSpan_eq_glSpan]
  exact permSpan_eq_centralizer_glSpan

end Unitary

end LeanHaar.SchurWeylAbstract


