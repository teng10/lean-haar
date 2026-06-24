import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Schur–Weyl duality — self-contained, bundled version  [v3]

A standalone development of the algebraic Schur–Weyl duality, phrased entirely at the `Submodule`
level via a bundled `commutant`. It inlines only the pieces actually used from the original
`SchurWeylAbstract.lean`, dropping everything else, and is **coercion-free** throughout: every
duality statement is a homogeneous `Submodule = Submodule` equality.

## The two actions

* `permRep` — the symmetric group `S_k` permuting tensor factors of `⨂[ℂ]^k V`.
* `glPow A = A^{⊗k}` — the diagonal action of `Module.End ℂ V`.

## The bundled commutant

`commutant S : Submodule ℂ (Module.End ℂ M)` is the commutant of a submodule of operators, bundled
as a submodule (via `Subalgebra.centralizer`). All `Set`-level reasoning is confined to
`mem_commutant_iff` / `coe_commutant`.

## Main statements

* `glSpan_eq_commutant_permSpan`, `permSpan_eq_commutant_glSpan`, `commutant_commutant_permSpan`.
* `permSpan_eq_commutant_unitaryTensorSpan` — the unitary (physics) form.

The easy inclusions are proved; the two genuinely Schur–Weyl-specific facts — the GL **bridge**
`(permSpan)′ ≤ glSpan`, the **double-commutant** `(permSpan)′′ = permSpan`, and the **polarization**
`glSpan ≤ unitaryTensorSpan` — are left as `sorry` (they need Maschke + Jacobson density, which are
not imported here).
-/

namespace LeanHaar.SchurWeylV3

open scoped TensorProduct

/-!
## The bundled commutant
-/

section Commutant

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The commutant of a submodule of operators, bundled as a `Submodule` (the underlying submodule of
`Subalgebra.centralizer`, which supplies the closure proofs). -/
noncomputable def commutant (S : Submodule ℂ (Module.End ℂ M)) :
    Submodule ℂ (Module.End ℂ M) :=
  (Subalgebra.centralizer ℂ (S : Set (Module.End ℂ M))).toSubmodule

/-- Membership in `commutant S` is the commuting condition — the only place `Set`-level reasoning is
needed. -/
@[simp] lemma mem_commutant_iff {S : Submodule ℂ (Module.End ℂ M)} {X : Module.End ℂ M} :
    X ∈ commutant S ↔ ∀ Y ∈ S, Y * X = X * Y := Iff.rfl

/-- The carrier of `commutant S` is exactly `Set.centralizer ↑S`. -/
lemma coe_commutant (S : Submodule ℂ (Module.End ℂ M)) :
    (commutant S : Set (Module.End ℂ M)) = Set.centralizer (S : Set (Module.End ℂ M)) := rfl

/-- `commutant` is antitone: a bigger algebra has a smaller commutant. -/
lemma commutant_le_commutant {S T : Submodule ℂ (Module.End ℂ M)} (h : S ≤ T) :
    commutant T ≤ commutant S := by
  intro X hX
  rw [mem_commutant_iff] at hX ⊢
  exact fun Y hY => hX Y (h hY)

/-- A submodule is always contained in its double commutant. -/
lemma le_commutant_commutant (S : Submodule ℂ (Module.End ℂ M)) :
    S ≤ commutant (commutant S) := by
  intro X hX
  rw [mem_commutant_iff]
  intro Y hY
  rw [mem_commutant_iff] at hY
  exact (hY X hX).symm

end Commutant

/-!
## The two actions and their spans
-/

section Actions

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {k : ℕ}

/-- The diagonal action of `S_k = Equiv.Perm (Fin k)` on `⨂[ℂ]^k V`, permuting tensor factors via
`PiTensorProduct.reindex`. On pure tensors `W_π (⨂ᵢ fᵢ) = ⨂ᵢ f_{π⁻¹ i}`. -/
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

/-- The `k`-th tensor power `A^{⊗k}` of an operator `A : Module.End ℂ V`, acting on `⨂[ℂ]^k V` via
`PiTensorProduct.map`. On pure tensors `A^{⊗k} (⨂ᵢ fᵢ) = ⨂ᵢ A fᵢ`. -/
noncomputable def glPow (A : Module.End ℂ V) : Module.End ℂ (⨂[ℂ]^k V) :=
  PiTensorProduct.map fun _ : Fin k => A

@[simp] lemma glPow_tprod (A : Module.End ℂ V) (f : Fin k → V) :
    glPow A (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (fun i => A (f i)) := by
  simp only [glPow, PiTensorProduct.map_tprod]

/-- `Span{W_π : π ∈ S_k}` inside `Module.End ℂ (⨂[ℂ]^k V)`. -/
noncomputable def permSpan : Submodule ℂ (Module.End ℂ (⨂[ℂ]^k V)) :=
  Submodule.span ℂ (Set.range fun π : Equiv.Perm (Fin k) => permRep π)

/-- `Span{A^{⊗k} : A ∈ End ℂ V}` inside `Module.End ℂ (⨂[ℂ]^k V)`. -/
noncomputable def glSpan : Submodule ℂ (Module.End ℂ (⨂[ℂ]^k V)) :=
  Submodule.span ℂ (Set.range fun A : Module.End ℂ V => glPow A)

/-- `A^{⊗k}` commutes with the permutation operator `W_π`: both send `⨂ᵢ fᵢ ↦ ⨂ᵢ A f_{π⁻¹ i}`. -/
lemma glPow_commute_permRep (A : Module.End ℂ V) (π : Equiv.Perm (Fin k)) :
    permRep π * glPow A = glPow A * permRep π := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, glPow_tprod, permRep_tprod]

/-- **Easy direction of Schur–Weyl.** `glSpan ≤ (permSpan)′`: every `A^{⊗k}` commutes with every
`W_π`, hence with all of `permSpan`. Bundling makes this a one-level `span_le` + induction, with no
coercion. -/
lemma glSpan_le_commutant_permSpan :
    glSpan (V := V) (k := k) ≤ commutant (permSpan (V := V) (k := k)) := by
  rw [glSpan, Submodule.span_le]
  rintro _ ⟨A, rfl⟩
  rw [SetLike.mem_coe, mem_commutant_iff]
  intro Y hY
  rw [permSpan] at hY
  induction hY using Submodule.span_induction with
  | mem Y h => obtain ⟨π, rfl⟩ := h; exact glPow_commute_permRep A π
  | zero => rw [zero_mul, mul_zero]
  | add Y Z _ _ hY hZ => rw [add_mul, mul_add, hY, hZ]
  | smul c Y _ hY => rw [smul_mul_assoc, mul_smul_comm, hY]

end Actions

/-!
## Schur–Weyl duality (GL form), bundled

The easy inclusions are filled; the substantive inputs are isolated as `sorry`.
-/

section Duality

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] {k : ℕ}

/-- **Double-commutant theorem**, bundled: `(permSpan)′′ = permSpan`. The easy `≤` is general; the
reverse needs Maschke (semisimplicity) + Jacobson density. -/
theorem commutant_commutant_permSpan :
    commutant (commutant (permSpan (V := V) (k := k))) = permSpan (V := V) (k := k) := by
  refine le_antisymm ?_ (le_commutant_commutant _)
  sorry

/-- **Schur–Weyl (GL side)**, bundled: `glSpan = (permSpan)′`. The easy `≤` is
`glSpan_le_commutant_permSpan`; the reverse is the Schur–Weyl **bridge**. -/
theorem glSpan_eq_commutant_permSpan :
    glSpan (V := V) (k := k) = commutant (permSpan (V := V) (k := k)) := by
  refine le_antisymm glSpan_le_commutant_permSpan ?_
  sorry

/-- **Schur–Weyl (permutation side)**, bundled: `permSpan = (glSpan)′`. Derived from the GL side and
the double-commutant theorem, no further input. -/
theorem permSpan_eq_commutant_glSpan :
    permSpan (V := V) (k := k) = commutant (glSpan (V := V) (k := k)) := by
  rw [glSpan_eq_commutant_permSpan, commutant_commutant_permSpan]

end Duality

/-!
## Schur–Weyl duality (unitary form), bundled

The physics form `Comm(U(W)) = Span{W_π}`, over an inner-product space `W` (so the unitary group is
`W ≃ₗᵢ[ℂ] W`).
-/

section Unitary

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {k : ℕ}

/-- `Span{U^{⊗k} : U ∈ U(W)}`, the span of the `k`-th tensor powers of unitaries `U : W ≃ₗᵢ[ℂ] W`. -/
noncomputable def unitaryTensorSpan : Submodule ℂ (Module.End ℂ (⨂[ℂ]^k W)) :=
  Submodule.span ℂ (Set.range fun U : W ≃ₗᵢ[ℂ] W => glPow U.toLinearEquiv.toLinearMap)

omit [FiniteDimensional ℂ W] in
/-- The easy inclusion `unitaryTensorSpan ≤ glSpan`: every `U^{⊗k}` is an `A^{⊗k}` (take `A = U`). -/
lemma unitaryTensorSpan_le_glSpan :
    unitaryTensorSpan (W := W) (k := k) ≤ glSpan (V := W) (k := k) := by
  rw [unitaryTensorSpan, Submodule.span_le]
  rintro _ ⟨U, rfl⟩
  exact Submodule.subset_span ⟨U.toLinearEquiv.toLinearMap, rfl⟩

/-- The unitary and all-operator tensor powers span the same subspace (blueprint thm 7.11). The `≤`
is elementary; the `≥` (polarization: the unitaries span `End ℂ W`) is the substantive `sorry`. -/
lemma unitaryTensorSpan_eq_glSpan :
    unitaryTensorSpan (W := W) (k := k) = glSpan (V := W) (k := k) := by
  refine le_antisymm unitaryTensorSpan_le_glSpan ?_
  sorry

/-- **Schur–Weyl (unitary form)**, bundled: `permSpan = (unitaryTensorSpan)′`. Specialising to
`k = 1` (where `permSpan = ℂ ∙ 1`) gives the twirl / `1`-design fact `Comm(U(W)) = ℂ ∙ 1`. -/
theorem permSpan_eq_commutant_unitaryTensorSpan :
    permSpan (V := W) (k := k) = commutant (unitaryTensorSpan (W := W) (k := k)) := by
  rw [unitaryTensorSpan_eq_glSpan]
  exact permSpan_eq_commutant_glSpan

end Unitary

end LeanHaar.SchurWeylV3
