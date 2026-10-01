/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aesop
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Tactic

import LeanHaar.ForMathlib.TensorPower.Matrix

/-!
# Double Commutant Theorem for the Permutation Algebra

We prove that the double centralizer of `Span(permImage d k)` in `End(V^{⊗k})`
equals `Span(permImage d k)` itself. This uses Maschke's theorem (semisimplicity
of group algebra representations) and the Jacobson density theorem.

The public tensor permutation operators are defined in `TensorPower`. This proof
privately packages their action as a representation and a group-algebra module
to apply Mathlib's semisimplicity and density results. These adapters and the
auxiliary density constructions are implementation details of this file.
-/

noncomputable section

open scoped TensorProduct MonoidAlgebra

namespace SchurWeyl

variable (d k : ℕ)

/-! ### Private group-algebra adapters -/

/-- The permutation representation of `S_k` on the tensor power, obtained by
forgetting the inverses in `permAction`. -/
private def permRep : Representation ℂ (Equiv.Perm (Fin k)) (TensV d k) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (permAction d k)

/-- Abbreviation for the `ℂ[S_k]`-module structure on `V^{⊗k}`. -/
private abbrev PermModule := (permRep d k).asModule

/-- The algebra homomorphism `ℂ[S_k] →ₐ[ℂ] End(V^{⊗k})`. -/
private def permAlgHom : MonoidAlgebra ℂ (Equiv.Perm (Fin k)) →ₐ[ℂ] Module.End ℂ (TensV d k) :=
  (permRep d k).asAlgebraHom

private theorem permAlgHom_of (σ : Equiv.Perm (Fin k)) :
    permAlgHom d k (MonoidAlgebra.of ℂ _ σ) = (permAction d k σ).toLinearMap :=
  (permRep d k).asAlgebraHom_of σ

/-! ### Range of the algebra homomorphism equals Span(permImage) -/

/-
The image of `ℂ[S_k] →ₐ[ℂ] End(V^{⊗k})` as a submodule equals `Span(permImage)`.
-/
private theorem permAlgHom_range_eq :
    (permAlgHom d k).range.toSubmodule = Submodule.span ℂ (permImage d k) := by
  refine' le_antisymm _ _ <;> intro x <;> simp_all +decide [ Submodule.mem_span ];
  · rintro x rfl p hp; exact (by
    induction' x using MonoidAlgebra.induction_on with x y hx hy;
    · convert hp ⟨ x, rfl ⟩ using 1;
      convert permAlgHom_of d k x using 1;
    · simpa using p.add_mem hy ‹_›;
    · aesop);
  · intro hx;
    contrapose! hx;
    refine' ⟨ Submodule.map ( permAlgHom d k |> AlgHom.toLinearMap ) ⊤, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
    rintro _ ⟨ σ, rfl ⟩ ; exact ⟨ MonoidAlgebra.of ℂ _ σ, permAlgHom_of d k σ ⟩ ;

/-- Every element in the range of `permAlgHom` is in `Span(permImage)`. -/
private theorem mem_span_permImage_of_mem_range {f : Module.End ℂ (TensV d k)}
    (hf : f ∈ Set.range (permAlgHom d k)) :
    f ∈ (Submodule.span ℂ (permImage d k) : Submodule ℂ _) := by
  rw [← permAlgHom_range_eq d k]; exact hf

/-! ### Local hypotheses for Maschke and density -/

/-- The natural number cardinality of `S_k` is nonzero in `ℂ` (needed for Maschke). -/
local instance neZero_card_perm : NeZero (Nat.card (Equiv.Perm (Fin k)) : ℂ) := by
  constructor
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'

/-! ### Module.Finite condition for the density theorem -/

local instance permModule_finite_over_endRing :
    Module.Finite (Module.End (MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (PermModule d k))
      (PermModule d k) :=
  Module.Finite.of_restrictScalars_finite ℂ _ _

/-! ### Connecting centralizers -/

/-
A `ℂ[S_k]`-linear endomorphism of `PermModule`, restricted to a `ℂ`-linear map,
lies in the centralizer of `Span(permImage)`.
-/
private theorem endModule_mem_centralizer
    (f : Module.End (MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (PermModule d k)) :
    (f.restrictScalars ℂ : Module.End ℂ (TensV d k)) ∈
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))).centralizer := by
  intro g hg;
  induction hg using Submodule.span_induction;
  · obtain ⟨ σ, rfl ⟩ := ‹_›;
    convert f.map_smul' ( MonoidAlgebra.of ℂ ( Equiv.Perm ( Fin k ) ) σ ) using 1;
    simp +decide [ LinearMap.ext_iff ];
    convert Iff.rfl;
    constructor <;> intro h x <;> convert h ( ( permRep d k ).asModuleEquiv.symm x ) using 1;
    · convert h ( ( permRep d k ).asModuleEquiv.symm x ) |> Eq.symm using 1;
    · convert h ( ( permRep d k ).asModuleEquiv.symm x ) using 1;
    · convert h ( ( permRep d k ).asModuleEquiv x ) |> Eq.symm using 1;
    · convert h ( ( permRep d k ).asModuleEquiv x ) using 1;
  · aesop;
  · simp_all +decide [ add_mul, mul_add ];
  · simp_all +decide

/-- An endomorphism in the double centralizer gives an `End_{ℂ[S_k]}(M)`-linear map. -/
private def doubleCentralizerToEndEndModule
    (T : Module.End ℂ (TensV d k))
    (hT : T ∈ ((↑(Submodule.span ℂ (permImage d k)) : Set _).centralizer).centralizer) :
    Module.End (Module.End (MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (PermModule d k))
      (PermModule d k) where
  toFun m := T m
  map_add' := T.map_add
  map_smul' f m := by
    show T (f m) = f (T m)
    have hf_cen := endModule_mem_centralizer d k f
    exact (congr_fun (congr_arg DFunLike.coe (hT _ hf_cen)) m).symm

/-! ### The Double Commutant Theorem -/

/-- `PermModule` is a semisimple `ℂ[S_k]`-module (Maschke's theorem).

We pin down the `AddCommGroup`/`Module` instances explicitly: in current Mathlib
the generic `Representation.asModule` carries an `AddCommMonoid` derived directly
from the base module together with an `AddCommGroup` that is only *defeq* to it,
and typeclass search does not always reconcile the two when the `AddCommGroup`
variant is forced first (as happens inside `IsSemisimpleModule`). Supplying the
instances by hand avoids that resolution gap. -/
private theorem permModule_isSemisimple :
    @IsSemisimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin k))) _ (PermModule d k)
      (Representation.instAddCommGroupAsModule (permRep d k))
      (Representation.instModuleMonoidAlgebraAsModule (permRep d k)) :=
  inferInstance

/-- Surjectivity of `Module.toModuleEnd : ℂ[S_k] → End_{End}(PermModule)`.
This is the Jacobson density input to the double commutant theorem. The instance
arguments are supplied explicitly for the same reason as in
`permModule_isSemisimple`. -/
private theorem permModule_toModuleEnd_surjective :
    Function.Surjective (Module.toModuleEnd
      (Module.End (MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (PermModule d k))
      (S := MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (PermModule d k)) :=
  @Module.Finite.toModuleEnd_moduleEnd_surjective
    (MonoidAlgebra ℂ (Equiv.Perm (Fin k))) _ (PermModule d k)
    (Representation.instAddCommGroupAsModule (permRep d k))
    (Representation.instModuleMonoidAlgebraAsModule (permRep d k))
    (permModule_isSemisimple d k)
    (permModule_finite_over_endRing d k)

/-- **Double Commutant Theorem** for the permutation algebra. -/
theorem double_centralizer_permImage {d k : ℕ} :
    ((↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))).centralizer).centralizer ⊆
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) := by
  intro T hT
  obtain ⟨r, hr⟩ := permModule_toModuleEnd_surjective d k
    (doubleCentralizerToEndEndModule d k T hT)
  suffices h : T = permAlgHom d k r by
    rw [h]; exact mem_span_permImage_of_mem_range d k ⟨r, rfl⟩
  refine LinearMap.ext fun m => ?_
  have := congr_fun (congr_arg DFunLike.coe hr) m
  -- Evaluate the equality of module endomorphisms on the underlying tensor space.
  simp only [Module.toModuleEnd_apply] at this
  exact this.symm

end SchurWeyl

end
