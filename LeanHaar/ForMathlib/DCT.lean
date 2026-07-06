/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Cases
import Aesop

import LeanHaar.ForMathlib.TensorV2

/-!
# Double Commutant Theorem for the Permutation Algebra

We prove that the double centralizer of `Span(permImage d k)` in `End(V^{⊗k})`
equals `Span(permImage d k)` itself. This uses Maschke's theorem (semisimplicity
of group algebra representations) and the Jacobson density theorem.
-/

noncomputable section

open scoped TensorProduct MonoidAlgebra

namespace ForMathlib.Tensor

namespace SchurWeyl

variable (d k : ℕ)

/-! ### Module.Finite for TensV -/

instance tensV_module_finite : Module.Finite ℂ (TensV d k) :=
  Module.Finite.of_basis (Basis.piTensorProduct (fun (_ : Fin k) => Pi.basisFun ℂ (Fin d)))

/-! ### The permutation representation -/

example : AddCommGroup (TensV d k) := inferInstance

/-- The permutation action as a monoid homomorphism `S_k →* End(V^{⊗k})`. -/
def permMonoidHom : Equiv.Perm (Fin k) →* Module.End ℂ (TensV d k) where
  toFun σ := (permAction d σ).toLinearMap
  map_one' := by
    refine LinearMap.ext fun x => ?_; show permAction d 1 x = x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v => simp [permAction_tprod, Equiv.Perm.one_def]
    | add x y ihx ihy => simp [map_add, ihx, ihy]
  map_mul' σ τ := by
    refine LinearMap.ext fun x => ?_
    show permAction d (σ * τ) x = permAction d σ (permAction d τ x)
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v => simp only [permAction_tprod, map_smul]; congr 1
    | add x y ihx ihy => simp [map_add, ihx, ihy]

/-- The permutation representation of `S_k` on `V^{⊗k}`. -/
abbrev permRep : Representation ℂ (Equiv.Perm (Fin k)) (TensV d k) :=
  permMonoidHom d k

/-- The natural number cardinality of `S_k` is nonzero in `ℂ` (needed for Maschke). -/
instance neZero_card_perm : NeZero (Nat.card (Equiv.Perm (Fin k)) : ℂ) := by
  constructor
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'

/-- Abbreviation for the `ℂ[S_k]`-module structure on `V^{⊗k}`. -/
abbrev PermModule := (permRep d k).asModule

noncomputable instance permModule_module : Module (MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (PermModule d k) :=
  Representation.instModuleMonoidAlgebraAsModule (permRep d k)


/-- The algebra homomorphism `ℂ[S_k] →ₐ[ℂ] End(V^{⊗k})`. -/
def permAlgHom : MonoidAlgebra ℂ (Equiv.Perm (Fin k)) →ₐ[ℂ] Module.End ℂ (TensV d k) :=
  (permRep d k).asAlgebraHom

@[simp]
theorem permAlgHom_of (σ : Equiv.Perm (Fin k)) :
    permAlgHom d k (MonoidAlgebra.of ℂ _ σ) = (permAction d σ).toLinearMap := by
  unfold permAlgHom permRep permMonoidHom
  simp [Representation.asAlgebraHom]

/-! ### Range of the algebra homomorphism equals Span(permImage) -/

/-
The image of `ℂ[S_k] →ₐ[ℂ] End(V^{⊗k})` as a submodule equals `Span(permImage)`.
-/
theorem permAlgHom_range_eq :
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
theorem mem_span_permImage_of_mem_range {f : Module.End ℂ (TensV d k)}
    (hf : f ∈ Set.range (permAlgHom d k)) :
    f ∈ (Submodule.span ℂ (permImage d k) : Submodule ℂ _) := by
  rw [← permAlgHom_range_eq d k]; exact hf

/-! ### Module.Finite condition for the density theorem -/

instance permModule_finite_over_endRing :
    Module.Finite (Module.End (MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (PermModule d k))
      (PermModule d k) :=
  Module.Finite.of_restrictScalars_finite ℂ _ _

/-! ### Connecting centralizers -/

/-
A `ℂ[S_k]`-linear endomorphism of `PermModule`, restricted to a `ℂ`-linear map,
lies in the centralizer of `Span(permImage)`.
-/
theorem endModule_mem_centralizer
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

/-- An endomorphism that commutes with all of `Span(permImage)` is `ℂ[S_k]`-linear. -/
def centralizer_to_endModule
    (f : Module.End ℂ (TensV d k))
    (hf : f ∈ (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))).centralizer) :
    Module.End (MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (PermModule d k) where
  toFun m := f m
  map_add' := f.map_add
  map_smul' r m := by
    show f ((permRep d k).asAlgebraHom r m) = (permRep d k).asAlgebraHom r (f m)
    have hr : (permRep d k).asAlgebraHom r ∈
        (Submodule.span ℂ (permImage d k) : Submodule ℂ _) := by
      rw [← permAlgHom_range_eq]; exact ⟨r, rfl⟩
    exact (congr_fun (congr_arg DFunLike.coe (hf _ hr)) m).symm

/-- An endomorphism in the double centralizer gives an `End_{ℂ[S_k]}(M)`-linear map. -/
def doubleCentralizer_to_endEndModule
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

section Bicommutant

set_option allowUnsafeReducibility true
attribute [local reducible] Representation.asModule

/-- **Double Commutant Theorem** for the permutation algebra. -/
theorem double_centralizer_permImage' :
    ((↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))).centralizer).centralizer ⊆
    (↑(Submodule.span ℂ (permImage d k)) : Set (Module.End ℂ (TensV d k))) := by
  intro T hT
  letI : Module ℂ[Equiv.Perm (Fin k)] (PermModule d k) :=
    Representation.instModuleMonoidAlgebraAsModule (permRep d k)
  haveI : IsSemisimpleModule ℂ[Equiv.Perm (Fin k)] (PermModule d k) := inferInstance
  obtain ⟨r, hr⟩ := @Module.Finite.toModuleEnd_moduleEnd_surjective
    ℂ[Equiv.Perm (Fin k)] _ (PermModule d k) _ _ _ (permModule_finite_over_endRing d k)
    (doubleCentralizer_to_endEndModule d k T hT)
  suffices h : T = permAlgHom d k r by
    rw [h]; exact mem_span_permImage_of_mem_range d k ⟨r, rfl⟩
  refine LinearMap.ext fun m => ?_
  have := congr_fun (congr_arg DFunLike.coe hr) m
  -- this should give: (Module.toModuleEnd ... r) m = (doubleCentralizer_to_endEndModule ...) m
  -- i.e., r • m = T m (in PermModule), and r • m = permAlgHom(r)(m)
  simp only [Module.toModuleEnd_apply] at this
  -- Now this should be: r • m = T m, where r • m in PermModule = permAlgHom(r)(m)
  exact this.symm

end Bicommutant

end SchurWeyl

end ForMathlib.Tensor

end
