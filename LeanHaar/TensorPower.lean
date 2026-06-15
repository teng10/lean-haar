import LeanHaar.HilbertSpace
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Tensor powers of finite Hilbert spaces

This file defines `HilbertTensorPower d k`, the `k`-fold tensor power of the finite Hilbert
space `𝓗[d]`, as a structure wrapping Mathlib's homogeneous tensor power `⨂[ℂ]^k 𝓗[d]`
(itself a `PiTensorProduct`).

Like `FiniteHilbertSpace` in `Defs.lean`, it is a single-field structure wrapping an existing
Mathlib type. Wrapping — rather than using an `abbrev` — keeps every transferred instance, and
later the inner product, local to this type instead of leaking onto *every* `PiTensorProduct`
of the same shape.

## Main definitions

* `HilbertTensorPower d k` — the wrapper type, with notation `𝓗⊗[d, k]`.
* `HilbertTensorPower.equivTensorPower` — the underlying equivalence to `⨂[ℂ]^k 𝓗[d]`.
* `HilbertTensorPower.linearEquivTensorPower` — the same as a `ℂ`-linear equivalence; this is the
  bridge through which the full `PiTensorProduct` API (`tprod`, `reindex`, `map`, …) is reused.

## Scope

This file sets up the `ℂ`-vector space structure only (Layer 0). The permutation operator `W_π`,
the inner product, and unitarity are built in later files on top of `linearEquivTensorPower`.

## Conventions

The permutation operator `W_π` (Layer 1, built on `PiTensorProduct.reindex`) will use the
convention
```
W_π (ψ₁ ⊗ ⋯ ⊗ ψ_k) = ψ_{π⁻¹ 1} ⊗ ⋯ ⊗ ψ_{π⁻¹ k},
```
i.e. the new slot `i` receives the factor from old slot `π⁻¹ i`. This matches the blueprint and,
crucially, makes `π ↦ W_π` a group *homomorphism* (`W_π ∘ W_σ = W_{π * σ}`) rather than an
anti-homomorphism — so the downstream `S_k`-action arguments come out the right way round.

`PiTensorProduct.reindex ℂ _ π` already implements exactly this, because
`reindex π (tprod f) = tprod (f ∘ π.symm)`. There is **no** manual `π⁻¹`: do not try to "match"
the `π⁻¹` visible in the formula by passing `π⁻¹` to `reindex`, as that gives the opposite
(anti-homomorphism) convention.
-/

namespace LeanHaar

open scoped TensorProduct

/-- The `k`-fold tensor power of the finite Hilbert space `𝓗[d]`, realized as a structure
wrapping Mathlib's homogeneous tensor power `⨂[ℂ]^k 𝓗[d]` (itself a `PiTensorProduct`).

All algebraic structure is transferred from the underlying tensor power along
`equivTensorPower`. We use the notation `𝓗⊗[d, k]`. -/
@[ext]
structure HilbertTensorPower (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) where
  /-- The underlying element of the Mathlib tensor power `⨂[ℂ]^k 𝓗[d]`. -/
  val : ⨂[ℂ]^k (FiniteHilbertSpace d)

@[inherit_doc HilbertTensorPower]
scoped notation:max "𝓗⊗[" d ", " k "]" => HilbertTensorPower d k

namespace HilbertTensorPower

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-- The equivalence between `𝓗⊗[d, k]` and the underlying tensor power `⨂[ℂ]^k 𝓗[d]`,
given by `val`. -/
def equivTensorPower : 𝓗⊗[d, k] ≃ ⨂[ℂ]^k (FiniteHilbertSpace d) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-!
## The `ℂ`-vector space structure

The vector space structure is transferred from `⨂[ℂ]^k 𝓗[d]` along `equivTensorPower`.
-/

noncomputable instance : AddCommGroup (𝓗⊗[d, k]) := equivTensorPower.addCommGroup

noncomputable instance : Module ℂ (𝓗⊗[d, k]) := equivTensorPower.module ℂ

@[simp] lemma val_add (x y : 𝓗⊗[d, k]) : (x + y).val = x.val + y.val := rfl

@[simp] lemma val_smul (c : ℂ) (x : 𝓗⊗[d, k]) : (c • x).val = c • x.val := rfl

@[simp] lemma val_zero : (0 : 𝓗⊗[d, k]).val = 0 := rfl

@[simp] lemma val_neg (x : 𝓗⊗[d, k]) : (-x).val = -x.val := rfl

@[simp] lemma val_sub (x y : 𝓗⊗[d, k]) : (x - y).val = x.val - y.val := rfl

/-- `equivTensorPower` as a `ℂ`-linear equivalence, upgrading the bare equivalence.

This is the canonical bridge to Mathlib's `PiTensorProduct` API: pure tensors (`tprod`),
`reindex` (for the permutation operator) and `map` (for tensor powers of operators) are accessed
by transporting along this equivalence. -/
noncomputable def linearEquivTensorPower : 𝓗⊗[d, k] ≃ₗ[ℂ] ⨂[ℂ]^k (FiniteHilbertSpace d) :=
  { equivTensorPower with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp] lemma linearEquivTensorPower_apply (x : 𝓗⊗[d, k]) :
    linearEquivTensorPower x = x.val := rfl

@[simp] lemma linearEquivTensorPower_symm_apply (x : ⨂[ℂ]^k (FiniteHilbertSpace d)) :
    linearEquivTensorPower.symm x = ⟨x⟩ := rfl

/-!
## Finite-dimensionality

`⨂[ℂ]^k 𝓗[d]` has the basis `Basis.piTensorProduct` indexed by multi-indices `Fin k → d`,
which we transport to `𝓗⊗[d, k]` along `linearEquivTensorPower`. Being a finite basis, this makes
the space finite dimensional.
-/

instance : FiniteDimensional ℂ (𝓗⊗[d, k]) :=
  Module.Finite.of_basis
    ((Basis.piTensorProduct fun _ : Fin k => (FiniteHilbertSpace.basisFun d).toBasis).map
      linearEquivTensorPower.symm)

/-!
## Pure tensors

`tprod ψ` is the pure (decomposable) tensor `ψ 1 ⊗ ⋯ ⊗ ψ k`, the wrapper-level counterpart of
`PiTensorProduct.tprod`. Pure tensors span `𝓗⊗[d, k]`, so it suffices to specify operators on them.
-/

/-- The pure tensor `ψ 1 ⊗ ⋯ ⊗ ψ k` as an element of `𝓗⊗[d, k]`. -/
noncomputable def tprod (ψ : Fin k → FiniteHilbertSpace d) : 𝓗⊗[d, k] :=
  ⟨PiTensorProduct.tprod ℂ ψ⟩

@[simp] lemma val_tprod (ψ : Fin k → FiniteHilbertSpace d) :
    (tprod ψ).val = PiTensorProduct.tprod ℂ ψ := rfl

@[simp] lemma linearEquivTensorPower_tprod (ψ : Fin k → FiniteHilbertSpace d) :
    linearEquivTensorPower (tprod ψ) = PiTensorProduct.tprod ℂ ψ := rfl

@[simp] lemma linearEquivTensorPower_symm_tprod (ψ : Fin k → FiniteHilbertSpace d) :
    linearEquivTensorPower.symm (PiTensorProduct.tprod ℂ ψ) = tprod ψ := rfl

/-- Linear maps out of `𝓗⊗[d, k]` are determined by their action on pure tensors: this is the
universal property of the tensor product, transported through `linearEquivTensorPower`. -/
lemma hom_ext {M : Type*} [AddCommMonoid M] [Module ℂ M] {f g : 𝓗⊗[d, k] →ₗ[ℂ] M}
    (h : ∀ ψ : Fin k → FiniteHilbertSpace d, f (tprod ψ) = g (tprod ψ)) : f = g := by
  have key : f ∘ₗ linearEquivTensorPower.symm.toLinearMap
      = g ∘ₗ linearEquivTensorPower.symm.toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    -- `(f ∘ₗ L.symm) (tprod ℂ ψ)` is defeq to `f (tprod ψ)`, so `h ψ` closes it directly.
    intro ψ
    exact h ψ
  ext x
  simpa using LinearMap.congr_fun key (linearEquivTensorPower x)


end HilbertTensorPower

end LeanHaar
