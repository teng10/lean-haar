import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Complex.Polynomial.Basic
import QuantumInfo.States.Pure.Qubit

/-!
# Commutant of `U(2)` via Schur's lemma

This file proves, **directly from Schur's lemma**
```
{M : End ℂ (Fin 2 → ℂ) | ∀ U ∈ U(2), M U = U M} = {λ • 1 | λ ∈ ℂ}.
```

## Design

* The group is Physlib's `𝐔[Qubit] = Matrix.unitaryGroup (Fin 2) ℂ`, acting on `Fin 2 → ℂ` by
  `Matrix.toLin'` — the *defining* representation `stdRep`.
* The space `{M | ∀ U, M * stdRep U = stdRep U * M}` is exactly the carrier of
  `IntertwiningMap stdRep stdRep`, the self-intertwiners of `stdRep`.
* Mathlib's Schur's lemma in the unbundled form
  `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed` says that over
  an algebraically closed field the algebra map `ℂ → IntertwiningMap stdRep stdRep`, `c ↦ c • 1`, is
  **bijective** — i.e. every self-intertwiner is a unique scalar.
* The only substantive input is **irreducibility** of `stdRep`, which is *not* in Mathlib. We prove
  it with Physlib's Pauli gates `Qubit.Z`, `Qubit.X`: `Z` (via the eigen-projections `(1 ± Z)/2`)
  extracts a coordinate of any nonzero vector, and `X` (the swap) turns one basis vector into the
  other. This is the irreducible mathematical content — an invariant line would be a common
  eigenvector of every unitary, but `X` and `Z` share none.
-/

namespace LeanHaar.SchurUnitary

open Matrix Representation

/-! ## The defining representation `stdRep` of `U(2)` on `ℂ²` -/

/-- The defining representation of `𝐔[Qubit] = U(2)` on `ℂ² = Fin 2 → ℂ`: a unitary `U` acts by
matrix-vector multiplication `v ↦ U *ᵥ v`. -/
noncomputable def stdRep : Representation ℂ 𝐔[Qubit] (Fin 2 → ℂ) where
  toFun U := Matrix.toLin' (U : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by ext v; simp
  map_mul' U V := by ext v; simp [Module.End.mul_apply]

@[simp] lemma stdRep_apply (U : 𝐔[Qubit]) (v : Fin 2 → ℂ) :
    stdRep U v = (U : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v :=
  Matrix.toLin'_apply _ _

/-- Action of the Pauli `Z = diag(1, -1)` on a vector. -/
lemma stdRep_Z (v : Fin 2 → ℂ) : stdRep Qubit.Z v = ![v 0, -v 1] := by
  funext i; fin_cases i <;> simp [Qubit.Z, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Action of the Pauli `X` (the swap) on a vector. -/
lemma stdRep_X (v : Fin 2 → ℂ) : stdRep Qubit.X v = ![v 1, v 0] := by
  funext i; fin_cases i <;> simp [Qubit.X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ## Irreducibility of `stdRep` -/

/-- If a submodule of `ℂ²` contains both standard basis vectors, it is everything. -/
private lemma eq_top_of_basis_mem (N : Submodule ℂ (Fin 2 → ℂ))
    (h0 : (![1, 0] : Fin 2 → ℂ) ∈ N) (h1 : (![0, 1] : Fin 2 → ℂ) ∈ N) : N = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x = x 0 • (![1, 0] : Fin 2 → ℂ) + x 1 • ![0, 1] := by
    funext i; fin_cases i <;> simp
  rw [hx]
  exact N.add_mem (N.smul_mem _ h0) (N.smul_mem _ h1)

/-- **Irreducibility** of the defining representation of `U(2)` on `ℂ²`. -/
instance : Representation.IsIrreducible stdRep := by
  -- `ℂ²` is nontrivial, so `⊥ ≠ ⊤`.
  haveI : Nontrivial (Subrepresentation stdRep) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun S => ?_⟩
  set N := S.toSubmodule
  rcases eq_or_ne N ⊥ with hbot | hbot
  · exact Or.inl (Subrepresentation.toSubmodule_injective hbot)
  refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
  show N = ⊤
  -- Any `![a, 0] ∈ N` with `a ≠ 0` already forces `N = ⊤`: normalize to `![1,0]`, `X`-swap to
  -- `![0,1]`.
  have key : ∀ a : ℂ, a ≠ 0 → (![a, 0] : Fin 2 → ℂ) ∈ N → N = ⊤ := by
    intro a ha hmem
    have e0 : (![1, 0] : Fin 2 → ℂ) ∈ N := by
      have h := N.smul_mem a⁻¹ hmem
      rwa [show a⁻¹ • (![a, 0] : Fin 2 → ℂ) = ![1, 0] from by
        funext i; fin_cases i <;> simp [inv_mul_cancel₀ ha]] at h
    have e1 : (![0, 1] : Fin 2 → ℂ) ∈ N := by
      have h := S.apply_mem_toSubmodule Qubit.X e0
      rw [stdRep_X] at h; simpa using h
    exact eq_top_of_basis_mem N e0 e1
  -- Pick a nonzero `v ∈ N`; its `Z`-eigen-projections `(v ± Z v)/2 = ![v 0, 0]`, `![0, v 1]`
  -- lie in `N`.
  obtain ⟨v, hvN, hv0⟩ := (Submodule.ne_bot_iff N).1 hbot
  have hZ : (![v 0, -v 1] : Fin 2 → ℂ) ∈ N := by
    have := S.apply_mem_toSubmodule Qubit.Z hvN; rwa [stdRep_Z] at this
  have hp0 : (![v 0, 0] : Fin 2 → ℂ) ∈ N := by
    have heq : (2⁻¹ : ℂ) • (v + ![v 0, -v 1]) = ![v 0, 0] := by
      funext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail]
      ring
    rw [← heq]; exact N.smul_mem _ (N.add_mem hvN hZ)
  have hp1 : (![0, v 1] : Fin 2 → ℂ) ∈ N := by
    have heq : (2⁻¹ : ℂ) • (v - ![v 0, -v 1]) = ![0, v 1] := by
      funext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail]
      ring
    rw [← heq]; exact N.smul_mem _ (N.sub_mem hvN hZ)
  -- One coordinate of `v` is nonzero; reduce both cases to `key` (for `v 1`, `X`-swap `![0, v 1]`
  -- into `![v 1, 0]` first).
  rcases eq_or_ne (v 0) 0 with h0 | h0
  · refine key (v 1) (fun hv1 => hv0 ?_) ?_
    · funext i; fin_cases i <;> simp [h0, hv1]
    · have h := S.apply_mem_toSubmodule Qubit.X hp1
      rw [stdRep_X] at h; simpa using h
  · exact key (v 0) h0 hp0

/-! ## The theorem: the commutant of `U(2)` is the scalars -/

/-- **Commutant of `U(2)` is the scalars.** An operator `M` on `ℂ²` commutes with every unitary
`U ∈ U(2)` iff `M = c • 1` for some `c ∈ ℂ`. This is Schur's lemma: such an `M` is a self-intertwiner
of the (irreducible) defining representation, and over `ℂ` every self-intertwiner is a scalar. -/
theorem commutant_eq_scalars (M : Module.End ℂ (Fin 2 → ℂ)) :
    (∀ U : 𝐔[Qubit], M * stdRep U = stdRep U * M) ↔ ∃ c : ℂ, M = c • 1 := by
  constructor
  · intro hM
    -- package `M` as a self-intertwiner of `stdRep`
    have hf : ∀ (U : 𝐔[Qubit]) (v : Fin 2 → ℂ), M (stdRep U v) = stdRep U (M v) := by
      intro U v
      have h := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T v) (hM U)
      simpa [Module.End.mul_apply] using h
    let f : IntertwiningMap stdRep stdRep :=
      LinearMap.intertwiningMap_of_isIntertwiningMap stdRep stdRep M hf
    -- Schur: `c ↦ c • 1` is onto the self-intertwiners, so `f = c • 1` for some `c`
    obtain ⟨c, hc⟩ :=
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := stdRep)).2 f
    refine ⟨c, ?_⟩
    calc M = f.toLinearMap := rfl
      _ = (algebraMap ℂ (IntertwiningMap stdRep stdRep) c).toLinearMap := by rw [hc]
      _ = c • 1 := rfl
  · rintro ⟨c, rfl⟩ U
    rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- The commutant of `U(2)`, in set form, is exactly the scalar multiples of the identity. -/
theorem commutant_set_eq :
    {M : Module.End ℂ (Fin 2 → ℂ) | ∀ U : 𝐔[Qubit], M * stdRep U = stdRep U * M}
      = {M : Module.End ℂ (Fin 2 → ℂ) | ∃ c : ℂ, M = c • 1} := by
  ext M
  simp only [Set.mem_setOf_eq]
  exact commutant_eq_scalars M

end LeanHaar.SchurUnitary
