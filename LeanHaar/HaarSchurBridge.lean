import LeanHaar.SchurWeylAbstract
import LeanHaar.HaarMoments

/-!
# Bridge: Haar twirl ⟶ Schur–Weyl commutant ⟶ moments

This file connects the Haar-twirl properties (the `HaarMoments.IsHaarTwirl` hypotheses) to the
Schur–Weyl development (`SchurWeylAbstract`), abstractly over a finite-dimensional inner product
space `W`.

The substantive step is **Schur–Weyl** in *generator form*: an operator lies in `permSpan` iff it
commutes with the `k`-th tensor power `U^{⊗k}` of every unitary `U` (`mem_permSpan_iff_commute`).
This is the abstract version of `UnitaryCommutants.commutant_unitary_eq_permSpan` (the `W := 𝓗[d]`
special case). Commuting with every `U^{⊗k}` is exactly what an actual Haar twirl
`∫ U^{⊗k} O U^{†⊗k} dμ` satisfies (by left-invariance of `μ`), so feeding that through the bridge
yields the `IsHaarTwirl` hypothesis the moment corollaries (in `Examples/UnitaryMoments.lean`)
consume.

## Main results

* `mem_permSpan_iff_commute` — generator-form Schur–Weyl, abstract in `W`.
* `isHaarTwirl_permSpan` — commuting with every `U^{⊗k}` + trace-matching ⟹ `IsHaarTwirl 𝒯 permSpan`.

The `k`-specific corollaries built on this (e.g. the end-to-end first moment) live in
`Examples/UnitaryMoments.lean`.
-/

open scoped TensorProduct
open Module LeanHaar.SchurWeylAbstract LeanHaar.HaarMoments

namespace LeanHaar.HaarSchurBridge

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {k : ℕ}

/-- General algebra fact: commuting with a span equals commuting with its generators. (Same content
as `LeanHaar.centralizer_span` in `UnitaryCommutants`; kept here so the abstract bridge does not
depend on the concrete `𝓗[d]` file. Worth consolidating into one abstract location.) -/
lemma centralizer_span {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (S : Set A) :
    Set.centralizer (Submodule.span R S : Set A) = Set.centralizer S := by
  ext x
  simp only [Set.mem_centralizer_iff]
  refine ⟨fun h y hy => h y (Submodule.subset_span hy), fun h y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => rw [zero_mul, mul_zero]
  | add y z _ _ hy hz => rw [add_mul, mul_add, hy, hz]
  | smul c y _ hy => rw [smul_mul_assoc, mul_smul_comm, hy]

/-- **Schur–Weyl in generator form** (abstract). `M` lies in `permSpan` iff it commutes with the
`k`-th tensor power `U^{⊗k}` of every unitary `U : W ≃ₗᵢ[ℂ] W`.

This is the abstract counterpart of `UnitaryCommutants.commutant_unitary_eq_permSpan`, which is the
special case `W := 𝓗[d]` (re-packaged as a set equality). -/
theorem mem_permSpan_iff_commute (M : Module.End ℂ (⨂[ℂ]^k W)) :
    M ∈ permSpan (V := W) (k := k) ↔
      ∀ U : W ≃ₗᵢ[ℂ] W,
        M * glPow U.toLinearEquiv.toLinearMap = glPow U.toLinearEquiv.toLinearMap * M := by
  have h := permSpan_eq_centralizer_unitaryTensorSpan (W := W) (k := k)
  rw [unitaryTensorSpan, centralizer_span] at h
  rw [← SetLike.mem_coe, h, Set.mem_centralizer_iff]
  refine ⟨fun hM U => (hM _ ⟨U, rfl⟩).symm, ?_⟩
  rintro hM x ⟨U, rfl⟩
  exact (hM U).symm

/-- **The bridge.** If `𝒯 O` commutes with every unitary tensor power `U^{⊗k}` and `𝒯` preserves
trace pairings against the permutation operators, then `𝒯` is a Haar twirl onto `permSpan`.

The first hypothesis is exactly what an actual Haar twirl satisfies (commuting with every unitary, by
left-invariance); the second is the trace-matching consequence of Haar invariance. Membership in
`permSpan` is provided by `mem_permSpan_iff_commute` (generator-form Schur–Weyl). -/
theorem isHaarTwirl_permSpan
    (𝒯 : Module.End ℂ (⨂[ℂ]^k W) →ₗ[ℂ] Module.End ℂ (⨂[ℂ]^k W))
    (hmem : ∀ O, ∀ U : W ≃ₗᵢ[ℂ] W,
      𝒯 O * glPow U.toLinearEquiv.toLinearMap = glPow U.toLinearEquiv.toLinearMap * 𝒯 O)
    (htrace : ∀ B ∈ permSpan (V := W) (k := k), ∀ O,
      LinearMap.trace ℂ (⨂[ℂ]^k W) (B * 𝒯 O) = LinearMap.trace ℂ (⨂[ℂ]^k W) (B * O)) :
    IsHaarTwirl 𝒯 (permSpan (V := W) (k := k)) :=
  ⟨fun O => (mem_permSpan_iff_commute (𝒯 O)).2 (hmem O), htrace⟩

end LeanHaar.HaarSchurBridge
