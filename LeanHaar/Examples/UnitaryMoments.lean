import LeanHaar.HaarSchurBridge
import Mathlib.LinearAlgebra.Span.Basic

/-!
# First and second moments of the Haar twirl

The bridge between Schur–Weyl duality and the Haar moment twirl, at `k = 1` and `k = 2`. The chain is
the same both times:

`𝒯` commutes with every `U^{⊗k}` + trace-matches  ⟹  `IsHaarTwirl 𝒯 permSpan`  (Schur, via
`isHaarTwirl_permSpan`)  ⟹  `IsHaarTwirl 𝒯 span{…}`  (`permSpan_one`/`permSpan_two`)  ⟹  the explicit
moment formula (the `1×1`/`2×2` linear solve).

## The four results

* `permSpan_one` / `permSpan_two` — the commutant `permSpan` at `k = 1` / `k = 2` *is* the span of the
  permutation operators: `span{1}`, resp. `span{1, F}` with `F` the swap.
* `firstMoment` / `secondMoment` — the twirl, characterized via Schur–Weyl, equals `(Tr O / d) • 1`,
  resp. the Corollary 13 `(c_I, c_F)` formula.
-/

open Module
open scoped TensorProduct
open LeanHaar.HaarMoments LeanHaar.SchurWeylAbstract LeanHaar.HaarSchurBridge

namespace LeanHaar.Examples.UnitaryMoments

/-! ## The permutation-operator span at `k = 1` and `k = 2` -/

section PermSpan

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- At `k = 1`, `S₁` is trivial, so the commutant is the scalar line `span{1}`. -/
theorem permSpan_one :
    permSpan (V := V) (k := 1) = Submodule.span ℂ {(1 : Module.End ℂ (⨂[ℂ]^1 V))} := by
  unfold permSpan
  congr 1
  ext Y
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨π, rfl⟩; rw [Subsingleton.elim π 1]; exact map_one permRep
  · rintro rfl; exact ⟨1, map_one permRep⟩

/-- At `k = 2`, `S₂ = {1, swap}`, so the commutant is `span{1, F}` with `F` the swap operator. -/
theorem permSpan_two :
    permSpan (V := V) (k := 2)
      = Submodule.span ℂ {1, permRep (Equiv.swap (0 : Fin 2) 1)} := by
  have key : ∀ σ : Equiv.Perm (Fin 2), σ = 1 ∨ σ = Equiv.swap (0 : Fin 2) 1 := by decide
  unfold permSpan
  congr 1
  ext Y
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨π, rfl⟩
    rcases key π with rfl | rfl
    · exact Or.inl (map_one permRep)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, map_one permRep⟩
    · exact ⟨Equiv.swap (0 : Fin 2) 1, rfl⟩

end PermSpan

/-! ## The linear-equation solves (within a finite-dimensional commutant) -/

section Solve

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Module.Free ℂ V]

/-- `Tr(1) = dim V`. -/
@[simp] lemma trace_one_End :
    LinearMap.trace ℂ V (1 : Module.End ℂ V) = (finrank ℂ V : ℂ) :=
  LinearMap.trace_one ℂ V

omit [Module.Finite ℂ V] [Module.Free ℂ V] in
/-- Expand `Tr(B · (a•A + b•C))` by bilinearity. -/
private lemma trace_mul_smul_add (B A C : Module.End ℂ V) (a b : ℂ) :
    LinearMap.trace ℂ V (B * (a • A + b • C)) =
      a * LinearMap.trace ℂ V (B * A) + b * LinearMap.trace ℂ V (B * C) := by
  rw [mul_add, mul_smul_comm, mul_smul_comm, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

omit [Module.Finite ℂ V] [Module.Free ℂ V] in
/-- **1×1 solve.** Commutant `span{A}`: the twirl is the single trace ratio. -/
theorem eq_smul_singleton {𝒯 : Module.End ℂ V →ₗ[ℂ] Module.End ℂ V}
    {A : Module.End ℂ V} (h : IsHaarTwirl 𝒯 (Submodule.span ℂ {A}))
    (hAA : LinearMap.trace ℂ V (A * A) ≠ 0) (O : Module.End ℂ V) :
    𝒯 O = (LinearMap.trace ℂ V (A * O) / LinearMap.trace ℂ V (A * A)) • A := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h.mem O)
  have hm := h.trace_match A (Submodule.mem_span_singleton_self A) O
  rw [← hc] at hm ⊢
  rw [mul_smul_comm, map_smul, smul_eq_mul] at hm
  congr 1
  rw [eq_div_iff hAA]
  linear_combination hm

omit [Module.Finite ℂ V] [Module.Free ℂ V] in
/-- **2×2 solve.** Commutant `span{A, B}` with nonzero Gram determinant: the twirl is the Cramer
solution of the trace-pairing system. -/
theorem eq_of_pair {𝒯 : Module.End ℂ V →ₗ[ℂ] Module.End ℂ V}
    {A B : Module.End ℂ V} (h : IsHaarTwirl 𝒯 (Submodule.span ℂ {A, B}))
    (hdet : LinearMap.trace ℂ V (A * A) * LinearMap.trace ℂ V (B * B)
          - LinearMap.trace ℂ V (A * B) * LinearMap.trace ℂ V (B * A) ≠ 0)
    (O : Module.End ℂ V) :
    𝒯 O =
      ((LinearMap.trace ℂ V (A * O) * LinearMap.trace ℂ V (B * B)
          - LinearMap.trace ℂ V (B * O) * LinearMap.trace ℂ V (A * B))
        / (LinearMap.trace ℂ V (A * A) * LinearMap.trace ℂ V (B * B)
          - LinearMap.trace ℂ V (A * B) * LinearMap.trace ℂ V (B * A))) • A
    + ((LinearMap.trace ℂ V (A * A) * LinearMap.trace ℂ V (B * O)
          - LinearMap.trace ℂ V (B * A) * LinearMap.trace ℂ V (A * O))
        / (LinearMap.trace ℂ V (A * A) * LinearMap.trace ℂ V (B * B)
          - LinearMap.trace ℂ V (A * B) * LinearMap.trace ℂ V (B * A))) • B := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (h.mem O)
  have hmA := h.trace_match A (Submodule.subset_span (Set.mem_insert A {B})) O
  have hmB := h.trace_match B (Submodule.subset_span (Set.mem_insert_of_mem A rfl)) O
  rw [← hab, trace_mul_smul_add] at hmA hmB
  rw [← hab]
  set g11 := LinearMap.trace ℂ V (A * A)
  set g12 := LinearMap.trace ℂ V (A * B)
  set g21 := LinearMap.trace ℂ V (B * A)
  set g22 := LinearMap.trace ℂ V (B * B)
  set r1 := LinearMap.trace ℂ V (A * O)
  set r2 := LinearMap.trace ℂ V (B * O)
  have ha : a = (r1 * g22 - r2 * g12) / (g11 * g22 - g12 * g21) := by
    rw [eq_div_iff hdet]; linear_combination g22 * hmA - g12 * hmB
  have hb : b = (g11 * r2 - g21 * r1) / (g11 * g22 - g12 * g21) := by
    rw [eq_div_iff hdet]; linear_combination g11 * hmB - g21 * hmA
  rw [ha, hb]

end Solve

/-! ## The moments: Schur–Weyl ⟶ twirl formula -/

section Moments

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- **First moment.** A twirl `𝒯` that commutes with every `U^{⊗1}` and matches traces against
`permSpan` is `(Tr O / d) • 1`. Schur–Weyl (`isHaarTwirl_permSpan`) places it in `permSpan`,
`permSpan_one` identifies that with the scalars, and the `1×1` solve finishes. -/
theorem firstMoment [Nontrivial (⨂[ℂ]^1 W)]
    [Module.Finite ℂ (⨂[ℂ]^1 W)] [Module.Free ℂ (⨂[ℂ]^1 W)]
    (𝒯 : Module.End ℂ (⨂[ℂ]^1 W) →ₗ[ℂ] Module.End ℂ (⨂[ℂ]^1 W))
    (hmem : ∀ O, ∀ U : W ≃ₗᵢ[ℂ] W,
      𝒯 O * glPow U.toLinearEquiv.toLinearMap = glPow U.toLinearEquiv.toLinearMap * 𝒯 O)
    (htrace : ∀ B ∈ permSpan (V := W) (k := 1), ∀ O,
      LinearMap.trace ℂ (⨂[ℂ]^1 W) (B * 𝒯 O) = LinearMap.trace ℂ (⨂[ℂ]^1 W) (B * O))
    (O : Module.End ℂ (⨂[ℂ]^1 W)) :
    𝒯 O = (LinearMap.trace ℂ (⨂[ℂ]^1 W) O / (finrank ℂ (⨂[ℂ]^1 W) : ℂ)) • 1 := by
  have hT := isHaarTwirl_permSpan 𝒯 hmem htrace
  rw [permSpan_one] at hT
  have hAA : LinearMap.trace ℂ (⨂[ℂ]^1 W) ((1 : Module.End ℂ (⨂[ℂ]^1 W)) * 1) ≠ 0 := by
    rw [one_mul, trace_one_End]; exact_mod_cast Module.finrank_pos.ne'
  rw [eq_smul_singleton hT hAA O]
  simp only [one_mul, trace_one_End]

/-- **Second moment.** A twirl `𝒯` that commutes with every `U^{⊗2}` and matches traces against
`permSpan` is `c_I • 1 + c_F • F` (Corollary 13), with `F` the swap. Schur–Weyl places it in
`permSpan`, `permSpan_two` identifies that with `span{1, F}`, and the `2×2` solve finishes. The two
trace constants `Tr 1 = d²` and `Tr F = d` are supplied as hypotheses. -/
theorem secondMoment [Module.Finite ℂ (⨂[ℂ]^2 W)] [Module.Free ℂ (⨂[ℂ]^2 W)] {d : ℕ}
    (hd0 : (d : ℂ) ≠ 0) (hd1 : (d : ℂ) ^ 2 - 1 ≠ 0)
    (htr1 : LinearMap.trace ℂ (⨂[ℂ]^2 W) 1 = (d : ℂ) ^ 2)
    (htrF : LinearMap.trace ℂ (⨂[ℂ]^2 W) (permRep (Equiv.swap (0 : Fin 2) 1)) = (d : ℂ))
    (𝒯 : Module.End ℂ (⨂[ℂ]^2 W) →ₗ[ℂ] Module.End ℂ (⨂[ℂ]^2 W))
    (hmem : ∀ O, ∀ U : W ≃ₗᵢ[ℂ] W,
      𝒯 O * glPow U.toLinearEquiv.toLinearMap = glPow U.toLinearEquiv.toLinearMap * 𝒯 O)
    (htrace : ∀ B ∈ permSpan (V := W) (k := 2), ∀ O,
      LinearMap.trace ℂ (⨂[ℂ]^2 W) (B * 𝒯 O) = LinearMap.trace ℂ (⨂[ℂ]^2 W) (B * O))
    (O : Module.End ℂ (⨂[ℂ]^2 W)) :
    𝒯 O =
      ((LinearMap.trace ℂ (⨂[ℂ]^2 W) O
          - (d : ℂ)⁻¹ * LinearMap.trace ℂ (⨂[ℂ]^2 W) (permRep (Equiv.swap (0 : Fin 2) 1) * O))
        / ((d : ℂ) ^ 2 - 1)) • 1
    + ((LinearMap.trace ℂ (⨂[ℂ]^2 W) (permRep (Equiv.swap (0 : Fin 2) 1) * O)
          - (d : ℂ)⁻¹ * LinearMap.trace ℂ (⨂[ℂ]^2 W) O)
        / ((d : ℂ) ^ 2 - 1)) • permRep (Equiv.swap (0 : Fin 2) 1) := by
  have hT := isHaarTwirl_permSpan 𝒯 hmem htrace
  rw [permSpan_two] at hT
  set F : Module.End ℂ (⨂[ℂ]^2 W) := permRep (Equiv.swap (0 : Fin 2) 1) with hF
  have hF2 : F * F = 1 := by
    rw [hF, ← map_mul, show Equiv.swap (0 : Fin 2) 1 * Equiv.swap (0 : Fin 2) 1 = 1 from by decide,
      map_one]
  have hden : (d : ℂ) ^ 2 * (d : ℂ) ^ 2 - (d : ℂ) * (d : ℂ) ≠ 0 := by
    have : (d : ℂ) ^ 2 * (d : ℂ) ^ 2 - (d : ℂ) * (d : ℂ) = (d : ℂ) ^ 2 * ((d : ℂ) ^ 2 - 1) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero 2 hd0) hd1
  have hdet : LinearMap.trace ℂ (⨂[ℂ]^2 W) ((1 : Module.End ℂ (⨂[ℂ]^2 W)) * 1)
        * LinearMap.trace ℂ (⨂[ℂ]^2 W) (F * F)
      - LinearMap.trace ℂ (⨂[ℂ]^2 W) ((1 : Module.End ℂ (⨂[ℂ]^2 W)) * F)
        * LinearMap.trace ℂ (⨂[ℂ]^2 W) (F * 1) ≠ 0 := by
    simp only [one_mul, mul_one, hF2, htr1, htrF]; exact hden
  rw [eq_of_pair hT hdet O]
  simp only [one_mul, mul_one, hF2, htr1, htrF]
  congr 1
  · congr 1; field_simp; try ring
  · congr 1; field_simp; try ring

end Moments

end LeanHaar.Examples.UnitaryMoments
