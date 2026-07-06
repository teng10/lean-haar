import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace
import Aesop

import LeanHaar.ForMathlib.TensorV2
import LeanHaar.ForMathlib.Commutation
import LeanHaar.ForMathlib.MatrixRepresentation

/-!
# Weingarten calculus: computing moments

This file formalizes the linear-algebra core of the Weingarten "moment" theorem
(Theorem 10 in the accompanying blueprint).

For an operator `O ∈ End((ℂ^d)^{⊗k})`, the Haar moment operator
`𝔼_{U∼μ_H}[U^{⊗k} O U^{†⊗k}]` is, by Schur–Weyl duality, a linear combination of
the permutation operators `V_d(π)`:
```
  𝔼[U^{⊗k} O U^{†⊗k}] = ∑_{π ∈ S_k} c_π(O) · V_d(π),
```
and the coefficients `c_π(O)` are determined by the linear system of `k!` equations
```
  Tr(V_d^†(σ) O) = ∑_{π ∈ S_k} c_π(O) · Tr(V_d^†(σ) V_d(π))   for all σ ∈ S_k.
```

This file proves the self-contained mathematical heart of the statement, namely that
**this linear system always has at least one solution**, and that the corresponding
operator `M = ∑_π c_π V_d(π)` lies in the span of the permutation operators and has the
same `Tr(V_d^†(σ) · )` values as `O` for every `σ`.

The construction is the Hilbert–Schmidt orthogonal projection of `O` onto the span of
the permutation operators: writing operators as vectors of their matrix entries in the
computational (tensor) basis, the Hilbert–Schmidt inner product `⟪A, B⟫ = Tr(A^† B)`
becomes the standard inner product on `EuclideanSpace`, and the solution `c` is the
coefficient vector of the orthogonal projection.

## Main results

* `SchurWeyl.gram_system_solvable` — abstract Gram-system solvability in any finite
  dimensional inner product space (orthogonal projection onto a finite-dimensional span).
* `SchurWeyl.permDual_eq_conjTranspose` — `V_d^†(σ)` is the conjugate transpose of
  `V_d(σ)` in the computational basis (so it is the genuine Hermitian adjoint).
* `SchurWeyl.weingarten_linear_system_solvable` — the linear system always has a
  solution (the literal final claim of Theorem 10).
* `SchurWeyl.weingarten_moment_operator_spec` — there is a combination
  `M = ∑_π c_π V_d(π)` of permutation operators with `Tr(V_d^†(σ) M) = Tr(V_d^†(σ) O)`
  for all `σ`, exhibiting the moment-operator decomposition.

## References

* [J. Watrous, *The Theory of Quantum Information*][watrous2018]
-/

noncomputable section

open scoped TensorProduct InnerProductSpace Matrix

namespace ForMathlib.Tensor

variable {d k : ℕ}

/-! ### Abstract Gram-system solvability -/

/-- **Gram-system solvability.** In a finite-dimensional inner product space, for any
finite family of vectors `v` and any target vector `w`, the linear system
`⟪v j, w⟫ = ∑ i, c i • ⟪v j, v i⟫` always has a solution `c`: take `c` to be the
coefficients of the orthogonal projection of `w` onto `span (range v)`. -/
theorem gram_system_solvable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] (v : ι → H) (w : H) :
    ∃ c : ι → ℂ, ∀ j, ⟪v j, w⟫_ℂ = ∑ i, c i * ⟪v j, v i⟫_ℂ := by
  classical
  set S : Submodule ℂ H := Submodule.span ℂ (Set.range v) with hS
  have hfin : FiniteDimensional ℂ S := by
    rw [hS]; exact FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  obtain ⟨y, hyS, z, hzperp, hwyz⟩ := S.exists_add_mem_mem_orthogonal w
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hyS
  refine ⟨c, fun j => ?_⟩
  have hvj : v j ∈ S := Submodule.subset_span ⟨j, rfl⟩
  have hzero : ⟪v j, z⟫_ℂ = 0 := by
    rw [inner_eq_zero_symm]; exact (S.mem_orthogonal' z).1 hzperp _ hvj
  calc ⟪v j, w⟫_ℂ = ⟪v j, y⟫_ℂ + ⟪v j, z⟫_ℂ := by rw [hwyz, inner_add_right]
    _ = ⟪v j, y⟫_ℂ := by rw [hzero, add_zero]
    _ = ∑ i, c i * ⟪v j, v i⟫_ℂ := by rw [← hc, inner_sum]; simp_rw [inner_smul_right]

/-! ### Permutation operators and their Hermitian adjoints -/

/-- The permutation operator `V_d(σ)` as a linear endomorphism of `V^{⊗k}`. -/
def permOp (d : ℕ) {k : ℕ} (σ : Equiv.Perm (Fin k)) : Module.End ℂ (TensV d k) :=
  (permAction d σ).toLinearMap

/-- The Hermitian adjoint `V_d^†(σ)` of the permutation operator, defined as the inverse
permutation operator `V_d(σ⁻¹)`. The lemma `permDual_eq_conjTranspose` confirms this is the
conjugate transpose of `V_d(σ)` in the computational basis. -/
def permDual (d : ℕ) {k : ℕ} (σ : Equiv.Perm (Fin k)) : Module.End ℂ (TensV d k) :=
  (permAction d σ⁻¹).toLinearMap

/-- `V_d^†(σ)` is the conjugate transpose of `V_d(σ)` in the computational basis, i.e. it
is the genuine Hermitian adjoint of the permutation operator. -/
theorem permDual_eq_conjTranspose (σ : Equiv.Perm (Fin k)) :
    toEndMatrix d k (permDual d σ) = (toEndMatrix d k (permOp d σ))ᴴ := by
  ext I J
  rw [permOp, permDual, Matrix.conjTranspose_apply, toEndMatrix_permAction,
    toEndMatrix_permAction]
  have e1 : ((σ⁻¹ : Equiv.Perm (Fin k)).symm) = σ := by simp [Equiv.Perm.inv_def]
  rw [e1]
  have hiff : (J = I ∘ σ.symm) ↔ (I = J ∘ σ) := by
    constructor
    · intro h; funext x; rw [h]; simp [Function.comp]
    · intro h; funext x; rw [h]; simp [Function.comp]
  by_cases h : I = J ∘ σ
  · rw [if_pos h, if_pos (hiff.mpr h)]; simp
  · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]; simp

/-! ### Hilbert–Schmidt vectorization and the trace bridge -/

/-- The Hilbert–Schmidt "vectorization" of an operator: the vector of its matrix entries
in the computational basis, viewed as an element of a Euclidean space. The standard inner
product of two such vectors is the Hilbert–Schmidt inner product `Tr(A^† B)`. -/
def endVec (O : Module.End ℂ (TensV d k)) :
    EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d)) :=
  WithLp.toLp 2 (fun p => toEndMatrix d k O p.1 p.2)

/-- The trace bridge: the Euclidean inner product of the vectorizations of `V_d(σ)` and `O`
equals the Hilbert–Schmidt inner product `Tr(V_d^†(σ) O)`. -/
theorem inner_endVec_perm_eq_trace (σ : Equiv.Perm (Fin k)) (O : Module.End ℂ (TensV d k)) :
    ⟪endVec (permOp d σ), endVec O⟫_ℂ =
      LinearMap.trace ℂ (TensV d k) ((permDual d σ) ∘ₗ O) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, endVec]
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d k)]
  rw [show ((permDual d σ) ∘ₗ O) = (permDual d σ).comp O from rfl]
  rw [LinearMap.toMatrix_comp (tensorBasis d k) (tensorBasis d k) (tensorBasis d k)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  have key : ∀ I J : Fin k → Fin d,
      (starRingEnd ℂ) (toEndMatrix d k (permOp d σ) I J) = toEndMatrix d k (permDual d σ) J I := by
    intro I J
    rw [permOp, permDual, toEndMatrix_permAction, toEndMatrix_permAction]
    have e1 : ((σ⁻¹ : Equiv.Perm (Fin k)).symm) = σ := by simp [Equiv.Perm.inv_def]
    rw [e1]
    have hiff : (I = J ∘ σ.symm) ↔ (J = I ∘ σ) := by
      constructor
      · intro h; funext x; rw [h]; simp [Function.comp]
      · intro h; funext x; rw [h]; simp [Function.comp]
    by_cases h : I = J ∘ σ.symm
    · rw [if_pos h, if_pos (hiff.mp h)]; simp
    · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]; simp
  simp_rw [key]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => mul_comm _ _))

/-! ### The Weingarten moment system -/

/-- **Computing moments (Theorem 10), linear-system part.** For any operator
`O ∈ End((ℂ^d)^{⊗k})`, the linear system of `k!` equations
```
  Tr(V_d^†(σ) O) = ∑_{π ∈ S_k} c_π · Tr(V_d^†(σ) V_d(π))   for all σ ∈ S_k
```
always has at least one solution `c`. -/
theorem weingarten_linear_system_solvable (O : Module.End ℂ (TensV d k)) :
    ∃ c : Equiv.Perm (Fin k) → ℂ, ∀ σ : Equiv.Perm (Fin k),
      LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ O) =
        ∑ π : Equiv.Perm (Fin k),
          c π * LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ permOp d π) := by
  obtain ⟨c, hc⟩ := gram_system_solvable
    (fun σ : Equiv.Perm (Fin k) => endVec (permOp d σ)) (endVec O)
  refine ⟨c, fun σ => ?_⟩
  have h := hc σ
  rw [inner_endVec_perm_eq_trace] at h
  simp_rw [inner_endVec_perm_eq_trace] at h
  exact h

/-- Trace against `V_d^†(σ)` of a linear combination of permutation operators expands
linearly over the combination. -/
theorem trace_permDual_comp_sum (σ : Equiv.Perm (Fin k)) (c : Equiv.Perm (Fin k) → ℂ) :
    LinearMap.trace ℂ (TensV d k)
        (permDual d σ ∘ₗ (∑ π : Equiv.Perm (Fin k), c π • permOp d π)) =
      ∑ π : Equiv.Perm (Fin k), c π * LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ permOp d π) := by
  set T : Module.End ℂ (TensV d k) →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ (TensV d k)).comp
      (LinearMap.llcomp ℂ (TensV d k) (TensV d k) (TensV d k) (permDual d σ))
  have hT : ∀ g, T g = LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ g) := fun g => rfl
  rw [← hT, map_sum]
  simp_rw [map_smul, smul_eq_mul, hT]

/-- `M = ∑_π c_π V_d(π)` is a linear combination of permutation operators, so it lies in
the span of the permutation operators. -/
theorem sum_smul_permOp_mem_span (c : Equiv.Perm (Fin k) → ℂ) :
    (∑ π : Equiv.Perm (Fin k), c π • permOp d π) ∈ Submodule.span ℂ (permImage d k) := by
  refine Submodule.sum_mem _ (fun π _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨π, rfl⟩

/-- **Computing moments (Theorem 10), operator part.** There is a linear combination
`M = ∑_{π ∈ S_k} c_π · V_d(π)` of the permutation operators (an element of their span)
whose Hilbert–Schmidt projections agree with those of `O`:
`Tr(V_d^†(σ) M) = Tr(V_d^†(σ) O)` for every `σ ∈ S_k`.

This is the moment-operator decomposition: the coefficients `c_π` solve the Weingarten
linear system, and `M` is exactly the operator characterized by the trace conditions. (In
the full Haar statement, `M` is the moment operator `𝔼_{U∼μ_H}[U^{⊗k} O U^{†⊗k}]`.) -/
theorem weingarten_moment_operator_spec (O : Module.End ℂ (TensV d k)) :
    ∃ c : Equiv.Perm (Fin k) → ℂ,
      (∑ π : Equiv.Perm (Fin k), c π • permOp d π) ∈ Submodule.span ℂ (permImage d k) ∧
      ∀ σ : Equiv.Perm (Fin k),
        LinearMap.trace ℂ (TensV d k)
            (permDual d σ ∘ₗ (∑ π : Equiv.Perm (Fin k), c π • permOp d π)) =
          LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ O) := by
  obtain ⟨c, hc⟩ := weingarten_linear_system_solvable O
  refine ⟨c, sum_smul_permOp_mem_span c, fun σ => ?_⟩
  rw [trace_permDual_comp_sum, ← hc σ]

/-! ### Connection to the Haar moment operator

The actual moment operator `M = 𝔼_{U∼μ_H}[U^{⊗k} O U^{†⊗k}]` (a Bochner integral over the
Haar probability measure on the unitary group `U(d)`) is not constructed here, as Mathlib
currently lacks the compactness/measurability instances and Haar measure on
`Matrix.unitaryGroup`. However, two properties of that integral are exactly what is needed
to deduce Theorem 10, and the theorem below proves the full conclusion from them:

* **(P1)** `M ∈ span (permImage d k)`. For the Haar integral this is Schur–Weyl duality:
  by left/right invariance of the Haar measure, `W^{⊗k} M W^{†⊗k} = M` for every unitary
  `W`, so `M` commutes with all `g^{⊗k}` (every operator is a `ℂ`-combination of unitaries),
  i.e. `M` lies in the centralizer of the diagonal action, which equals `span (permImage)`
  by `SchurWeyl.schur_weyl`.
* **(P2)** `Tr(V_d^†(σ) M) = Tr(V_d^†(σ) O)` for all `σ`. For the Haar integral the
  integrand `Tr(V_d^†(σ) U^{⊗k} O U^{†⊗k}) = Tr(U^{†⊗k} V_d^†(σ) U^{⊗k} O) = Tr(V_d^†(σ) O)`
  is constant in `U` (since `V_d(σ)` commutes with `U^{⊗k}`), and the Haar measure is a
  probability measure.
-/

/-- **Computing moments (Theorem 10), full statement from the Haar properties.** If an
operator `M` lies in the span of the permutation operators (property P1, supplied by
Schur–Weyl duality applied to the Haar moment operator) and has the same `Tr(V_d^†(σ) · )`
values as `O` for every `σ` (property P2, the constant-integrand identity), then `M` is a
linear combination of the permutation operators, `M = ∑_{π ∈ S_k} c_π · V_d(π)`, whose
coefficients `c_π` solve the Weingarten linear system
`Tr(V_d^†(σ) O) = ∑_π c_π · Tr(V_d^†(σ) V_d(π))` for all `σ ∈ S_k`.

Taking `M = 𝔼_{U∼μ_H}[U^{⊗k} O U^{†⊗k}]` gives precisely Theorem 10. -/
theorem weingarten_moment_decomposition_of_props (O M : Module.End ℂ (TensV d k))
    (hMspan : M ∈ Submodule.span ℂ (permImage d k))
    (hMtrace : ∀ σ : Equiv.Perm (Fin k),
      LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ M) =
        LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ O)) :
    ∃ c : Equiv.Perm (Fin k) → ℂ,
      M = ∑ π : Equiv.Perm (Fin k), c π • permOp d π ∧
      ∀ σ : Equiv.Perm (Fin k),
        LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ O) =
          ∑ π : Equiv.Perm (Fin k),
            c π * LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ permOp d π) := by
  have hperm : permImage d k = Set.range (fun π : Equiv.Perm (Fin k) => permOp d π) := rfl
  rw [hperm] at hMspan
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hMspan
  refine ⟨c, hc.symm, fun σ => ?_⟩
  rw [← hMtrace σ, ← hc, trace_permDual_comp_sum]

end ForMathlib.Tensor

end
