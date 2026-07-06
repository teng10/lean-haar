/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Aesop

import LeanHaar.ForMathlib.Weingarten
import LeanHaar.ForMathlib.MatrixRepresentation

/-!
# Weingarten calculus: the unique solution for `k ≤ d`

This file complements `Weingarten.lean`. There we proved that the Weingarten linear
system
```
  Tr(V_d^†(σ) O) = ∑_{π ∈ S_k} c_π · Tr(V_d^†(σ) V_d(π))   for all σ ∈ S_k
```
always has *at least one* solution (the Hilbert–Schmidt projection). Here we prove that
when `k ≤ d` the solution is **unique**, and we give it explicitly via the *inverse of the
Gram matrix*.

## Abstract core

For a finite family of vectors `v : ι → H` in a finite-dimensional inner product space, the
*Gram matrix* is `gramMatrix v σ π = ⟪v σ, v π⟫` and the *target vector* is
`gramVec v w j = ⟪v j, w⟫`. A vector `c : ι → ℂ` solves the Gram system iff
`gramMatrix v *ᵥ c = gramVec v w` (`SchurWeyl.isGramSolution_iff_mulVec`). When `v` is
linearly independent the Gram matrix is invertible (`SchurWeyl.gramMatrix_det_ne_zero`), so
the solution is unique and equals `(gramMatrix v)⁻¹ *ᵥ gramVec v w`
(`SchurWeyl.gram_solutionSet_eq_singleton`, `SchurWeyl.gram_system_unique`).

## Concrete Weingarten system (`k ≤ d`)

Specialising to `v σ = endVec (permOp d σ)` we obtain the Weingarten Gram matrix
`weingartenGram d k σ π = Tr(V_d^†(σ) V_d(π))` and target
`weingartenVec d k O σ = Tr(V_d^†(σ) O)`. The permutation operators are linearly
independent precisely when `k ≤ d` (`SchurWeyl.linearIndependent_permOp`), so:

* `SchurWeyl.weingartenGram_det_ne_zero` — the Gram matrix is invertible for `k ≤ d`.
* `SchurWeyl.weingartenSolutionSet` — the abstract set of solutions of the system.
* `SchurWeyl.weingarten_solutionSet_eq_singleton` — for `k ≤ d` the solution set is the
  singleton `{(weingartenGram d k)⁻¹ *ᵥ weingartenVec d k O}`.
* `SchurWeyl.weingarten_solution_unique` — the system has a unique solution for `k ≤ d`.

Because `Equiv.Perm (Fin k)` is a concrete finite type for every concrete `k`, plugging in a
value of `k` produces the explicit `k!`-by-`k!` system automatically.
-/

noncomputable section

open scoped TensorProduct InnerProductSpace Matrix
open Matrix

namespace ForMathlib.Tensor

/-! ### Abstract Gram system: matrix form, invertibility and uniqueness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **Gram matrix** of a finite family of vectors: `gramMatrix v j i = ⟪v j, v i⟫`. -/
def gramMatrix (v : ι → H) : Matrix ι ι ℂ := fun j i => ⟪v j, v i⟫_ℂ

/-- The **target vector** of the Gram system: `gramVec v w j = ⟪v j, w⟫`. -/
def gramVec (v : ι → H) (w : H) : ι → ℂ := fun j => ⟪v j, w⟫_ℂ

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem gramMatrix_apply (v : ι → H) (j i : ι) :
    gramMatrix v j i = ⟪v j, v i⟫_ℂ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem gramVec_apply (v : ι → H) (w : H) (j : ι) :
    gramVec v w j = ⟪v j, w⟫_ℂ := rfl

omit [DecidableEq ι] in
/-- A vector `c` solves the Gram system `∀ j, ⟪v j, w⟫ = ∑ i, c i * ⟪v j, v i⟫`
iff `gramMatrix v *ᵥ c = gramVec v w`. -/
theorem isGramSolution_iff_mulVec (v : ι → H) (w : H) (c : ι → ℂ) :
    (∀ j, ⟪v j, w⟫_ℂ = ∑ i, c i * ⟪v j, v i⟫_ℂ) ↔ gramMatrix v *ᵥ c = gramVec v w := by
  constructor
  · intro hc
    funext j
    rw [gramVec_apply, hc j, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl (fun i _ => by rw [gramMatrix_apply]; ring)
  · intro hc j
    have hj := congrFun hc j
    rw [gramVec_apply, Matrix.mulVec, dotProduct] at hj
    rw [← hj]
    exact Finset.sum_congr rfl (fun i _ => by rw [gramMatrix_apply]; ring)

/-- **The Gram matrix of a linearly independent family is invertible.** -/
theorem gramMatrix_det_ne_zero (v : ι → H) (hv : LinearIndependent ℂ v) :
    (gramMatrix v).det ≠ 0 := by
  intro hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
  obtain ⟨c, hc0, hc⟩ := hdet
  apply hc0
  set u := ∑ i, c i • v i with hu
  have hperp : ∀ j, ⟪v j, u⟫_ℂ = 0 := by
    intro j
    have hj := congrFun hc j
    simp only [Matrix.mulVec, gramMatrix, dotProduct, Pi.zero_apply] at hj
    rw [hu, inner_sum]
    simp_rw [inner_smul_right]
    rw [← hj]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have huu : ⟪u, u⟫_ℂ = 0 := by
    rw [hu, sum_inner]
    exact Finset.sum_eq_zero (fun i _ => by rw [inner_smul_left, hperp i, mul_zero])
  have hu0 : u = 0 := inner_self_eq_zero.mp huu
  funext i
  exact (Fintype.linearIndependent_iff.mp hv c (by rw [← hu]; exact hu0)) i

/-- The Gram matrix is a unit for a linearly independent family. -/
theorem gramMatrix_isUnit_det (v : ι → H) (hv : LinearIndependent ℂ v) :
    IsUnit (gramMatrix v).det :=
  isUnit_iff_ne_zero.mpr (gramMatrix_det_ne_zero v hv)

/-- For a linearly independent family, the Gram system has the unique solution
`(gramMatrix v)⁻¹ *ᵥ gramVec v w`. -/
theorem gram_solution_eq_inv (v : ι → H) (hv : LinearIndependent ℂ v) (w : H)
    (c : ι → ℂ) (hc : ∀ j, ⟪v j, w⟫_ℂ = ∑ i, c i * ⟪v j, v i⟫_ℂ) :
    c = (gramMatrix v)⁻¹ *ᵥ gramVec v w := by
  have hdet : IsUnit (gramMatrix v).det := gramMatrix_isUnit_det v hv
  have hmv : gramMatrix v *ᵥ c = gramVec v w := (isGramSolution_iff_mulVec v w c).mp hc
  rw [← hmv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- **Set of solutions** of the Gram system. -/
def gramSolutionSet (v : ι → H) (w : H) : Set (ι → ℂ) :=
  {c | ∀ j, ⟪v j, w⟫_ℂ = ∑ i, c i * ⟪v j, v i⟫_ℂ}

/-- For a linearly independent family, the solution set of the Gram system is the singleton
`{(gramMatrix v)⁻¹ *ᵥ gramVec v w}`. -/
theorem gram_solutionSet_eq_singleton (v : ι → H) (hv : LinearIndependent ℂ v) (w : H) :
    gramSolutionSet v w = {(gramMatrix v)⁻¹ *ᵥ gramVec v w} := by
  have hdet : IsUnit (gramMatrix v).det := gramMatrix_isUnit_det v hv
  ext c
  simp only [gramSolutionSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · exact fun hc => gram_solution_eq_inv v hv w c hc
  · intro hc
    rw [isGramSolution_iff_mulVec, hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]

/-- **Uniqueness of the Gram-system solution** for a linearly independent family. -/
theorem gram_system_unique (v : ι → H) (hv : LinearIndependent ℂ v) (w : H) :
    ∃! c : ι → ℂ, ∀ j, ⟪v j, w⟫_ℂ = ∑ i, c i * ⟪v j, v i⟫_ℂ := by
  obtain ⟨c, hc⟩ := gram_system_solvable v w
  refine ⟨c, hc, fun c' hc' => ?_⟩
  rw [gram_solution_eq_inv v hv w c' hc', gram_solution_eq_inv v hv w c hc]

end Abstract

/-! ### `endVec` as a linear equivalence -/

section EndVec

variable {d k : ℕ}

/-- Reading off the entries of a matrix as a function on the product index type, as a
linear equivalence. -/
def matrixEntriesEquiv (P Q : Type*) : Matrix P Q ℂ ≃ₗ[ℂ] (P × Q → ℂ) where
  toFun M p := M p.1 p.2
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `endVec` as a `ℂ`-linear **equivalence** from operators to the Euclidean space of matrix
entries. -/
def endVecEquiv (d k : ℕ) :
    Module.End ℂ (TensV d k) ≃ₗ[ℂ]
      EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d)) :=
  (toEndMatrix d k).trans
    ((matrixEntriesEquiv (Fin k → Fin d) (Fin k → Fin d)).trans
      (WithLp.linearEquiv 2 ℂ ((Fin k → Fin d) × (Fin k → Fin d) → ℂ)).symm)

/-- `endVec` as a `ℂ`-linear map from operators to the Euclidean space of matrix entries. -/
def endVecₗ (d k : ℕ) :
    Module.End ℂ (TensV d k) →ₗ[ℂ]
      EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d)) :=
  (endVecEquiv d k).toLinearMap

@[simp] theorem endVecₗ_apply (O : Module.End ℂ (TensV d k)) :
    endVecₗ d k O = endVec O := rfl

theorem endVecₗ_injective : Function.Injective (endVecₗ d k) :=
  (endVecEquiv d k).injective

theorem endVecₗ_ker : LinearMap.ker (endVecₗ d k) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective endVecₗ_injective

end EndVec

/-! ### Linear independence of the permutation operators for `k ≤ d` -/

section LinIndep

variable {d k : ℕ}

/-
For `k ≤ d` the vectorised permutation operators `endVec (V_d(σ))` are linearly
independent in the Euclidean space of matrix entries.

Proof: a vanishing combination `∑ σ, g σ • endVec (V_d(σ)) = 0`, read off at the matrix
coordinate `(I, J)` with `J = Fin.castLE h` (injective) and `I = J ∘ τ⁻¹`, collapses to the
single term `g τ` because `V_d(σ)` has matrix entry `[I = J ∘ σ⁻¹]` and `J` injective forces
`σ = τ`. Hence every `g τ = 0`.
-/
theorem linearIndependent_endVec_permOp (h : k ≤ d) :
    LinearIndependent ℂ (fun σ : Equiv.Perm (Fin k) => endVec (permOp d σ)) := by
  refine' Fintype.linearIndependent_iff.2 _;
  intro g hg i;
  replace hg := congr_arg ( fun x => x ( ( Fin.castLE h ) ∘ i.symm, Fin.castLE h ) ) hg ; simp_all +decide [ Finset.sum_apply, Pi.smul_apply ];
  rw [ Finset.sum_eq_single i ] at hg;
  · simp_all +decide [ endVec ];
    simp_all +decide [ toEndMatrix_permAction, permOp ];
  · intro j _ hj; simp_all +decide [ endVec ] ;
    simp_all +decide [ toEndMatrix_permAction, permOp ];
    exact Or.inr fun h => hj <| Equiv.symm_bijective.injective <| Equiv.ext fun x => by simpa [ Fin.ext_iff ] using congr_fun h.symm x;
  · aesop

/-- For `k ≤ d` the permutation operators `V_d(π)` are linearly independent in
`End(V^{⊗k})`. This follows from the linear independence of their vectorisations
`endVec (V_d(σ))` since `endVec` is injective and linear. -/
theorem linearIndependent_permOp (h : k ≤ d) :
    LinearIndependent ℂ (fun σ : Equiv.Perm (Fin k) => permOp d σ) :=
  LinearIndependent.of_comp (endVecₗ d k)
    (by simpa only [Function.comp_def, endVecₗ_apply] using linearIndependent_endVec_permOp h)

end LinIndep

/-! ### The concrete Weingarten system and its unique solution for `k ≤ d` -/

section Weingarten

variable {d k : ℕ}

/-- The **Weingarten Gram matrix**: `weingartenGram d k σ π = Tr(V_d^†(σ) V_d(π))`. -/
def weingartenGram (d k : ℕ) : Matrix (Equiv.Perm (Fin k)) (Equiv.Perm (Fin k)) ℂ :=
  fun σ π => LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ permOp d π)

/-- The **Weingarten target vector**: `weingartenVec d k O σ = Tr(V_d^†(σ) O)`. -/
def weingartenVec (d k : ℕ) (O : Module.End ℂ (TensV d k)) : Equiv.Perm (Fin k) → ℂ :=
  fun σ => LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ O)

/-- The Weingarten Gram matrix is the Gram matrix of the vectorised permutation operators. -/
theorem weingartenGram_eq_gramMatrix :
    weingartenGram d k = gramMatrix (fun σ : Equiv.Perm (Fin k) => endVec (permOp d σ)) := by
  ext σ π
  rw [weingartenGram, gramMatrix_apply, inner_endVec_perm_eq_trace]

/-- The Weingarten target vector is the Gram target of the vectorised permutation operators. -/
theorem weingartenVec_eq_gramVec (O : Module.End ℂ (TensV d k)) :
    weingartenVec d k O =
      gramVec (fun σ : Equiv.Perm (Fin k) => endVec (permOp d σ)) (endVec O) := by
  funext σ
  rw [weingartenVec, gramVec_apply, inner_endVec_perm_eq_trace]

/-
**Closed form of the Gram-matrix entries.** The entry `Tr(V_d^†(σ) V_d(π))` equals the
number of index functions `J : Fin k → Fin d` satisfying the coincidence condition
`J ∘ σ⁻¹ = J ∘ π⁻¹` (equivalently, `J` is constant on the cycles of `σ⁻¹π`; this count is
`d ^ (number of cycles of σ⁻¹π)`). The right-hand side is decidable and computable, so for
concrete `d` and `k` the entire Weingarten system can be written down automatically.
-/
theorem weingartenGram_eq_card (σ π : Equiv.Perm (Fin k)) :
    weingartenGram d k σ π =
      (Fintype.card {J : Fin k → Fin d // J ∘ σ.symm = J ∘ π.symm} : ℂ) := by
  convert inner_endVec_perm_eq_trace σ ( permOp d π ) |> Eq.symm using 1;
  simp +decide [ inner, endVec ];
  simp +decide [ toEndMatrix_permAction, permOp ];
  simp +decide [ Fintype.card_subtype, Finset.sum_ite ];
  refine' Finset.card_bij ( fun x hx => ( x ∘ σ.symm, x ) ) _ _ _ <;> aesop

/-- A **computable** form of the Weingarten Gram matrix: each entry is the natural-number
coincidence count `#{J : Fin k → Fin d // J ∘ σ⁻¹ = J ∘ π⁻¹}`. For concrete `d` and `k` this
evaluates to explicit integers (see the examples below), so the Weingarten system can be
written down automatically just by plugging in `k` (and `d`). -/
def weingartenGramNat (d k : ℕ) :
    Matrix (Equiv.Perm (Fin k)) (Equiv.Perm (Fin k)) ℕ :=
  fun σ π => Fintype.card {J : Fin k → Fin d // J ∘ σ.symm = J ∘ π.symm}

/-- The complex Weingarten Gram matrix is the natural-number coincidence-count matrix,
cast to `ℂ`. -/
theorem weingartenGram_eq_natCast (σ π : Equiv.Perm (Fin k)) :
    weingartenGram d k σ π = (weingartenGramNat d k σ π : ℂ) :=
  weingartenGram_eq_card σ π

/-- The diagonal entries of the Gram matrix are `d ^ k` (this is `Tr(V_d^†(σ) V_d(σ)) =
Tr(\mathrm{id}) = d^k`). -/
@[simp] theorem weingartenGramNat_diag (σ : Equiv.Perm (Fin k)) :
    weingartenGramNat d k σ σ = d ^ k := by
  rw [weingartenGramNat,
    Fintype.card_congr (Equiv.subtypeUnivEquiv (fun J : Fin k → Fin d => rfl)),
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

-- Examples: plugging in `k = 2` (so `S_2 = {id, swap}`) and `d = 5`, the Gram matrix is
-- `[[25, 5], [5, 25]]`, computed automatically.
example : weingartenGramNat 5 2 (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2)) = 25 := by decide
example : weingartenGramNat 5 2 (Equiv.refl (Fin 2)) (Equiv.swap 0 1) = 5 := by decide
example : weingartenGramNat 5 2 (Equiv.swap 0 1) (Equiv.swap 0 1) = 25 := by decide

/-- **For `k ≤ d` the Weingarten Gram matrix is invertible.** -/
theorem weingartenGram_det_ne_zero (h : k ≤ d) : (weingartenGram d k).det ≠ 0 := by
  rw [weingartenGram_eq_gramMatrix]
  exact gramMatrix_det_ne_zero _ (linearIndependent_endVec_permOp h)

/-- The **set of solutions** of the Weingarten linear system. -/
def weingartenSolutionSet (d k : ℕ) (O : Module.End ℂ (TensV d k)) :
    Set (Equiv.Perm (Fin k) → ℂ) :=
  {c | ∀ σ : Equiv.Perm (Fin k),
      weingartenVec d k O σ = ∑ π : Equiv.Perm (Fin k), c π * weingartenGram d k σ π}

/-- **The Weingarten system has a unique solution for `k ≤ d`, given by the inverse Gram
matrix.** The solution set is the singleton
`{(weingartenGram d k)⁻¹ *ᵥ weingartenVec d k O}`. -/
theorem weingarten_solutionSet_eq_singleton (h : k ≤ d) (O : Module.End ℂ (TensV d k)) :
    weingartenSolutionSet d k O =
      {(weingartenGram d k)⁻¹ *ᵥ weingartenVec d k O} := by
  have hv := linearIndependent_endVec_permOp h
  rw [weingartenSolutionSet]
  simp only [weingartenGram_eq_gramMatrix, weingartenVec_eq_gramVec]
  exact gram_solutionSet_eq_singleton _ hv _

/-- **Uniqueness of the Weingarten coefficients for `k ≤ d`.** -/
theorem weingarten_solution_unique (h : k ≤ d) (O : Module.End ℂ (TensV d k)) :
    ∃! c : Equiv.Perm (Fin k) → ℂ, ∀ σ : Equiv.Perm (Fin k),
      weingartenVec d k O σ = ∑ π : Equiv.Perm (Fin k), c π * weingartenGram d k σ π := by
  have hv := linearIndependent_endVec_permOp h
  simp only [weingartenGram_eq_gramMatrix, weingartenVec_eq_gramVec]
  exact gram_system_unique _ hv _

/-- The unique Weingarten coefficient vector for `k ≤ d` is `(weingartenGram)⁻¹ *ᵥ
weingartenVec`, and it indeed solves the system. -/
theorem weingarten_solution_eq_inv (h : k ≤ d) (O : Module.End ℂ (TensV d k))
    (c : Equiv.Perm (Fin k) → ℂ)
    (hc : ∀ σ : Equiv.Perm (Fin k),
      weingartenVec d k O σ = ∑ π : Equiv.Perm (Fin k), c π * weingartenGram d k σ π) :
    c = (weingartenGram d k)⁻¹ *ᵥ weingartenVec d k O := by
  have hmem : c ∈ weingartenSolutionSet d k O := hc
  rw [weingarten_solutionSet_eq_singleton h O] at hmem
  exact hmem

end Weingarten

end ForMathlib.Tensor

end
