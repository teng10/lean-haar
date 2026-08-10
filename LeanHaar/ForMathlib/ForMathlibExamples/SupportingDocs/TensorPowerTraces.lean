/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.ForMathlib.ForMathlibExamples.k1Moment
import LeanHaar.ForMathlib.ForMathlibExamples.k2Moment

/-!
# Tensor products of matrices, tensor powers of operators, and their traces

Both examples built on the Haar moment operator — the quantum machine learning example and the
classical-shadow protocol — need the same elementary linear algebra on the tensor power
`(ℂ^d)^{⊗k}`: the operator `f 0 ⊗ ⋯ ⊗ f (k-1)`, its matrix entries, how such operators
multiply, how the conjugation action `SchurWeyl.actOn` acts on them, and the two trace formulas

* `Tr(A₀ ⊗ ⋯ ⊗ A_{k-1}) = Tr A₀ ⋯ Tr A_{k-1}`, hence `Tr(g^{⊗k}) = (Tr g)^k`,
* the swap identity `Tr(𝔽 (A ⊗ B)) = Tr(A B)`, hence `Tr(𝔽 g^{⊗2}) = Tr(g ∘ g)`.

They are proved here once, for matrices, and transferred to endomorphisms through the matrix
`matrixOf g` of `g` in the computational basis.

## Main definitions

* `SchurWeyl.tensorOp`, `SchurWeyl.tensorPow`: tensor products and tensor powers of matrices.
* `SchurWeyl.matrixOf`: the matrix of `g : End(ℂ^d)` in the computational basis.
* `SchurWeyl.conjBy`: the unitary conjugate `U M U†` of a matrix.

## Main results

* `SchurWeyl.trace_tensorOp`, `SchurWeyl.trace_tensorOp_two`,
  `SchurWeyl.trace_swap_comp_tensorOp`: the traces of tensor products of matrices.
* `SchurWeyl.trace_diagAction`, `SchurWeyl.trace_swap_comp_diagAction`: the same traces for the
  tensor powers `g^{⊗k}` of an endomorphism.
* `SchurWeyl.actOn_tensorOp`: conjugating a tensor product conjugates each factor.
* `SchurWeyl.trace_comp_eq_sum_toEndMatrix`, `SchurWeyl.trace_comp_eq_sum`: the trace of a
  composition, in matrix entries, on `(ℂ^d)^{⊗k}` and on `ℂ^d`.
* `SchurWeyl.trace_comp_mul_matrixOf`: the Born-weighted operator `Tr(ρ S) · S` is, entrywise,
  the contraction of `S^{⊗2}` against `ρ` in the first tensor factor.
-/

noncomputable section

open Matrix

namespace SchurWeyl

variable {d k : ℕ}

/-! ### Tensor products of matrices -/

/-- The operator `f 0 ⊗ f 1 ⊗ ⋯ ⊗ f (k-1)` on the `k`-fold tensor power of `ℂ^d`. -/
def tensorOp (f : Fin k → Matrix (Fin d) (Fin d) ℂ) : Module.End ℂ (TensV d k) :=
  PiTensorProduct.map (fun m => endOf (f m))

/-- The `k`-fold tensor power `M^{⊗k}` of a single matrix. -/
def tensorPow (d k : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) : Module.End ℂ (TensV d k) :=
  tensorOp (fun _ : Fin k => M)

/-- The unitary conjugate `U M U†` of a matrix. -/
def conjBy (U : Matrix.unitaryGroup (Fin d) ℂ) (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * M * star (U : Matrix (Fin d) (Fin d) ℂ)

/-- The matrix entries of `f 0 ⊗ ⋯ ⊗ f (k-1)` are products of matrix entries. -/
theorem toEndMatrix_tensorOp (f : Fin k → Matrix (Fin d) (Fin d) ℂ) (I J : Fin k → Fin d) :
    toEndMatrix d k (tensorOp f) I J = ∏ m : Fin k, f m (I m) (J m) := by
  unfold toEndMatrix tensorOp
  rw [LinearMap.toMatrix_apply]
  unfold tensorBasis
  simp [PiTensorProduct.map_tprod, Basis.piTensorProduct_apply, endOf, Matrix.toLin'_apply]

/-- `Tr(A₀ ⊗ ⋯ ⊗ A_{k-1}) = Tr A₀ ⋯ Tr A_{k-1}`. -/
theorem trace_tensorOp (f : Fin k → Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.trace ℂ (TensV d k) (tensorOp f) = ∏ m : Fin k, (f m).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d k)]
  have h : Matrix.trace (LinearMap.toMatrix (tensorBasis d k) (tensorBasis d k) (tensorOp f))
      = ∑ I : Fin k → Fin d, ∏ m : Fin k, f m (I m) (I m) := by
    simp [Matrix.trace, Matrix.diag, ← toEndMatrix_tensorOp]
    rfl
  rw [h]
  simp only [Matrix.trace, Matrix.diag_apply, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- Tensor products of matrices multiply factorwise. -/
theorem tensorOp_comp (f g : Fin k → Matrix (Fin d) (Fin d) ℂ) :
    tensorOp f ∘ₗ tensorOp g = tensorOp (fun m => f m * g m) := by
  unfold tensorOp
  rw [← PiTensorProduct.map_comp]
  exact congrArg _ (funext fun m => (endOf_mul (f m) (g m)).symm)

/-- The diagonal action of a matrix is its tensor power. -/
theorem diagAction_eq_tensorPow (M : Matrix (Fin d) (Fin d) ℂ) :
    diagAction d k (endOf M) = tensorPow d k M := rfl

/-- Conjugating a tensor product of matrices by `U^{⊗k}` conjugates each factor. -/
theorem actOn_tensorOp (f : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    actOn (tensorOp f) U =
      tensorOp (fun m => (U : Matrix (Fin d) (Fin d) ℂ) * f m *
        star (U : Matrix (Fin d) (Fin d) ℂ)) := by
  unfold actOn
  rw [diagAction_eq_tensorPow, diagAction_eq_tensorPow, tensorPow, tensorPow,
    ← LinearMap.comp_assoc, tensorOp_comp, tensorOp_comp]

/-! ### The swap operator -/

/-- Matrix entries of the swap operator `𝔽 d` on `TensV d 2`. -/
theorem toEndMatrix_swap (I J : Fin 2 → Fin d) :
    toEndMatrix d 2 (𝔽 d) I J = if I = J ∘ (Equiv.swap 0 1) then 1 else 0 := by
  have h : toEndMatrix d 2 (𝔽 d) I J
      = toEndMatrix d 2 ((permAction d (Equiv.swap (0 : Fin 2) 1)).toLinearMap) I J := rfl
  rw [h, toEndMatrix_permAction]
  simp

/-- **Swap trick**: `Tr(𝔽 (A ⊗ B)) = Tr(A B)`. -/
theorem trace_swap_comp_tensorOp (f : Fin 2 → Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ tensorOp f) = (f 0 * f 1).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d 2)]
  have hcomp : LinearMap.toMatrix (tensorBasis d 2) (tensorBasis d 2) (𝔽 d ∘ₗ tensorOp f)
      = toEndMatrix d 2 (𝔽 d) * toEndMatrix d 2 (tensorOp f) := toEndMatrix_comp _ _
  rw [hcomp]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  have hinner : ∀ I : Fin 2 → Fin d,
      (∑ J : Fin 2 → Fin d, toEndMatrix d 2 (𝔽 d) I J * toEndMatrix d 2 (tensorOp f) J I)
        = f 0 (I 1) (I 0) * f 1 (I 0) (I 1) := by
    intro I
    rw [Finset.sum_eq_single (I ∘ Equiv.swap 0 1)]
    · have hI : I = (I ∘ Equiv.swap 0 1) ∘ Equiv.swap 0 1 := by funext x; simp
      rw [toEndMatrix_swap, toEndMatrix_tensorOp, if_pos hI]
      simp [Fin.prod_univ_two]
    · intro J _ hJ
      rw [toEndMatrix_swap, if_neg, zero_mul]
      intro h
      apply hJ
      funext x
      have hx := congrFun h (Equiv.swap 0 1 x)
      simpa using hx.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun I _ => hinner I]
  have h := Fintype.sum_equiv (finTwoArrowEquiv (Fin d))
    (fun I : Fin 2 → Fin d => f 0 (I 1) (I 0) * f 1 (I 0) (I 1))
    (fun p : Fin d × Fin d => f 0 p.2 p.1 * f 1 p.1 p.2) (fun I => rfl)
  rw [h, Fintype.sum_prod_type, Finset.sum_comm]

/-- `Tr(A ⊗ B) = Tr A · Tr B`. -/
theorem trace_tensorOp_two (f : Fin 2 → Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.trace ℂ (TensV d 2) (tensorOp f) = (f 0).trace * (f 1).trace := by
  rw [trace_tensorOp, Fin.prod_univ_two]

/-! ### Tensor powers of an endomorphism of `ℂ^d` -/

/-- The matrix of `g : End(ℂ^d)` in the computational basis. -/
def matrixOf (g : Module.End ℂ (Fin d → ℂ)) : Matrix (Fin d) (Fin d) ℂ :=
  LinearMap.toMatrix (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d)) g

/-- An endomorphism of `ℂ^d` is the endomorphism attached to its matrix. -/
@[simp] theorem endOf_matrixOf (g : Module.End ℂ (Fin d → ℂ)) : endOf (matrixOf g) = g := by
  simp [endOf, matrixOf, Matrix.toLin'_toMatrix']

/-- The matrix of a composition is the product of the matrices. -/
theorem matrixOf_comp (g h : Module.End ℂ (Fin d → ℂ)) :
    matrixOf (g ∘ₗ h) = matrixOf g * matrixOf h :=
  LinearMap.toMatrix_comp _ _ _ g h

/-- The tensor power `g^{⊗k}` of an endomorphism is the tensor power of its matrix. -/
theorem diagAction_eq_tensorPow_matrixOf (g : Module.End ℂ (Fin d → ℂ)) :
    diagAction d k g = tensorPow d k (matrixOf g) := by
  rw [← diagAction_eq_tensorPow, endOf_matrixOf]

/-- The trace is the sum of the diagonal matrix entries. -/
theorem trace_eq_sum_diag (g : Module.End ℂ (Fin d → ℂ)) :
    LinearMap.trace ℂ (Fin d → ℂ) g = ∑ i, matrixOf g i i :=
  LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin d)) g

/-- The trace of an endomorphism is the trace of its matrix. -/
theorem trace_matrixOf (g : Module.End ℂ (Fin d → ℂ)) :
    (matrixOf g).trace = LinearMap.trace ℂ (Fin d → ℂ) g :=
  (trace_eq_sum_diag g).symm

/-- The trace of a tensor power is the power of the trace: `Tr(g^{⊗k}) = Tr(g)^k`. -/
theorem trace_diagAction (g : Module.End ℂ (Fin d → ℂ)) :
    LinearMap.trace ℂ (TensV d k) (diagAction d k g)
      = LinearMap.trace ℂ (Fin d → ℂ) g ^ k := by
  rw [diagAction_eq_tensorPow_matrixOf, tensorPow, trace_tensorOp, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, trace_matrixOf]

/-- Contracting a twofold tensor power with the swap operator squares the operator:
`Tr(𝔽 g^{⊗2}) = Tr(g ∘ g)`. -/
theorem trace_swap_comp_diagAction (g : Module.End ℂ (Fin d → ℂ)) :
    LinearMap.trace ℂ (TensV d 2) (𝔽 d ∘ₗ diagAction d 2 g)
      = LinearMap.trace ℂ (Fin d → ℂ) (g ∘ₗ g) := by
  rw [diagAction_eq_tensorPow_matrixOf, tensorPow, trace_swap_comp_tensorOp,
    ← matrixOf_comp, trace_matrixOf]

/-! ### Traces of compositions, in matrix entries -/

/-- The trace of a composition on `(ℂ^d)^{⊗k}`, expanded in the tensor basis. -/
theorem trace_comp_eq_sum_toEndMatrix (Y X : Module.End ℂ (TensV d k)) :
    LinearMap.trace ℂ (TensV d k) (Y ∘ₗ X)
      = ∑ I : Fin k → Fin d, ∑ J : Fin k → Fin d,
          toEndMatrix d k Y I J * toEndMatrix d k X J I := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d k)]
  have hcomp : LinearMap.toMatrix (tensorBasis d k) (tensorBasis d k) (Y ∘ₗ X)
      = toEndMatrix d k Y * toEndMatrix d k X := toEndMatrix_comp _ _
  rw [hcomp]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-- The trace of a product on `ℂ^d`, in matrix entries: `Tr(ρ S) = ∑_{a,c} ρ_{ac} S_{ca}`. -/
theorem trace_comp_eq_sum (ρ S : Module.End ℂ (Fin d → ℂ)) :
    LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ S)
      = ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 * matrixOf S p.2 p.1 := by
  rw [trace_eq_sum_diag, matrixOf_comp]
  simp [Matrix.mul_apply, Fintype.sum_prod_type]

/-- The Born-weighted snapshot `Tr(ρ S) · S` is the contraction of `S^{⊗2}` against `ρ` in the
first tensor factor; this is the pointwise form of the partial-trace step of Observation 58. -/
theorem trace_comp_mul_matrixOf (ρ S : Module.End ℂ (Fin d → ℂ)) (i j : Fin d) :
    LinearMap.trace ℂ (Fin d → ℂ) (ρ ∘ₗ S) * matrixOf S i j =
      ∑ p : Fin d × Fin d, matrixOf ρ p.1 p.2 *
        toEndMatrix d 2 (diagAction d 2 S) ![p.2, i] ![p.1, j] := by
  rw [trace_comp_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [toEndMatrix_diagAction]
  simp [Fin.prod_univ_two, matrixOf, mul_assoc]

end SchurWeyl

end
