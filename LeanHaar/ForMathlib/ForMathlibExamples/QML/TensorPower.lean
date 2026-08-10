import LeanHaar.ForMathlib.ForMathlibExamples.k1Moment
import LeanHaar.ForMathlib.ForMathlibExamples.k2Moment

/-!
# Tensor powers of matrices and their traces

This file provides the elementary linear algebra used by the quantum machine learning example:
the operator `f 0 ⊗ ⋯ ⊗ f (k-1)` on the `k`-fold tensor power of `ℂ^d`, its matrix entries, how
such operators multiply, how the conjugation action `SchurWeyl.actOn` acts on them, and the two
trace formulas

* `Tr(A₀ ⊗ ⋯ ⊗ A_{k-1}) = Tr A₀ ⋯ Tr A_{k-1}`,
* the swap identity `Tr(𝔽 (A ⊗ B)) = Tr(A B)`.

## Main declarations

* `QML.tensorOp`, `QML.tensorPow`: tensor products and tensor powers of matrices.
* `QML.trace_tensorOp`, `QML.trace_tensorOp_two`, `QML.trace_swap_comp_tensorOp`: their traces.
* `QML.actOn_tensorOp`: conjugating a tensor product conjugates each factor.
* `QML.conjBy`: the unitary conjugate `U M U†` of a matrix.
-/

noncomputable section

open Matrix SchurWeyl

namespace QML

variable {d k : ℕ}

/-- The operator `f 0 ⊗ f 1 ⊗ ⋯ ⊗ f (k-1)` on the `k`-fold tensor power of `ℂ^d`. -/
def tensorOp (f : Fin k → Matrix (Fin d) (Fin d) ℂ) : Module.End ℂ (TensV d k) :=
  PiTensorProduct.map (fun m => endOf (f m))

/-- The `k`-fold tensor power `M^{⊗k}` of a single matrix. -/
def tensorPow (d k : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) : Module.End ℂ (TensV d k) :=
  tensorOp (fun _ : Fin k => M)

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

/-- The unitary conjugate `U M U†` of a matrix. -/
def conjBy (U : Matrix.unitaryGroup (Fin d) ℂ) (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * M * star (U : Matrix (Fin d) (Fin d) ℂ)

end QML

end
