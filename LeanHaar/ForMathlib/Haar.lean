/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Group.Defs
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Aesop

import LeanHaar.ForMathlib.TensorV2
import LeanHaar.ForMathlib.Commutation
import LeanHaar.ForMathlib.DirectProof
import LeanHaar.ForMathlib.Duality
import LeanHaar.ForMathlib.Weingarten
import LeanHaar.ForMathlib.Svd
import LeanHaar.ForMathlib.MatrixRepresentation


/-!
# The Haar layer for Weingarten calculus

This file builds the measure-theoretic foundation behind the Weingarten moment operator
and constructs the genuine Haar moment operator
`𝔼_{U∼μ_H}[U^{⊗k} O U^{†⊗k}]` as a (componentwise) integral over the unitary group.

## Main contents

* **Compactness** of the unitary group `U(d) = Matrix.unitaryGroup (Fin d) ℂ`
  (`ForMathlib.Tensor.isCompact_unitaryGroup`, `ForMathlib.Tensor.instCompactSpaceUnitaryGroup`).
* The **Haar probability measure** `ForMathlib.Tensor.haarProb d` on `U(d)`: the normalized
  (left-invariant, regular) Haar measure, with `IsProbabilityMeasure` and
  `IsMulLeftInvariant` instances.
* `ForMathlib.Tensor.actOn` — the conjugation action `O ↦ U^{⊗k} O U^{†⊗k}`.
* `ForMathlib.Tensor.momentOp` — the Haar moment operator, defined componentwise as the
  Haar average of `actOn O U`.
* `ForMathlib.Tensor.momentOp_trace` — property **(P2)**: the moment operator has the same
  `Tr(V_d^†(σ) · )` values as `O` (the constant-integrand identity).
* `ForMathlib.Tensor.momentOp_conj_unitary` / `ForMathlib.Tensor.momentOp_comm_unitary` — the unitary
  invariance of the moment operator.
-/

noncomputable section

open scoped TensorProduct Matrix
open Matrix MeasureTheory Topology

namespace ForMathlib.Tensor

open SchurWeyl

/-! ### Compactness of the unitary group -/

/-- Each entry of a unitary matrix has norm at most `1`. -/
theorem unitary_entry_norm_le_one (d : ℕ) {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d) : ‖M i j‖ ≤ 1 := by
  have h_unitary : star (M) * M = 1 := by
    exact hM.1
  replace h_unitary := congr_fun ( congr_fun h_unitary j ) j
  simp_all +decide [ Matrix.mul_apply, Complex.ext_iff ]
  exact Real.sqrt_le_iff.mpr ⟨ by positivity, by simpa [ Complex.normSq_apply, sq ] using h_unitary.1 ▸ Finset.single_le_sum ( fun x _ => add_nonneg ( mul_self_nonneg ( M x j |> Complex.re ) ) ( mul_self_nonneg ( M x j |> Complex.im ) ) ) ( Finset.mem_univ i ) ⟩

/-- The unitary group is a closed subset of the space of matrices contained in the
compact "polydisc" of matrices with entries of norm `≤ 1`; hence it is compact. -/
theorem isCompact_unitaryGroup (d : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  have h_unitary_closed : IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
    isClosed_unitary
  refine IsCompact.of_isClosed_subset (s := Set.pi Set.univ fun _ =>
      Set.pi Set.univ fun _ => Metric.closedBall ( 0 : ℂ ) 1) ?_ h_unitary_closed ?_
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ProperSpace.isCompact_closedBall _ _
  · exact fun M hM => fun i _ j _ => mem_closedBall_zero_iff.mpr ( unitary_entry_norm_le_one d hM i j )

/-- The unitary group is a compact topological space. -/
instance instCompactSpaceUnitaryGroup (d : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin d) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup d)

/-! ### Measurable structure and the Haar probability measure -/

/-- The space of matrices is second countable (a finite product of copies of `ℂ`). -/
instance instSecondCountableMatrix (d : ℕ) :
    SecondCountableTopology (Matrix (Fin d) (Fin d) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℂ))

/-- The Borel σ-algebra on the unitary group. -/
instance instMeasurableSpaceUnitaryGroup (d : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (Fin d) ℂ) := borel _

instance instBorelSpaceUnitaryGroup (d : ℕ) :
    BorelSpace (Matrix.unitaryGroup (Fin d) ℂ) := ⟨rfl⟩

/-- The (unnormalized) left Haar measure on the unitary group assigns positive mass to
the whole (nonempty, open) space. -/
theorem haar_univ_ne_zero (d : ℕ) :
    (Measure.haar (G := Matrix.unitaryGroup (Fin d) ℂ)) Set.univ ≠ 0 := by
  by_contra h_contra
  convert h_contra.not_gt ( ?_ )
  apply_rules [ IsOpen.measure_pos, isOpen_univ ]
  exact ⟨ 1, Set.mem_univ 1 ⟩

/-- The left Haar measure on the (compact) unitary group is finite. -/
theorem haar_univ_ne_top (d : ℕ) :
    (Measure.haar (G := Matrix.unitaryGroup (Fin d) ℂ)) Set.univ ≠ ⊤ :=
  (measure_ne_top _ _)

/-- The **Haar probability measure** on the unitary group `U(d)`: the left Haar measure
normalized to total mass `1`. -/
def haarProb (d : ℕ) : Measure (Matrix.unitaryGroup (Fin d) ℂ) :=
  ((Measure.haar (G := Matrix.unitaryGroup (Fin d) ℂ)) Set.univ)⁻¹ •
    Measure.haar (G := Matrix.unitaryGroup (Fin d) ℂ)

/-- `haarProb d` is a probability measure. -/
instance instIsProbabilityMeasureHaarProb (d : ℕ) : IsProbabilityMeasure (haarProb d) := by
  constructor
  unfold haarProb
  simp

/-- `haarProb d` is left invariant. -/
instance instIsMulLeftInvariantHaarProb (d : ℕ) : (haarProb d).IsMulLeftInvariant := by
  unfold haarProb
  infer_instance

/-! ### The conjugation action and the moment operator -/

variable {d k : ℕ}

/-- A matrix `U` as an endomorphism of `ℂ^d`, via `Matrix.toLin'`. -/
def endOf (U : Matrix (Fin d) (Fin d) ℂ) : Module.End ℂ (Fin d → ℂ) := Matrix.toLin' U

/-- `endOf` turns matrix multiplication into composition of endomorphisms. -/
theorem endOf_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    endOf (A * B) = endOf A ∘ₗ endOf B :=
  Matrix.toLin'_mul A B

/-- `endOf 1 = id`. -/
theorem endOf_one : endOf (1 : Matrix (Fin d) (Fin d) ℂ) = LinearMap.id := by
  simp [endOf]

/-- The diagonal action is multiplicative: `g^{⊗k} ∘ h^{⊗k} = (g ∘ h)^{⊗k}`. -/
theorem diagAction_comp (g h : Module.End ℂ (Fin d → ℂ)) :
    diagAction d k g ∘ₗ diagAction d k h = diagAction d k (g ∘ₗ h) := by
  unfold diagAction
  rw [← PiTensorProduct.map_comp]

/-- The diagonal action of the identity is the identity. -/
theorem diagAction_id : diagAction d k (LinearMap.id) = LinearMap.id := by
  unfold diagAction; simp [PiTensorProduct.map_id]

/-- The conjugation action `O ↦ U^{⊗k} O U^{†⊗k}` on operators, where `U†` is the
conjugate transpose `star U`. -/
def actOn (O : Module.End ℂ (TensV d k)) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Module.End ℂ (TensV d k) :=
  diagAction d k (endOf (U : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ O ∘ₗ
    diagAction d k (endOf (star (U : Matrix (Fin d) (Fin d) ℂ)))

/-- For a unitary `U`, `(U†)^{⊗k} ∘ U^{⊗k} = id`. -/
theorem diagAction_endOf_unitary_left (U : Matrix.unitaryGroup (Fin d) ℂ) :
    diagAction d k (endOf (star (U : Matrix (Fin d) (Fin d) ℂ))) ∘ₗ
      diagAction d k (endOf (U : Matrix (Fin d) (Fin d) ℂ)) = LinearMap.id := by
  rw [diagAction_comp, ← endOf_mul]
  have : star (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff'.1 U.2)
  rw [this, endOf_one, diagAction_id]

/-- For a unitary `U`, `U^{⊗k} ∘ (U†)^{⊗k} = id`. -/
theorem diagAction_endOf_unitary_right (U : Matrix.unitaryGroup (Fin d) ℂ) :
    diagAction d k (endOf (U : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ
      diagAction d k (endOf (star (U : Matrix (Fin d) (Fin d) ℂ))) = LinearMap.id := by
  rw [diagAction_comp, ← endOf_mul]
  have : (U : Matrix (Fin d) (Fin d) ℂ) * star (U : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff.1 U.2)
  rw [this, endOf_one, diagAction_id]

/-
The matrix entry of the conjugation action is a continuous function of `U`.
-/
theorem continuous_actOn_entry (O : Module.End ℂ (TensV d k))
    (I J : Fin k → Fin d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      toEndMatrix d k (actOn O U) I J) := by
  have h_cont : Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => (toEndMatrix d k (diagAction d k (endOf (U : Matrix (Fin d) (Fin d) ℂ))) * toEndMatrix d k O * toEndMatrix d k (diagAction d k (endOf (star (U : Matrix (Fin d) (Fin d) ℂ)))) ) I J) := by
    have h_cont : Continuous (fun U : Matrix (Fin d) (Fin d) ℂ => (toEndMatrix d k (diagAction d k (endOf U)) * toEndMatrix d k O * toEndMatrix d k (diagAction d k (endOf (star U)))) I J) := by
      simp +decide only [mul_apply, toEndMatrix_diagAction];
      simp +decide [ endOf ];
      fun_prop;
    exact h_cont.comp continuous_subtype_val;
  unfold actOn;
  convert h_cont using 2;
  simp +decide [ toEndMatrix ];
  rw [ ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp ];
  rw [ LinearMap.comp_assoc ]

/-- Each matrix entry of the conjugation action is `haarProb`-integrable. -/
theorem integrable_actOn_entry (O : Module.End ℂ (TensV d k))
    (I J : Fin k → Fin d) :
    Integrable (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      toEndMatrix d k (actOn O U) I J) (haarProb d) :=
  (continuous_actOn_entry O I J).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The matrix of the Haar moment operator: the entrywise Haar average of `actOn O U`. -/
def momentMatrix (O : Module.End ℂ (TensV d k)) :
    Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ :=
  fun I J => ∫ U, toEndMatrix d k (actOn O U) I J ∂(haarProb d)

/-- The **Haar moment operator** `𝔼_{U∼μ_H}[U^{⊗k} O U^{†⊗k}]`, defined as the operator
whose matrix in the computational basis is the entrywise Haar average of `actOn O U`. -/
def momentOp (O : Module.End ℂ (TensV d k)) : Module.End ℂ (TensV d k) :=
  (toEndMatrix d k).symm (momentMatrix O)

/-- The matrix of `momentOp O` is `momentMatrix O`. -/
theorem toEndMatrix_momentOp (O : Module.End ℂ (TensV d k)) :
    toEndMatrix d k (momentOp O) = momentMatrix O := by
  simp [momentOp]

/-! ### Property (P2): the trace identity -/

/-
**Pointwise (P2).** Since `V_d^†(σ)` commutes with `U^{⊗k}` and
`(U†)^{⊗k} ∘ U^{⊗k} = id`, conjugating `O` by `U` does not change the value
`Tr(V_d^†(σ) · )`.
-/
theorem trace_permDual_actOn (σ : Equiv.Perm (Fin k)) (O : Module.End ℂ (TensV d k))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ actOn O U) =
      LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ O) := by
  convert LinearMap.trace_mul_comm ℂ ( permDual d σ ∘ₗ O ∘ₗ diagAction d k ( endOf ( star U ) ) ) ( diagAction d k ( endOf U ) ) using 1;
  · convert LinearMap.trace_mul_comm ℂ ( permDual d σ ∘ₗ diagAction d k ( endOf U ) ) ( O ∘ₗ diagAction d k ( endOf ( star U ) ) ) using 1;
    convert LinearMap.trace_mul_comm ℂ ( permDual d σ ) ( O ∘ₗ diagAction d k ( endOf ( star U ) ) * diagAction d k ( endOf U ) ) using 1;
    simp +decide [ mul_assoc, ForMathlib.Tensor.permDual, ForMathlib.Tensor.permAction_diagAction_comm ];
    rfl;
  · convert LinearMap.trace_mul_comm ℂ ( permDual d σ ∘ₗ O ) ( diagAction d k ( endOf ( star U ) ) ∘ₗ diagAction d k ( endOf U ) ) using 1;
    · rw [ ForMathlib.Tensor.diagAction_endOf_unitary_left U ] ; aesop ( simp_config := { singlePass := true } ) ;
    · convert LinearMap.trace_mul_comm ℂ ( diagAction d k ( endOf U ) ∘ₗ ( permDual d σ ∘ₗ O ) ) ( diagAction d k ( endOf ( star U ) ) ) using 1

/-
**Property (P2).** The Haar moment operator has the same `Tr(V_d^†(σ) · )` values
as `O` for every permutation `σ`.
-/
theorem momentOp_trace (σ : Equiv.Perm (Fin k)) (O : Module.End ℂ (TensV d k)) :
    LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ momentOp O) =
      LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ O) := by
  have h_trace_eq : ∀ (f g : Module.End ℂ (TensV d k)), LinearMap.trace ℂ (TensV d k) (f ∘ₗ g) = Matrix.trace (toEndMatrix d k f * toEndMatrix d k g) := by
    intros f g; exact (by
    unfold toEndMatrix; simp +decide [ ← LinearMap.toMatrix_comp ] ;
    convert LinearMap.trace_eq_matrix_trace ℂ ( tensorBasis d k ) ( f ∘ₗ g ) using 1);
  rw [ h_trace_eq, h_trace_eq, ForMathlib.Tensor.toEndMatrix_momentOp ];
  have h_trace_eq : ∫ U : Matrix.unitaryGroup (Fin d) ℂ, Matrix.trace ((toEndMatrix d k (permDual d σ)) * (toEndMatrix d k (actOn O U))) ∂(haarProb d) = ∫ U : Matrix.unitaryGroup (Fin d) ℂ, Matrix.trace ((toEndMatrix d k (permDual d σ)) * (toEndMatrix d k O)) ∂(haarProb d) := by
    have h_trace_eq : ∀ U : Matrix.unitaryGroup (Fin d) ℂ, Matrix.trace ((toEndMatrix d k (permDual d σ)) * (toEndMatrix d k (actOn O U))) = Matrix.trace ((toEndMatrix d k (permDual d σ)) * (toEndMatrix d k O)) := by
      intro U
      have := ForMathlib.Tensor.trace_permDual_actOn σ O U
      simp_all +decide [ ForMathlib.Tensor.toEndMatrix ];
    simp only [ h_trace_eq ];
  convert h_trace_eq using 1;
  · simp +decide [ Matrix.trace, Matrix.mul_apply, momentMatrix ];
    rw [ MeasureTheory.integral_finset_sum ];
    · rw [ Finset.sum_congr rfl ];
      intro i hi; rw [ MeasureTheory.integral_finset_sum ] ;
      · exact Finset.sum_congr rfl fun _ _ => by rw [ MeasureTheory.integral_const_mul ] ;
      · exact fun j _ => MeasureTheory.Integrable.const_mul ( ForMathlib.Tensor.integrable_actOn_entry O j i ) _;
    · exact fun i _ => MeasureTheory.integrable_finset_sum _ fun j _ => MeasureTheory.Integrable.const_mul ( ForMathlib.Tensor.integrable_actOn_entry O j i ) _;
  · simp +decide [ ForMathlib.Tensor.haarProb ]

/-! ### Unitary invariance of the moment operator -/

/-
Conjugating `actOn O U` by a unitary `W` corresponds to left-translating the
argument: `W^{⊗k} (actOn O U) (W†)^{⊗k} = actOn O (W * U)`.
-/
theorem conj_actOn (O : Module.End ℂ (TensV d k)) (W U : Matrix.unitaryGroup (Fin d) ℂ) :
    diagAction d k (endOf (W : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ actOn O U ∘ₗ
        diagAction d k (endOf (star (W : Matrix (Fin d) (Fin d) ℂ))) =
      actOn O (W * U) := by
  ext;
  simp +decide [ actOn, endOf_mul ];
  rw [ ← diagAction_comp, ← diagAction_comp ];
  rfl

/-
**Unitary invariance (P1, geometric form).** The Haar moment operator is invariant
under conjugation by every unitary `W`: `W^{⊗k} M (W†)^{⊗k} = M`. This is the
left-invariance of the Haar measure.
-/
theorem momentOp_conj_unitary (O : Module.End ℂ (TensV d k))
    (W : Matrix.unitaryGroup (Fin d) ℂ) :
    diagAction d k (endOf (W : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ momentOp O ∘ₗ
        diagAction d k (endOf (star (W : Matrix (Fin d) (Fin d) ℂ))) =
      momentOp O := by
  -- By definition of `momentOp`, we know that `toEndMatrix d k (momentOp O) = momentMatrix O`.
  have h_momentOp : toEndMatrix d k (momentOp O) = momentMatrix O :=
    toEndMatrix_momentOp O
  refine' ( toEndMatrix d k ).injective _;
  -- We'll use the fact that `toEndMatrix d k` is linear and multiplicative to simplify the expression.
  have h_linear : ∀ (A B : Module.End ℂ (TensV d k)), toEndMatrix d k (A ∘ₗ B) = toEndMatrix d k A * toEndMatrix d k B := by
    intros A B; exact (by
    convert LinearMap.toMatrix_comp ( tensorBasis d k ) ( tensorBasis d k ) ( tensorBasis d k ) A B using 1);
  have h_integral : ∀ (I J : Fin k → Fin d), ∫ U : Matrix.unitaryGroup (Fin d) ℂ, (toEndMatrix d k (actOn O (W * U))) I J ∂(haarProb d) = ∫ U : Matrix.unitaryGroup (Fin d) ℂ, (toEndMatrix d k (actOn O U)) I J ∂(haarProb d) := by
    have h_integral : ∀ (f : Matrix.unitaryGroup (Fin d) ℂ → ℂ), MeasureTheory.Integrable f (haarProb d) → ∫ U : Matrix.unitaryGroup (Fin d) ℂ, f (W * U) ∂(haarProb d) = ∫ U : Matrix.unitaryGroup (Fin d) ℂ, f U ∂(haarProb d) := by
      intro f hf;
      convert MeasureTheory.integral_mul_left_eq_self ( fun U => f U ) W using 1;
      infer_instance;
    exact fun I J => h_integral _ ( ForMathlib.Tensor.integrable_actOn_entry O I J );
  ext I J; simp +decide [ *, Matrix.mul_apply ] ;
  convert h_integral I J using 1;
  rw [ show ( fun U : Matrix.unitaryGroup ( Fin d ) ℂ => ( toEndMatrix d k ) ( actOn O ( W * U ) ) I J ) = fun U : Matrix.unitaryGroup ( Fin d ) ℂ => ( toEndMatrix d k ( diagAction d k ( endOf ( W : Matrix ( Fin d ) ( Fin d ) ℂ ) ) ) * ( toEndMatrix d k ( actOn O U ) ) * ( toEndMatrix d k ( diagAction d k ( endOf ( star ( W : Matrix ( Fin d ) ( Fin d ) ℂ ) ) ) ) ) ) I J from funext fun U => ?_ ];
  · simp +decide [ Matrix.mul_apply, Finset.mul_sum _ _ _, Finset.sum_mul ];
    rw [ MeasureTheory.integral_finsetSum ];
    · rw [ Finset.sum_comm ];
      refine' Finset.sum_congr rfl fun i hi => _;
      rw [ MeasureTheory.integral_finsetSum ];
      · simp +decide [ mul_assoc, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, momentMatrix ];
      · exact fun _ _ => MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( ForMathlib.Tensor.integrable_actOn_entry O _ _ ) _ ) _;
    · intro i hi; exact MeasureTheory.integrable_finsetSum _ fun j hj => MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( ForMathlib.Tensor.integrable_actOn_entry O j i ) _ ) _;
  · rw [ ← h_linear, ← h_linear ];
    rw [ ← conj_actOn ];
    rw [ LinearMap.comp_assoc ]

/-
The Haar moment operator commutes with `W^{⊗k}` for every unitary `W`.
-/
theorem momentOp_comm_unitary (O : Module.End ℂ (TensV d k))
    (W : Matrix.unitaryGroup (Fin d) ℂ) :
    momentOp O ∘ₗ diagAction d k (endOf (W : Matrix (Fin d) (Fin d) ℂ)) =
      diagAction d k (endOf (W : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ momentOp O := by
  -- Apply the equality from h_unitary_commutativity.
  have := ForMathlib.Tensor.momentOp_conj_unitary O W;
  simp_all +decide [ LinearMap.ext_iff ];
  intro x
  have := this ((diagAction d k (endOf (star (W : Matrix (Fin d) (Fin d) ℂ)))) x)
  simp_all +decide;
  rw [ ← this ];
  congr! 2;
  convert ForMathlib.Tensor.diagAction_endOf_unitary_left W |> congr_arg ( fun f => f x ) using 1

/-! ### Property (P1) and Theorem 10 for the genuine Haar moment operator

To conclude that the moment operator lies in the span of the permutation operators we use
that it commutes with every `g^{⊗k}` (not only the unitary ones). The reduction from the
unitary commutant to the full commutant is the classical density of the unitary group.

We carry out this reduction in full, modulo a *single* classical input — the existence of a
**singular value decomposition** `M = U₁ · diag(s) · U₂` of every complex matrix into two
unitaries and a diagonal matrix (`ForMathlib.Tensor.svd_exists`). Mathlib currently has no SVD
(nor polar decomposition) for matrices, so this one fact is left as the lone hypothesis;
everything else — the diagonal case via a torus argument and the assembly — is proved. -/

/-
**Orthonormal completion of the normalized columns.** If `Nᴴ * N` is the diagonal
matrix with nonnegative real entries `D`, then the columns of `N` are pairwise orthogonal
and the `i`-th column has squared norm `D i`. Normalizing the columns with `D i ≠ 0` gives
an orthonormal family, which extends to an orthonormal basis `b` of `EuclideanSpace ℂ (Fin d)`
with `b i` equal to the normalized `i`-th column whenever `D i ≠ 0`.
-/


/-
The diagonal action of a diagonal matrix is diagonal in the tensor basis, with entry
`∏ m, z (I m)` on the diagonal.
-/
theorem toEndMatrix_diagAction_diagonal (z : Fin d → ℂ) (I J : Fin k → Fin d) :
    toEndMatrix d k (diagAction d k (endOf (Matrix.diagonal z))) I J =
      if I = J then ∏ m, z (I m) else 0 := by
  convert ForMathlib.Tensor.diagAction_diagonal ( fun i => z i ) I J using 1;
  congr! 2;
  ext; simp [endOf, LinearMap.pi];
  rw [ Pi.single_apply, Pi.single_apply ] ; aesop

/-
A diagonal matrix with unit-modulus entries is unitary.
-/
theorem diagonal_mem_unitaryGroup (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    Matrix.diagonal z ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  constructor;
  · ext i j; by_cases hi : i = j <;> simp_all +decide [ Matrix.mul_apply ] ;
    · simp +decide [ hi, Matrix.one_apply, diagonal ];
      simp +decide [ mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz ];
    · rw [ Finset.sum_eq_single i ] <;> aesop;
  · ext i j ; by_cases hi : i = j <;> simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    · simp +decide [ hi, Matrix.one_apply ];
    · exact Or.inr ( if_neg ( Ne.symm hi ) )

/-
An equality of index-monomials `∏ m, z (I m) = ∏ m, z (J m)` holding for all arguments
on the unit torus holds for all arguments.
-/
theorem prod_eq_of_torus (I J : Fin k → Fin d)
    (h : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ = 1) → ∏ m, z (I m) = ∏ m, z (J m)) :
    ∀ z : Fin d → ℂ, ∏ m, z (I m) = ∏ m, z (J m) := by
  intro z
  by_contra h_neq
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin d, (Finset.univ.filter (fun m => I m = i₀)).card ≠ (Finset.univ.filter (fun m => J m = i₀)).card := by
    contrapose! h_neq;
    -- By definition of $cnt$, we can rewrite the products as $\prod_{i} z_i^{cnt_I(i)}$ and $\prod_{i} z_i^{cnt_J(i)}$.
    have h_prod_eq : (∏ m, z (I m)) = (∏ i, z i ^ (Finset.univ.filter (fun m => I m = i)).card) ∧ (∏ m, z (J m)) = (∏ i, z i ^ (Finset.univ.filter (fun m => J m = i)).card) := by
      simp +decide only [Finset.card_filter];
      simp +decide only [← Finset.prod_pow_eq_pow_sum];
      exact ⟨ by rw [ Finset.prod_comm ] ; exact Finset.prod_congr rfl fun _ _ => by aesop, by rw [ Finset.prod_comm ] ; exact Finset.prod_congr rfl fun _ _ => by aesop ⟩;
    aesop;
  -- Apply the hypothesis to the torus point `z := Function.update (fun _ => (1:ℂ)) i₀ w` for `w` with `‖w‖ = 1`.
  have h_torus : ∀ w : ℂ, ‖w‖ = 1 → w ^ (Finset.univ.filter (fun m => I m = i₀)).card = w ^ (Finset.univ.filter (fun m => J m = i₀)).card := by
    intro w hw; specialize h ( fun i => if i = i₀ then w else 1 ) ; simp_all +decide [ Finset.prod_ite ] ;
    exact h fun i => by split_ifs <;> simp +decide [ * ] ;
  -- The unit circle is infinite, so the polynomial `X ^ cnt I i₀ - X ^ cnt J i₀` has infinitely many roots, forcing `cnt I i₀ = cnt J i₀`.
  have h_inf_roots : Set.Infinite {w : ℂ | ‖w‖ = 1} := by
    intro H;
    have := H.image Complex.im;
    refine' this.not_infinite <| Set.Icc_infinite ( show -1 < 1 by norm_num ) |> Set.Infinite.mono fun x hx => _;
    exact ⟨ Complex.exp ( Complex.I * Real.arcsin x ), by simp +decide [ Complex.norm_exp ], by simp +decide [ Complex.exp_im, Real.sin_arcsin hx.1 hx.2 ] ⟩;
  have h_poly_zero : (Polynomial.X ^ (Finset.univ.filter (fun m => I m = i₀)).card - Polynomial.X ^ (Finset.univ.filter (fun m => J m = i₀)).card : Polynomial ℂ) = 0 := by
    exact Classical.not_not.1 fun h => h_inf_roots <| Set.Finite.subset ( Polynomial.roots ( Polynomial.X ^ Finset.card ( Finset.filter ( fun m => I m = i₀ ) Finset.univ ) - Polynomial.X ^ Finset.card ( Finset.filter ( fun m => J m = i₀ ) Finset.univ ) ) |> Multiset.toFinset |> Finset.finite_toSet ) fun x hx => by aesop;
  simp_all +decide [ sub_eq_zero ];
  replace h_poly_zero := congr_arg Polynomial.natDegree h_poly_zero ; aesop

/-
If `X` commutes with `g^{⊗k}` for every unitary `g`, then it commutes with the diagonal
action of *every* diagonal matrix.
-/
theorem comm_diagAction_diagonal (X : Module.End ℂ (TensV d k))
    (h : ∀ W : Matrix.unitaryGroup (Fin d) ℂ,
      X ∘ₗ diagAction d k (endOf (W : Matrix (Fin d) (Fin d) ℂ)) =
        diagAction d k (endOf (W : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ X)
    (z : Fin d → ℂ) :
    X ∘ₗ diagAction d k (endOf (Matrix.diagonal z)) =
      diagAction d k (endOf (Matrix.diagonal z)) ∘ₗ X := by
  have h_diagonal : ∀ I J, toEndMatrix d k X I J * (∏ m, z (J m)) = (∏ m, z (I m)) * toEndMatrix d k X I J := by
    intro I J; by_cases hIJ : toEndMatrix d k X I J = 0 <;> simp_all +decide [ mul_comm ] ;
    apply ForMathlib.Tensor.prod_eq_of_torus;
    intro z hz;
    have := h ( Matrix.diagonal z ) ( ForMathlib.Tensor.diagonal_mem_unitaryGroup z hz ) ; replace := congr_arg ( fun f => toEndMatrix d k f I J ) this; simp_all +decide ;
    have h_eq : toEndMatrix d k (X ∘ₗ diagAction d k (endOf (Matrix.diagonal z))) I J = toEndMatrix d k X I J * (∏ m, z (J m)) ∧ toEndMatrix d k (diagAction d k (endOf (Matrix.diagonal z)) ∘ₗ X) I J = (∏ m, z (I m)) * toEndMatrix d k X I J := by
      have h_eq : ∀ (f g : Module.End ℂ (TensV d k)), toEndMatrix d k (f ∘ₗ g) = toEndMatrix d k f * toEndMatrix d k g := by
        intros f g; exact (by
          convert LinearMap.toMatrix_comp ( tensorBasis d k ) ( tensorBasis d k ) ( tensorBasis d k ) f g using 1);
      simp_all +decide [ Matrix.mul_apply, ForMathlib.Tensor.toEndMatrix_diagAction_diagonal ];
    grind;
  have h_diagonal : toEndMatrix d k X * toEndMatrix d k (diagAction d k (endOf (Matrix.diagonal z))) = toEndMatrix d k (diagAction d k (endOf (Matrix.diagonal z))) * toEndMatrix d k X := by
    ext I J; simp +decide [ Matrix.mul_apply, ForMathlib.Tensor.toEndMatrix_diagAction_diagonal ] ;
    exact h_diagonal I J;
  convert ( toEndMatrix d k ).injective ( show toEndMatrix d k ( X ∘ₗ diagAction d k ( endOf ( diagonal z ) ) ) = toEndMatrix d k ( diagAction d k ( endOf ( diagonal z ) ) ∘ₗ X ) from ?_ ) using 1;
  convert h_diagonal using 1;
  · convert LinearMap.toMatrix_comp ( tensorBasis d k ) ( tensorBasis d k ) ( tensorBasis d k ) X ( diagAction d k ( endOf ( diagonal z ) ) ) using 1;
  · convert LinearMap.toMatrix_comp ( tensorBasis d k ) ( tensorBasis d k ) ( tensorBasis d k ) _ _ using 1

/-
**Density of the unitary group.** If `X` commutes with `g^{⊗k}` for every *unitary*
`g`, then it commutes with `g^{⊗k}` for *every* `g`, i.e. it lies in the centralizer of
the diagonal image. Proved from `svd_exists` together with `comm_diagAction_diagonal`.
-/
theorem mem_centralizer_of_comm_unitary (X : Module.End ℂ (TensV d k))
    (h : ∀ W : Matrix.unitaryGroup (Fin d) ℂ,
      X ∘ₗ diagAction d k (endOf (W : Matrix (Fin d) (Fin d) ℂ)) =
        diagAction d k (endOf (W : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ X) :
    X ∈ (diagImage d k).centralizer := by
  intro Y hY
  obtain ⟨g, hg⟩ := hY
  have h_comm : X ∘ₗ diagAction d k g = diagAction d k g ∘ₗ X := by
    -- By hypothesis, we know that $X$ commutes with $diagAction d k g$ for any unitary $g$.
    have h_comm : ∀ (U : Matrix.unitaryGroup (Fin d) ℂ), X ∘ₗ diagAction d k (endOf (U : Matrix (Fin d) (Fin d) ℂ)) = diagAction d k (endOf (U : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ X := by
      assumption;
    -- By hypothesis, we know that $X$ commutes with $diagAction d k g$ for any matrix $g$.
    have h_comm : ∀ (g : Matrix (Fin d) (Fin d) ℂ), X ∘ₗ diagAction d k (endOf g) = diagAction d k (endOf g) ∘ₗ X := by
      intro g
      obtain ⟨U₁, U₂, s, hg⟩ := svd_exists g;
      have h_comm_diag : X ∘ₗ diagAction d k (endOf (Matrix.diagonal s)) = diagAction d k (endOf (Matrix.diagonal s)) ∘ₗ X := by
        apply ForMathlib.Tensor.comm_diagAction_diagonal X h_comm s;
      have h_comm_diag : X ∘ₗ (diagAction d k (endOf (U₁ : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ diagAction d k (endOf (Matrix.diagonal s)) ∘ₗ diagAction d k (endOf (U₂ : Matrix (Fin d) (Fin d) ℂ))) = (diagAction d k (endOf (U₁ : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ diagAction d k (endOf (Matrix.diagonal s)) ∘ₗ diagAction d k (endOf (U₂ : Matrix (Fin d) (Fin d) ℂ))) ∘ₗ X := by
        simp_all +decide [ LinearMap.ext_iff, LinearMap.comp_assoc ];
      convert h_comm_diag using 1 <;> simp +decide [ hg, endOf_mul, diagAction_comp ];
      · rfl;
      · rw [ LinearMap.comp_assoc ];
    convert h_comm ( LinearMap.toMatrix ( Pi.basisFun ℂ ( Fin d ) ) ( Pi.basisFun ℂ ( Fin d ) ) g ) using 1;
    · unfold endOf; aesop;
    · simp +decide [ endOf ];
  convert h_comm.symm using 1; all_goals exact hg ▸ rfl

/-- **Property (P1).** The Haar moment operator lies in the span of the permutation
operators. -/
theorem momentOp_mem_span (O : Module.End ℂ (TensV d k)) :
    momentOp O ∈ Submodule.span ℂ (permImage d k) := by
  have hc : momentOp O ∈ (diagImage d k).centralizer :=
    mem_centralizer_of_comm_unitary (momentOp O) (momentOp_comm_unitary O)
  rw [schur_weyl] at hc
  exact hc

/-- **Computing moments (Theorem 10), for the genuine Haar moment operator.** The Haar
moment operator `momentOp O = 𝔼_{U∼μ_H}[U^{⊗k} O U^{†⊗k}]` is a linear combination of the
permutation operators `V_d(π)` whose coefficients `c_π` solve the Weingarten linear
system. -/
theorem weingarten_moment_haar (O : Module.End ℂ (TensV d k)) :
    ∃ c : Equiv.Perm (Fin k) → ℂ,
      momentOp O = ∑ π : Equiv.Perm (Fin k), c π • permOp d π ∧
      ∀ σ : Equiv.Perm (Fin k),
        LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ O) =
          ∑ π : Equiv.Perm (Fin k),
            c π * LinearMap.trace ℂ (TensV d k) (permDual d σ ∘ₗ permOp d π) :=
  weingarten_moment_decomposition_of_props O (momentOp O) (momentOp_mem_span O)
    (fun σ => momentOp_trace σ O)

end ForMathlib.Tensor

end
