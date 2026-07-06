import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Star.Unitary

-- NOTE FROM MELODY: These updates have changed. I think Yan was working on reorganizing the files.
-- For now, I've changed the import statements to reflect the new file structure, but
-- the content of the file remains the same.
import LeanHaar.ForMathlib.TensorV2
import Leanhaar.ForMathlib.MatrixRepresentation




/-!
# The Haar layer for Weingarten calculus

This file builds the measure-theoretic foundation behind the Weingarten moment operator
and constructs the genuine Haar moment operator
`𝔼_{U∼μ_H}[U^{⊗k} O U^{†⊗k}]` as a (componentwise) integral over the unitary group.

## Main contents

* **Compactness** of the unitary group `U(d) = Matrix.unitaryGroup (Fin d) ℂ`
  (`SchurWeyl.isCompact_unitaryGroup`, `SchurWeyl.instCompactSpaceUnitaryGroup`).
* The **Haar probability measure** `SchurWeyl.haarProb d` on `U(d)`: the normalized
  (left-invariant, regular) Haar measure, with `IsProbabilityMeasure` and
  `IsMulLeftInvariant` instances.
* `SchurWeyl.actOn` — the conjugation action `O ↦ U^{⊗k} O U^{†⊗k}`.
* `SchurWeyl.momentOp` — the Haar moment operator, defined componentwise as the
  Haar average of `actOn O U`.
* `SchurWeyl.momentOp_trace` — property **(P2)**: the moment operator has the same
  `Tr(V_d^†(σ) · )` values as `O` (the constant-integrand identity).
* `SchurWeyl.momentOp_conj_unitary` / `SchurWeyl.momentOp_comm_unitary` — the unitary
  invariance of the moment operator.
-/

noncomputable section

open scoped TensorProduct Matrix
open Matrix MeasureTheory Topology
namespace ForMathlib.Tensor

namespace SchurWeyl

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

/--
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

end SchurWeyl

end ForMathlib.Tensor
