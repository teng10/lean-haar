import LeanHaar.ForMathlib.ForMathlibExamples.k1Moment
import LeanHaar.ForMathlib.ForMathlibExamples.k2Moment

/-!
# Quantum machine learning over Haar-random unitaries

This file formalizes Observations 56 and 57 from `qml.tex`. Samples remain elements of
`Matrix.unitaryGroup (Fin d) ℂ` equipped with `SchurWeyl.haarProb`, while all quantum
operators are endomorphisms of `SchurWeyl.TensV d k`.

The public observation statements display the Haar integrals and the conjugation action
`SchurWeyl.actOn` directly. Their tensor-contraction assumptions use the repository's
Haar moment operator `SchurWeyl.momentOp`. A small scalar `MomentSystem` interface
separates the reusable variance deduction from those Haar-specific calculations.
-/

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace QML

open SchurWeyl

/-- The compact group from which a Haar-random `d × d` unitary is sampled. -/
abbrev HaarUnitary (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

/-- A quantum operator on the `k`-fold tensor power of `ℂ^d`. -/
abbrev Operator (d k : ℕ) := Module.End ℂ (TensV d k)

/-- Trace of an endomorphism of a tensor power. -/
def operatorTrace {d k : ℕ} (A : Operator d k) : ℂ :=
  LinearMap.trace ℂ (TensV d k) A

/-- The commutator `[A,B] = AB - BA`, at the endomorphism level. -/
def commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : Module.End ℂ V) : Module.End ℂ V :=
  A ∘ₗ B - B ∘ₗ A

/-- Algebraic variance for an arbitrary scalar expectation functional. -/
def variance {Ω : Type*} (expectation : (Ω → ℂ) → ℂ) (X : Ω → ℂ) : ℂ :=
  expectation (fun ω => X ω ^ 2) - expectation X ^ 2

/-- A small interface recording the first two scalar moments of a random quantity. -/
structure MomentSystem {Ω : Type*} (expectation : (Ω → ℂ) → ℂ)
    (X : Ω → ℂ) (first second : ℂ) : Prop where
  first_eq : expectation X = first
  second_eq : expectation (fun ω => X ω ^ 2) = second

/-- The reusable algebraic deduction of mean and variance from a moment system. -/
theorem MomentSystem.mean_and_variance {Ω : Type*}
    {expectation : (Ω → ℂ) → ℂ} {X : Ω → ℂ} {first second : ℂ}
    (h : MomentSystem expectation X first second) :
    expectation X = first ∧ variance expectation X = second - first ^ 2 := by
  constructor
  · exact h.first_eq
  · simp only [variance, h.first_eq, h.second_eq]

/-- Integrating a trace contraction of the Haar conjugation action is the same as
contracting with the Haar moment operator. -/
theorem haar_integral_trace_actOn_comp {d k : ℕ} (A B : Operator d k) :
    (∫ U, operatorTrace (actOn A U ∘ₗ B) ∂(haarProb d)) =
      operatorTrace (momentOp A ∘ₗ B) := by
  unfold operatorTrace
  simp_rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d k)]
  change (∫ U, Matrix.trace (toEndMatrix d k (actOn A U ∘ₗ B)) ∂(haarProb d)) =
    Matrix.trace (toEndMatrix d k (momentOp A ∘ₗ B))
  simp_rw [toEndMatrix_comp]
  rw [toEndMatrix_momentOp]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, momentMatrix]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [MeasureTheory.integral_mul_const]
    · intro j hj
      exact (integrable_actOn_entry A i j).mul_const _
  · intro i hi
    exact MeasureTheory.integrable_finsetSum _ fun j _ =>
      (integrable_actOn_entry A i j).mul_const _

/-- **Observation 56 (expectation of the cost function).**

For an `n`-qubit system, normalized Haar sampling and tracelessness of `O` imply zero expected cost. -/
theorem expectation_cost_function (n : ℕ) (ρ O : Operator (2 ^ n) 1)
    (hO : operatorTrace O = 0) :
    (∫ U, operatorTrace (actOn ρ U ∘ₗ O) ∂(haarProb (2 ^ n))) = 0 := by
  rw [haar_integral_trace_actOn_comp, k1_moment]
  simp only [LinearMap.smul_comp, LinearMap.id_comp]
  change operatorTrace (((operatorTrace ρ / ((2 ^ n : ℕ) : ℂ)) • O)) = 0
  unfold operatorTrace at hO ⊢
  rw [map_smul, hO, smul_zero]

/-- **Observation 56 (variance of the cost function).**

For an `n`-qubit system, normalized Haar sampling, tracelessness of `O`, and the displayed
`momentOp` contraction imply the stated variance. The hypotheses exhibit the tensor-square
endomorphisms and their Haar moment contraction explicitly. -/
theorem variance_cost_function (n : ℕ) (ρ O : Operator (2 ^ n) 1)
    (state₂ observable₂ : Operator (2 ^ n) 2)
    (hO : operatorTrace O = 0)
    (hcost_sq : ∀ U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ,
      operatorTrace (actOn ρ U ∘ₗ O) ^ 2 =
        operatorTrace (actOn state₂ U ∘ₗ observable₂))
    (hmoment : operatorTrace (momentOp state₂ ∘ₗ observable₂) =
      ((operatorTrace (ρ ∘ₗ ρ) - ((2 ^ n : ℕ) : ℂ)⁻¹) /
        (((2 ^ n : ℕ) : ℂ) ^ 2 - 1)) * operatorTrace (O ∘ₗ O)) :
    ((∫ U, operatorTrace (actOn ρ U ∘ₗ O) ^ 2 ∂(haarProb (2 ^ n))) -
      (∫ U, operatorTrace (actOn ρ U ∘ₗ O) ∂(haarProb (2 ^ n))) ^ 2) =
      ((operatorTrace (ρ ∘ₗ ρ) - ((2 : ℂ) ^ n)⁻¹) /
        (((2 : ℂ) ^ n) ^ 2 - 1)) * operatorTrace (O ∘ₗ O) := by
  let expectation : (HaarUnitary (2 ^ n) → ℂ) → ℂ :=
    fun X => ∫ U, X U ∂(haarProb (2 ^ n))
  let X : HaarUnitary (2 ^ n) → ℂ :=
    fun U => operatorTrace (actOn ρ U ∘ₗ O)
  have hmean : expectation X = 0 := expectation_cost_function n ρ O hO
  have hsecond : expectation (fun U => X U ^ 2) =
      ((operatorTrace (ρ ∘ₗ ρ) - ((2 : ℂ) ^ n)⁻¹) /
        (((2 : ℂ) ^ n) ^ 2 - 1)) * operatorTrace (O ∘ₗ O) := by
    change (∫ U, operatorTrace (actOn ρ U ∘ₗ O) ^ 2 ∂(haarProb (2 ^ n))) = _
    calc
      _ = ∫ U, operatorTrace (actOn state₂ U ∘ₗ observable₂)
          ∂(haarProb (2 ^ n)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with U
            exact hcost_sq U
      _ = operatorTrace (momentOp state₂ ∘ₗ observable₂) :=
        haar_integral_trace_actOn_comp state₂ observable₂
      _ = _ := by simpa [Nat.cast_pow] using hmoment
  have hs : MomentSystem expectation X 0
      (((operatorTrace (ρ ∘ₗ ρ) - ((2 : ℂ) ^ n)⁻¹) /
        (((2 : ℂ) ^ n) ^ 2 - 1)) * operatorTrace (O ∘ₗ O)) :=
    ⟨hmean, hsecond⟩
  simpa [expectation, X, variance] using hs.mean_and_variance.2

/-- Cyclicity gives the algebraic core of the swap-trick computation for arbitrary
finite free endomorphism spaces, not only concrete matrices. -/
theorem trace_commutator_sq {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V] (A B : Module.End ℂ V) :
    LinearMap.trace ℂ V (commutator A B ∘ₗ commutator A B) =
      2 * LinearMap.trace ℂ V (A ∘ₗ B ∘ₗ A ∘ₗ B) -
        2 * LinearMap.trace ℂ V (A ∘ₗ A ∘ₗ B ∘ₗ B) := by
  have cyc (X Y Z : Module.End ℂ V) :
      LinearMap.trace ℂ V (X ∘ₗ Y ∘ₗ Z) =
        LinearMap.trace ℂ V (Y ∘ₗ Z ∘ₗ X) := by
    simpa only [LinearMap.comp_assoc] using
      (LinearMap.trace_comp_comm' X (Y ∘ₗ Z)).symm
  unfold commutator
  simp only [LinearMap.comp_sub, LinearMap.sub_comp, map_sub, LinearMap.comp_assoc]
  have h1 : LinearMap.trace ℂ V (A ∘ₗ B ∘ₗ B ∘ₗ A) =
      LinearMap.trace ℂ V (A ∘ₗ A ∘ₗ B ∘ₗ B) := by
    simpa only [LinearMap.comp_assoc] using
      (LinearMap.trace_comp_comm' A (A ∘ₗ B ∘ₗ B))
  have h2 := cyc B A (A ∘ₗ B)
  have h3 := cyc B A (B ∘ₗ A)
  simp only [LinearMap.comp_assoc] at h2 h3
  rw [h1, h2, h3]
  ring

/-- ** Barren plateaus (expectation).**

For two independent samples from `haarProb`, the explicit `momentOp` contractions imply
that the endomorphism-level gradient has zero mean. -/
theorem expectation_barren_plateau {d : ℕ} (ρ O H : Operator d 1)
    (firstInput firstTest : Operator d 1)
    (hfirst_as_moment :
      (∫ UA, ∫ UB,
        Complex.I * operatorTrace
          (actOn ρ UB ∘ₗ commutator H (actOn O UA⁻¹))
        ∂(haarProb d) ∂(haarProb d)) =
        operatorTrace (momentOp firstInput ∘ₗ firstTest))
    (hfirst_contraction : operatorTrace (momentOp firstInput ∘ₗ firstTest) = 0) :
    (∫ UA, ∫ UB,
      Complex.I * operatorTrace
        (actOn ρ UB ∘ₗ commutator H (actOn O UA⁻¹))
      ∂(haarProb d) ∂(haarProb d)) = 0 :=
  hfirst_as_moment.trans hfirst_contraction

/-- ** Barren plateaus (variance).**

For two independent samples from `haarProb`, the explicit `momentOp` contractions imply
that the endomorphism-level gradient has the stated variance. -/
theorem variance_barren_plateau {d : ℕ} (ρ O H : Operator d 1)
    (firstInput firstTest : Operator d 1)
    (secondInput secondTest : Operator d 2)
    (hfirst_as_moment :
      (∫ UA, ∫ UB,
        Complex.I * operatorTrace
          (actOn ρ UB ∘ₗ commutator H (actOn O UA⁻¹))
        ∂(haarProb d) ∂(haarProb d)) =
        operatorTrace (momentOp firstInput ∘ₗ firstTest))
    (hfirst_contraction : operatorTrace (momentOp firstInput ∘ₗ firstTest) = 0)
    (hsecond_as_moment :
      (∫ UA, ∫ UB,
        (Complex.I * operatorTrace
          (actOn ρ UB ∘ₗ commutator H (actOn O UA⁻¹))) ^ 2
        ∂(haarProb d) ∂(haarProb d)) =
        operatorTrace (momentOp secondInput ∘ₗ secondTest))
    (hsecond_contraction :
      operatorTrace (momentOp secondInput ∘ₗ secondTest) =
        2 * (d : ℂ) *
          ((operatorTrace (ρ ∘ₗ ρ) - (d : ℂ)⁻¹) / ((d : ℂ) ^ 2 - 1)) *
          (operatorTrace (O ∘ₗ O) / ((d : ℂ) ^ 2 - 1)) *
          operatorTrace (H ∘ₗ H)) :
    ((∫ UA, ∫ UB,
      (Complex.I * operatorTrace
        (actOn ρ UB ∘ₗ commutator H (actOn O UA⁻¹))) ^ 2
      ∂(haarProb d) ∂(haarProb d)) -
      (∫ UA, ∫ UB,
        Complex.I * operatorTrace
          (actOn ρ UB ∘ₗ commutator H (actOn O UA⁻¹))
        ∂(haarProb d) ∂(haarProb d)) ^ 2) =
      2 * (d : ℂ) *
        ((operatorTrace (ρ ∘ₗ ρ) - (d : ℂ)⁻¹) / ((d : ℂ) ^ 2 - 1)) *
        (operatorTrace (O ∘ₗ O) / ((d : ℂ) ^ 2 - 1)) *
        operatorTrace (H ∘ₗ H) := by
  let expectation : ((HaarUnitary d × HaarUnitary d) → ℂ) → ℂ :=
    fun X => ∫ UA, ∫ UB, X (UA, UB) ∂(haarProb d) ∂(haarProb d)
  let X : HaarUnitary d × HaarUnitary d → ℂ := fun U =>
    Complex.I * operatorTrace
      (actOn ρ U.2 ∘ₗ commutator H (actOn O U.1⁻¹))
  have hfirst : expectation X = 0 :=
    expectation_barren_plateau ρ O H firstInput firstTest hfirst_as_moment hfirst_contraction
  have hsecond : expectation (fun U => X U ^ 2) =
      2 * (d : ℂ) *
        ((operatorTrace (ρ ∘ₗ ρ) - (d : ℂ)⁻¹) / ((d : ℂ) ^ 2 - 1)) *
        (operatorTrace (O ∘ₗ O) / ((d : ℂ) ^ 2 - 1)) *
        operatorTrace (H ∘ₗ H) :=
    hsecond_as_moment.trans hsecond_contraction
  have hs : MomentSystem expectation X 0
      (2 * (d : ℂ) *
        ((operatorTrace (ρ ∘ₗ ρ) - (d : ℂ)⁻¹) / ((d : ℂ) ^ 2 - 1)) *
        (operatorTrace (O ∘ₗ O) / ((d : ℂ) ^ 2 - 1)) *
        operatorTrace (H ∘ₗ H)) := ⟨hfirst, hsecond⟩
  simpa [expectation, X, variance] using hs.mean_and_variance.2

end QML
