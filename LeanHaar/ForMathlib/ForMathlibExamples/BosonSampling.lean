/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/
import LeanHaar.ForMathlib.Defs
import LeanHaar.ForMathlib.Commutation
import LeanHaar.ForMathlib.DirectProof
import LeanHaar.ForMathlib.Main
import LeanHaar.ForMathlib.Weingarten
import LeanHaar.ForMathlib.Haar


/-!
# Group twirling for the `SchurWeyl` operator model

This file states the finite-sector assembly step of the group-twirling theorem directly in the
operator model developed in `Haar.lean`.  In particular, the twirling operation is
`SchurWeyl.momentOp`, its integrand is `SchurWeyl.actOn`, and integration uses
`SchurWeyl.haarProb` on `Matrix.unitaryGroup (Fin d) ℂ`.

The representation-theoretic input is packaged as `SchurWeyl.TwirlingDecomposition`.  Its
`sectorAverage` field is the sectorwise Schur-orthogonality calculation.  This separation keeps
the assembly theorem independent of a particular construction of isotypic projections while
making it immediately usable with the definitions in the ForMathlib development.
-/

noncomputable section

open scoped BigOperators TensorProduct
open Matrix MeasureTheory

namespace SchurWeyl

variable {d k n : ℕ}


/-- The operator space on which the Haar twirling operation acts. -/
abbrev Operator (d k : ℕ) := Module.End ℂ (TensV d k)

/-- Data and hypotheses expressing a finite isotypic decomposition for the concrete operator
model used by `momentOp`.

`projection q` is the superoperator `O ↦ Π_q O Π_q`, while `replacement q` is the
superoperator `R_{M_q} ⊗ I_{N_q}`.  The fields `actOn_eq_sum` and `sectorAverage` are respectively
the decomposition of the conjugation orbit into sector contributions and the sectorwise
Schur-orthogonality identity.  The latter is stated entrywise because `momentOp` itself is defined
entrywise in `Haar.lean`. -/
structure TwirlingDecomposition (d k : ℕ) (Q : Type*) [Fintype Q] where
  /-- The projection superoperator onto an isotypic sector. -/
  projection : Q → Module.End ℂ (Operator d k)
  /-- Depolarization on the irrep carrier, tensored with the identity on its multiplicity space. -/
  replacement : Q → Module.End ℂ (Operator d k)
  /-- The contribution of one isotypic sector to the conjugation orbit. -/
  sectorAct : Q → Matrix.unitaryGroup (Fin d) ℂ → Operator d k → Operator d k
  /-- The full conjugation orbit is the sum of its sector contributions. -/
  actOn_eq_sum : ∀ (O : Operator d k) (U : Matrix.unitaryGroup (Fin d) ℂ),
    actOn O U = ∑ q, sectorAct q U O
  /-- Every matrix coefficient of every sector contribution is Haar integrable. -/
  sectorIntegrable : ∀ (O : Operator d k) (q : Q) (I J : Fin k → Fin d),
    Integrable (fun U ↦ toEndMatrix d k (sectorAct q U O) I J) (haarProb d)
  /-- Sectorwise Schur orthogonality. -/
  sectorAverage : ∀ (O : Operator d k) (q : Q) (I J : Fin k → Fin d),
    (∫ U, toEndMatrix d k (sectorAct q U O) I J ∂(haarProb d)) =
      toEndMatrix d k (replacement q (projection q O)) I J

variable {Q : Type*} [Fintype Q]

/-- **Group twirling theorem**, in the operator model of the ForMathlib files.

For a finite isotypic decomposition, Haar twirling is the sum over sectors of the completely
depolarizing channel on the irrep carrier tensored with the identity channel on the multiplicity
space, after projection onto that sector. -/
theorem momentOp_eq_sum_sector (D : TwirlingDecomposition d k Q) (O : Operator d k) :
    momentOp O = ∑ q, D.replacement q (D.projection q O) := by
  apply (toEndMatrix d k).injective
  ext I J
  rw [toEndMatrix_momentOp]
  simp only [momentMatrix]
  simp_rw [D.actOn_eq_sum]
  simp_rw [map_sum (toEndMatrix d k) _ Finset.univ]
  simp_rw [Matrix.sum_apply]
  rw [integral_finsetSum Finset.univ]
  · simp_rw [D.sectorAverage]
  · intro q _
    exact D.sectorIntegrable O q I J

/-- Superoperator-valued form of `momentOp_eq_sum_sector`. -/
theorem momentOp_eq_sum_sector_apply (D : TwirlingDecomposition d k Q) :
    momentOp = fun O ↦ ∑ q, D.replacement q (D.projection q O) := by
  funext O
  exact momentOp_eq_sum_sector D O

/-- The additional data used in Proposition 10 after vectorizing the state and observable.

The operator `secondMomentOperator` is the vectorized rank-one operator
`P̂⁽ⁿ⁾ |ρ⟩⟩⟨⟨ρ| P̂⁽ⁿ⁾` from (D9), and `evaluate` is contraction against
`|O⟩⟩⟨⟨O|`.  The two norm-square fields are the Hilbert--Schmidt norm squares of the
corresponding isotypic components.  Keeping these identifications as data makes the result
independent of a particular construction of the bosonic Fock space and of its vectorization. -/
structure BosonSamplingSecondMoment (d k n : ℕ) where
  /-- Multiplicity-free isotypic decomposition indexed by `0, …, n`. -/
  decomposition : TwirlingDecomposition d k (Fin (n + 1))
  /-- The vectorized rank-one state operator occurring in (D9). -/
  secondMomentOperator : Operator d k
  /-- Contraction with the vectorized rank-one observable operator. -/
  evaluate : Operator d k →ₗ[ℂ] ℂ
  /-- The expectation value `f_U(ρ, O)` from (D2)--(D4). -/
  expectationValue : Matrix.unitaryGroup (Fin d) ℂ → ℝ
  /-- Equations (D6)--(D9): the Haar expectation is the contraction of the moment operator.

  This is the model-specific vectorization identity connecting the PDF's expectation-value
  notation to the abstract `momentOp`; the latter is itself defined as the Haar average. -/
  expectation_secondMoment_eq_momentOp :
    (∫ U, expectationValue U ^ 2 ∂(haarProb d)) =
      (evaluate (momentOp secondMomentOperator)).re
  /-- Dimension of the irreducible component labelled by `q`. -/
  irrepDim : Fin (n + 1) → ℕ
  irrepDim_pos : ∀ q, 0 < irrepDim q
  /-- `‖P_q⁽ⁿ⁾(ρ)‖₂²`. -/
  stateComponentNormSq : Fin (n + 1) → ℝ
  /-- `‖P_q⁽ⁿ⁾(O)‖₂²`. -/
  observableComponentNormSq : Fin (n + 1) → ℝ
  /-- Evaluation of each depolarized isotypic block, i.e. equations (D10)--(D14). -/
  evaluate_sector : ∀ q,
    (evaluate
      (decomposition.replacement q
        (decomposition.projection q secondMomentOperator))).re =
      stateComponentNormSq q * observableComponentNormSq q / irrepDim q

/-- Intermediate moment-operator form of Proposition 10.

Assume the multiplicity-free decomposition of Lemma 1.  Contracting the Haar moment operator
with the rank-one observable gives the sum, over `q = 0, …, n`, of the product of the two
projected Hilbert--Schmidt norm squares divided by the corresponding irrep dimension. -/
theorem bosonSampling_secondMoment_contraction (D : BosonSamplingSecondMoment d k n) :
    (D.evaluate (momentOp D.secondMomentOperator)).re =
      ∑ q, D.stateComponentNormSq q * D.observableComponentNormSq q / D.irrepDim q := by
  rw [momentOp_eq_sum_sector D.decomposition, map_sum]
  change Complex.reLm (∑ q, D.evaluate
    (D.decomposition.replacement q
      (D.decomposition.projection q D.secondMomentOperator))) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun q _ ↦ D.evaluate_sector q)

/-- **Proposition 10, equation (D1), in expectation-value form.**

For Haar-random `U ∈ U(d)`, the second moment of the expectation value `f_U(ρ, O)` is
`∑ q, ‖P_q⁽ⁿ⁾(ρ)‖₂² ‖P_q⁽ⁿ⁾(O)‖₂² / d_q⁽ⁿ⁾`.  Unlike the intermediate contraction theorem,
this statement has exactly the expectation integral appearing in the PDF. -/
theorem bosonSampling_secondMoment (D : BosonSamplingSecondMoment d k n) :
    (∫ U, D.expectationValue U ^ 2 ∂(haarProb d)) =
      ∑ q, D.stateComponentNormSq q * D.observableComponentNormSq q / D.irrepDim q := by
  rw [D.expectation_secondMoment_eq_momentOp]
  exact bosonSampling_secondMoment_contraction D

end SchurWeyl
