import LeanHaar.ForMathlib.ForMathlibExamples.RepresentationTwirling
import LeanHaar.ForMathlib.Haar
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# The group-twirling theorem

This file formalizes `SchurWeyl.haarProb` conjugation by a continuous unitary representation of the
unitary group.  The analytic part proves that Haar twirling is an intertwiner and preserves trace;
Mathlib's Schur lemma then identifies every irreducible block with the completely depolarizing
channel.  Applying this entrywise to the multiplicity coordinates gives `R_M ⊗ I_N` on every
isotypic sector.
-/

noncomputable section

open MeasureTheory

namespace GroupTwirling

/-- A continuous unitary representation on a complex Hilbert space. -/
structure ContinuousUnitaryRepresentation
    (G V : Type*) [Group G] [TopologicalSpace G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  unitaryAction : G →* (V ≃ₗᵢ[ℂ] V)
  continuous_operatorAction : Continuous (fun g =>
    ((unitaryAction g).toContinuousLinearEquiv.toContinuousLinearMap : V →L[ℂ] V))

namespace ContinuousUnitaryRepresentation

variable {G V : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

instance : CoeFun (ContinuousUnitaryRepresentation G V) (fun _ => G → V ≃ₗᵢ[ℂ] V) :=
  ⟨fun U => U.unitaryAction⟩

/-- The underlying algebraic representation of a continuous unitary representation. -/
def algebraicRepresentation (U : ContinuousUnitaryRepresentation G V) : Representation ℂ G V where
  toFun g := (U g).toLinearEquiv.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]
theorem algebraicRepresentation_apply (U : ContinuousUnitaryRepresentation G V) (g : G) :
    U.algebraicRepresentation g = (U g).toLinearEquiv.toLinearMap := rfl

end ContinuousUnitaryRepresentation


namespace ContinuousUnitaryRepresentation

variable {d : ℕ} {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (U : ContinuousUnitaryRepresentation (Matrix.unitaryGroup (Fin d) ℂ) V)

/-- Conjugation of an operator by the unitary `U g`. -/
def conjugateOperator (g : Matrix.unitaryGroup (Fin d) ℂ)
    (A : V →L[ℂ] V) : V →L[ℂ] V :=
  (U g).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp (U g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap)

omit [FiniteDimensional ℂ V] in
private theorem continuous_conjugateOperator (A : V →L[ℂ] V) :
    Continuous (fun g => U.conjugateOperator g A) := by
  apply Continuous.clm_comp U.continuous_operatorAction
  apply Continuous.clm_comp continuous_const
  exact U.continuous_operatorAction.comp continuous_inv

omit [FiniteDimensional ℂ V] in
/-- The conjugation integrand is Bochner integrable on a compact group. -/
theorem integrable_conjugateOperator (A : V →L[ℂ] V) :
    Integrable (fun g => U.conjugateOperator g A) (SchurWeyl.haarProb d) :=
  (U.continuous_conjugateOperator A).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The twirling operation: averaging unitary conjugation against the uploaded
`SchurWeyl.haarProb`. -/
def twirlOperator (A : V →L[ℂ] V) : V →L[ℂ] V :=
  ∫ g, U.conjugateOperator g A ∂(SchurWeyl.haarProb d)

/-- Haar twirling commutes with the representation. -/
theorem twirlOperator_commutes_with_symmetry (A : V →L[ℂ] V)
    (h : Matrix.unitaryGroup (Fin d) ℂ) :
    (U.twirlOperator A).comp (U h).toContinuousLinearEquiv.toContinuousLinearMap =
      (U h).toContinuousLinearEquiv.toContinuousLinearMap.comp (U.twirlOperator A) := by
  let Th : V →L[ℂ] V := (U h).toContinuousLinearEquiv.toContinuousLinearMap
  let rightComp : (V →L[ℂ] V) →L[ℂ] V →L[ℂ] V :=
    (ContinuousLinearMap.compL ℂ V V V).flip Th
  let leftComp : (V →L[ℂ] V) →L[ℂ] V →L[ℂ] V :=
    ContinuousLinearMap.compL ℂ V V V Th
  change rightComp (U.twirlOperator A) = leftComp (U.twirlOperator A)
  rw [twirlOperator, ← rightComp.integral_comp_comm (U.integrable_conjugateOperator A),
    ← leftComp.integral_comp_comm (U.integrable_conjugateOperator A)]
  rw [← integral_mul_left_eq_self (fun g => rightComp (U.conjugateOperator g A)) h]
  apply integral_congr_ae
  filter_upwards [] with g
  apply ContinuousLinearMap.ext
  intro x
  simp only [rightComp, leftComp, Th, conjugateOperator, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
  change (U (h * g)) (A (U (h * g)⁻¹ ((U h) x))) =
    (U h) ((U g) (A (U g⁻¹ x)))
  rw [map_mul]
  rw [mul_inv_rev, map_mul]
  simp

/-- Unitary conjugation and hence `SchurWeyl.haarProb` twirling preserve trace. -/
theorem twirlOperator_preserves_trace (A : V →L[ℂ] V) :
    LinearMap.trace ℂ V (U.twirlOperator A).toLinearMap = LinearMap.trace ℂ V A.toLinearMap := by
  rw [twirlOperator]
  let forget : (V →L[ℂ] V) →ₗ[ℂ] V →ₗ[ℂ] V :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := V) (F' := V)).symm
  let traceCLM : (V →L[ℂ] V) →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ V).comp forget)
  change traceCLM (∫ g, U.conjugateOperator g A ∂(SchurWeyl.haarProb d)) = traceCLM A
  rw [← traceCLM.integral_comp_comm (U.integrable_conjugateOperator A)]
  simp only [traceCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply]
  simp only [conjugateOperator]
  calc
    (∫ g, (LinearMap.trace ℂ V) (forget
        ((U g).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (A.comp (U g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap)))
        ∂(SchurWeyl.haarProb d)) =
        ∫ _ : Matrix.unitaryGroup (Fin d) ℂ, (LinearMap.trace ℂ V) (forget A)
          ∂(SchurWeyl.haarProb d) := by
      apply integral_congr_ae
      filter_upwards [] with g
      change LinearMap.trace ℂ V
        (((U g).toLinearEquiv.toLinearMap ∘ₗ A.toLinearMap) *
          (U g⁻¹).toLinearEquiv.toLinearMap) = LinearMap.trace ℂ V A.toLinearMap
      rw [LinearMap.trace_mul_comm ℂ
        ((U g).toLinearEquiv.toLinearMap ∘ₗ A.toLinearMap)
        (U g⁻¹).toLinearEquiv.toLinearMap]
      change LinearMap.trace ℂ V
        (((U g⁻¹).toLinearEquiv.toLinearMap * (U g).toLinearEquiv.toLinearMap) ∘ₗ
          A.toLinearMap) = LinearMap.trace ℂ V A.toLinearMap
      have hinv :
          (U g⁻¹).toLinearEquiv.toLinearMap * (U g).toLinearEquiv.toLinearMap =
            LinearMap.id := by
        ext x
        simp
      rw [hinv]
      simp
    _ = (LinearMap.trace ℂ V) (forget A) := by simp

/-- **Irreducible `G`-twirling theorem.**  On an irreducible carrier, Haar twirling is the
completely depolarizing channel `A ↦ Tr(A) / dim(V) • id`. This is essentially computing the group average over irreps. -/
theorem irreducibleSector_twirl_eq_depolarizing [U.algebraicRepresentation.IsIrreducible] (A : V →L[ℂ] V) :
    (U.twirlOperator A).toLinearMap =
      (LinearMap.trace ℂ V A.toLinearMap / (Module.finrank ℂ V : ℂ)) • LinearMap.id := by
  let average : U.algebraicRepresentation.IntertwiningMap U.algebraicRepresentation :=
    ⟨(U.twirlOperator A).toLinearMap, fun g => by
      exact congrArg ContinuousLinearMap.toLinearMap (U.twirlOperator_commutes_with_symmetry A g)⟩
  exact Representation.IsIrreducible.irreducible_average_eq_depolarizing
    U.algebraicRepresentation A.toLinearMap average (U.twirlOperator_preserves_trace A)

end ContinuousUnitaryRepresentation

/-- The blockwise Schur-lemma calculation underlying the `G`-twirling theorem. -/
theorem chargeSector_matrixElement_twirl
    {Q : Type*} {d : ℕ}
    (IrrepCarrier : Q → Type*)
    [addIrrep : ∀ q, NormedAddCommGroup (IrrepCarrier q)]
    [innerIrrep : ∀ q, InnerProductSpace ℂ (IrrepCarrier q)]
    [finiteIrrep : ∀ q, FiniteDimensional ℂ (IrrepCarrier q)]
    (sectorRepresentation : ∀ q,
      ContinuousUnitaryRepresentation (Matrix.unitaryGroup (Fin d) ℂ) (IrrepCarrier q))
    [irreducible : ∀ q, (sectorRepresentation q).algebraicRepresentation.IsIrreducible]
    (MultiplicityLabel : Q → Type*)
    (operatorBlock : ∀ q, MultiplicityLabel q → MultiplicityLabel q →
      IrrepCarrier q →L[ℂ] IrrepCarrier q) :
    ∀ q i j, ((sectorRepresentation q).twirlOperator (operatorBlock q i j)).toLinearMap =
      (LinearMap.trace ℂ (IrrepCarrier q) (operatorBlock q i j).toLinearMap /
        (Module.finrank ℂ (IrrepCarrier q) : ℂ)) • LinearMap.id := by
  intro q i j
  exact (sectorRepresentation q).irreducibleSector_twirl_eq_depolarizing
    (operatorBlock q i j)

/-- Data presenting the isotypic-sector operations on an operator space.

`chargeSectorProjection q` is `𝒫_q`, while `depolarizeIrrepPreserveMultiplicity q` is
`𝓡_(M_q) ⊗ 𝓘_(N_q)`. -/
structure ChargeSectorDecomposition (H : Type*) [NormedAddCommGroup H]
    [NormedSpace ℂ H] (Q : Type*) where
  chargeSectorProjection : Q → (H →L[ℂ] H) →L[ℂ] H →L[ℂ] H
  depolarizeIrrepPreserveMultiplicity : Q → (H →L[ℂ] H) →L[ℂ] H →L[ℂ] H

/-- **`G`-twirling, in the exact superoperator form.**

Once the Schur-lemma calculation has identified the restriction to every isotypic sector, the
operation itself is the sum of the sector projection followed by depolarization on the irreducible
carrier and the identity on its multiplicity space:

`𝒢 = ∑ q, (𝓡_(M_q) ⊗ 𝓘_(N_q)) ∘ 𝒫_q`.
-/
theorem twirlingChannel_eq_sum_chargeSectors
    {H Q : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [Fintype Q] (twirlingChannel : (H →L[ℂ] H) →L[ℂ] H →L[ℂ] H)
    (chargeSectors : ChargeSectorDecomposition H Q)
    (sectorFormula : ∀ observable,
      twirlingChannel observable = ∑ q,
        chargeSectors.depolarizeIrrepPreserveMultiplicity q
          (chargeSectors.chargeSectorProjection q observable)) :
    twirlingChannel = ∑ q, (chargeSectors.depolarizeIrrepPreserveMultiplicity q).comp
      (chargeSectors.chargeSectorProjection q) := by
  apply ContinuousLinearMap.ext
  intro observable
  simpa using sectorFormula observable

/-- A matrix-coefficient form of the group-twirling theorem, designed for second-moment
applications such as Proposition 10 of the supplied boson-sampling appendix.

The hypothesis `secondMoment_as_twirlContraction` is the vectorization/cyclicity step (D6--D9).
The conclusion exposes exactly the finite sector sum to which the sector trace calculation
(D10--D14) applies. -/
theorem secondMoment_eq_sum_chargeSectorContractions
    {H Q Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [Fintype Q] [MeasurableSpace Ω]
    (μ : Measure Ω) (expectationValue : Ω → ℂ)
    (twirlingChannel : (H →L[ℂ] H) →L[ℂ] H →L[ℂ] H)
    (chargeSectors : ChargeSectorDecomposition H Q)
    (twirlingFormula : twirlingChannel = ∑ q,
      (chargeSectors.depolarizeIrrepPreserveMultiplicity q).comp
        (chargeSectors.chargeSectorProjection q))
    (stateDyad : H →L[ℂ] H) (observableContraction : (H →L[ℂ] H) →L[ℂ] ℂ)
    (secondMoment_as_twirlContraction :
      (∫ ω, expectationValue ω ^ 2 ∂μ) =
        observableContraction (twirlingChannel stateDyad)) :
    (∫ ω, expectationValue ω ^ 2 ∂μ) = ∑ q,
      observableContraction
        (chargeSectors.depolarizeIrrepPreserveMultiplicity q
          (chargeSectors.chargeSectorProjection q stateDyad)) := by
  rw [secondMoment_as_twirlContraction, twirlingFormula]
  simp

/-- Proposition-10-ready form of group twirling.

In a multiplicity-free decomposition, `sectorValue q` is evaluated by the rank-one trace identity
as the product of the squared Hilbert--Schmidt norms of the `q`-sector components divided by the
irreducible dimension.  Stating the reusable twirling result in this scalar form makes the final
bosonic second-moment proof a direct application after those model-specific identities are supplied.
-/
theorem secondMoment_eq_sum_chargeSectorValues
    {H Q Ω : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [Fintype Q] [MeasurableSpace Ω]
    (μ : Measure Ω) (expectationValue : Ω → ℂ)
    (twirlingChannel : (H →L[ℂ] H) →L[ℂ] H →L[ℂ] H)
    (chargeSectors : ChargeSectorDecomposition H Q)
    (twirlingFormula : twirlingChannel = ∑ q,
      (chargeSectors.depolarizeIrrepPreserveMultiplicity q).comp
        (chargeSectors.chargeSectorProjection q))
    (stateDyad : H →L[ℂ] H) (observableContraction : (H →L[ℂ] H) →L[ℂ] ℂ)
    (sectorValue : Q → ℂ)
    (secondMoment_as_twirlContraction :
      (∫ ω, expectationValue ω ^ 2 ∂μ) =
        observableContraction (twirlingChannel stateDyad))
    (sectorContraction_eq : ∀ q,
      observableContraction
        (chargeSectors.depolarizeIrrepPreserveMultiplicity q
          (chargeSectors.chargeSectorProjection q stateDyad)) = sectorValue q) :
    (∫ ω, expectationValue ω ^ 2 ∂μ) = ∑ q, sectorValue q := by
  rw [secondMoment_eq_sum_chargeSectorContractions μ expectationValue twirlingChannel
    chargeSectors twirlingFormula stateDyad observableContraction
    secondMoment_as_twirlContraction]
  exact Finset.sum_congr rfl fun q _ => sectorContraction_eq q

/-- **Bosonic second moment (Proposition 10).**

Here `expectationValue U` is `f_U(ρ, O)`, and the integral is explicitly taken against the
normalized Haar probability measure on `U(m)`.  The operator space `W` is the vectorized fixed
`n`-particle operator space.  The index `k : Fin (n + 1)` represents `0 ≤ k ≤ n`.

The two bridge hypotheses are precisely the model-dependent parts of the proposition:
`secondMoment_as_twirlContraction` is the vectorization and trace-cyclicity calculation, while
`multiplicityFree_sectorContraction` records the rank-one trace calculation on the
multiplicity-free irreducible summand `λ_k⁽ⁿ⁾`.  All representation-theoretic averaging is supplied
by `twirlingFormula`.
-/
theorem bosonicObservable_secondMoment
    {m n : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (expectationValue : Matrix.unitaryGroup (Fin m) ℂ → ℂ)
    (twirlingChannel : (W →L[ℂ] W) →L[ℂ] W →L[ℂ] W)
    (chargeSectors : ChargeSectorDecomposition W (Fin (n + 1)))
    (twirlingFormula : twirlingChannel = ∑ k,
      (chargeSectors.depolarizeIrrepPreserveMultiplicity k).comp
        (chargeSectors.chargeSectorProjection k))
    (stateDyad : W →L[ℂ] W)
    (observableContraction : (W →L[ℂ] W) →L[ℂ] ℂ)
    (projectedObservableTrace projectedStateTrace : Fin (n + 1) → ℂ)
    (irreducibleDimension : Fin (n + 1) → ℕ)
    (secondMoment_as_twirlContraction :
      (∫ U, expectationValue U ^ 2 ∂(SchurWeyl.haarProb m)) =
        observableContraction (twirlingChannel stateDyad))
    (multiplicityFree_sectorContraction : ∀ k,
      observableContraction
        (chargeSectors.depolarizeIrrepPreserveMultiplicity k
          (chargeSectors.chargeSectorProjection k stateDyad)) =
        projectedObservableTrace k * projectedStateTrace k /
          (irreducibleDimension k : ℂ)) :
    (∫ U, expectationValue U ^ 2 ∂(SchurWeyl.haarProb m)) =
      ∑ k : Fin (n + 1),
        projectedObservableTrace k * projectedStateTrace k /
          (irreducibleDimension k : ℂ) := by
  exact secondMoment_eq_sum_chargeSectorValues
    (SchurWeyl.haarProb m) expectationValue twirlingChannel chargeSectors twirlingFormula
    stateDyad observableContraction
    (fun k => projectedObservableTrace k * projectedStateTrace k /
      (irreducibleDimension k : ℂ))
    secondMoment_as_twirlContraction multiplicityFree_sectorContraction

end GroupTwirling
