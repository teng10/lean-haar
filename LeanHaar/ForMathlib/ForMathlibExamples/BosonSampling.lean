import LeanHaar.ForMathlib.ForMathlibExamples.RepresentationTwirling
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# The group-twirling theorem

This file formalizes normalized Haar conjugation by a continuous unitary representation of a
compact group.  The analytic part proves that Haar twirling is an intertwiner and preserves trace;
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
  toMonoidHom : G →* (V ≃ₗᵢ[ℂ] V)
  continuous_toContinuousLinearMap : Continuous (fun g =>
    ((toMonoidHom g).toContinuousLinearEquiv.toContinuousLinearMap : V →L[ℂ] V))

namespace ContinuousUnitaryRepresentation

variable {G V : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

instance : CoeFun (ContinuousUnitaryRepresentation G V) (fun _ => G → V ≃ₗᵢ[ℂ] V) :=
  ⟨fun T => T.toMonoidHom⟩

/-- The underlying algebraic representation of a continuous unitary representation. -/
def toRepresentation (T : ContinuousUnitaryRepresentation G V) : Representation ℂ G V where
  toFun g := (T g).toLinearEquiv.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]
theorem toRepresentation_apply (T : ContinuousUnitaryRepresentation G V) (g : G) :
    T.toRepresentation g = (T g).toLinearEquiv.toLinearMap := rfl

end ContinuousUnitaryRepresentation

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]

private theorem haar_univ_ne_zero : (Measure.haar (G := G)) Set.univ ≠ 0 := by
  by_contra h
  convert h.not_gt ?_
  apply_rules [IsOpen.measure_pos, isOpen_univ]
  exact ⟨1, Set.mem_univ 1⟩

private theorem haar_univ_ne_top : (Measure.haar (G := G)) Set.univ ≠ ⊤ :=
  measure_ne_top _ _

/-- Normalized Haar measure on a compact group. -/
def haarProbability : Measure G :=
  ((Measure.haar (G := G)) Set.univ)⁻¹ • Measure.haar (G := G)

instance : IsProbabilityMeasure (haarProbability (G := G)) := by
  constructor
  simp [haarProbability]

instance : (haarProbability (G := G)).IsMulLeftInvariant := by
  unfold haarProbability
  infer_instance

end Haar

namespace ContinuousUnitaryRepresentation

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (T : ContinuousUnitaryRepresentation G V)

/-- Conjugation of an operator by the unitary `T g`. -/
def conjugate (g : G) (A : V →L[ℂ] V) : V →L[ℂ] V :=
  (T g).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp (T g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap)

omit [MeasurableSpace G] [BorelSpace G] [CompactSpace G] [FiniteDimensional ℂ V] in
private theorem continuous_conjugate (A : V →L[ℂ] V) :
    Continuous (fun g => T.conjugate g A) := by
  apply Continuous.clm_comp T.continuous_toContinuousLinearMap
  apply Continuous.clm_comp continuous_const
  exact T.continuous_toContinuousLinearMap.comp continuous_inv

omit [FiniteDimensional ℂ V] in
/-- The conjugation integrand is Bochner integrable on a compact group. -/
theorem integrable_conjugate (A : V →L[ℂ] V) :
    Integrable (fun g => T.conjugate g A) (haarProbability (G := G)) :=
  (T.continuous_conjugate A).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The `G`-twirling operation: normalized Haar averaging of unitary conjugation. -/
def twirl (A : V →L[ℂ] V) : V →L[ℂ] V :=
  ∫ g, T.conjugate g A ∂haarProbability (G := G)

/-- Haar twirling commutes with the representation. -/
theorem twirl_commutes (A : V →L[ℂ] V) (h : G) :
    (T.twirl A).comp (T h).toContinuousLinearEquiv.toContinuousLinearMap =
      (T h).toContinuousLinearEquiv.toContinuousLinearMap.comp (T.twirl A) := by
  let Th : V →L[ℂ] V := (T h).toContinuousLinearEquiv.toContinuousLinearMap
  let rightComp : (V →L[ℂ] V) →L[ℂ] V →L[ℂ] V :=
    (ContinuousLinearMap.compL ℂ V V V).flip Th
  let leftComp : (V →L[ℂ] V) →L[ℂ] V →L[ℂ] V :=
    ContinuousLinearMap.compL ℂ V V V Th
  change rightComp (T.twirl A) = leftComp (T.twirl A)
  rw [twirl, ← rightComp.integral_comp_comm (T.integrable_conjugate A),
    ← leftComp.integral_comp_comm (T.integrable_conjugate A)]
  rw [← integral_mul_left_eq_self (fun g => rightComp (T.conjugate g A)) h]
  apply integral_congr_ae
  filter_upwards [] with g
  apply ContinuousLinearMap.ext
  intro x
  simp only [rightComp, leftComp, Th, conjugate, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
  change (T (h * g)) (A (T (h * g)⁻¹ ((T h) x))) =
    (T h) ((T g) (A (T g⁻¹ x)))
  rw [map_mul]
  rw [mul_inv_rev, map_mul]
  simp

/-- Unitary conjugation and hence normalized Haar twirling preserve trace. -/
theorem trace_twirl (A : V →L[ℂ] V) :
    LinearMap.trace ℂ V (T.twirl A).toLinearMap = LinearMap.trace ℂ V A.toLinearMap := by
  rw [twirl]
  let forget : (V →L[ℂ] V) →ₗ[ℂ] V →ₗ[ℂ] V :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := V) (F' := V)).symm
  let traceCLM : (V →L[ℂ] V) →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ V).comp forget)
  change traceCLM (∫ g, T.conjugate g A ∂haarProbability (G := G)) = traceCLM A
  rw [← traceCLM.integral_comp_comm (T.integrable_conjugate A)]
  simp only [traceCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply]
  simp only [conjugate]
  calc
    (∫ g, (LinearMap.trace ℂ V) (forget
        ((T g).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (A.comp (T g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap)))
        ∂haarProbability (G := G)) =
        ∫ _ : G, (LinearMap.trace ℂ V) (forget A) ∂haarProbability (G := G) := by
      apply integral_congr_ae
      filter_upwards [] with g
      change LinearMap.trace ℂ V
        (((T g).toLinearEquiv.toLinearMap ∘ₗ A.toLinearMap) *
          (T g⁻¹).toLinearEquiv.toLinearMap) = LinearMap.trace ℂ V A.toLinearMap
      rw [LinearMap.trace_mul_comm ℂ
        ((T g).toLinearEquiv.toLinearMap ∘ₗ A.toLinearMap)
        (T g⁻¹).toLinearEquiv.toLinearMap]
      change LinearMap.trace ℂ V
        (((T g⁻¹).toLinearEquiv.toLinearMap * (T g).toLinearEquiv.toLinearMap) ∘ₗ
          A.toLinearMap) = LinearMap.trace ℂ V A.toLinearMap
      have hinv :
          (T g⁻¹).toLinearEquiv.toLinearMap * (T g).toLinearEquiv.toLinearMap =
            LinearMap.id := by
        ext x
        simp
      rw [hinv]
      simp
    _ = (LinearMap.trace ℂ V) (forget A) := by simp

/-- **Irreducible `G`-twirling theorem.**  On an irreducible carrier, Haar twirling is the
completely depolarizing channel `A ↦ Tr(A) / dim(V) • id`. -/
theorem twirl_eq_depolarizing [T.toRepresentation.IsIrreducible] (A : V →L[ℂ] V) :
    (T.twirl A).toLinearMap =
      (LinearMap.trace ℂ V A.toLinearMap / (Module.finrank ℂ V : ℂ)) • LinearMap.id := by
  let average : T.toRepresentation.IntertwiningMap T.toRepresentation :=
    ⟨(T.twirl A).toLinearMap, fun g => by
      exact congrArg ContinuousLinearMap.toLinearMap (T.twirl_commutes A g)⟩
  exact Representation.IsIrreducible.average_eq_trace_div_finrank_smul_id
    T.toRepresentation A.toLinearMap average (T.trace_twirl A)

end ContinuousUnitaryRepresentation

/-- The blockwise Schur-lemma calculation underlying the `G`-twirling theorem. -/
theorem groupTwirling_block
    {G Q : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    (M : Q → Type*)
    [addM : ∀ q, NormedAddCommGroup (M q)]
    [innerM : ∀ q, InnerProductSpace ℂ (M q)]
    [finiteM : ∀ q, FiniteDimensional ℂ (M q)]
    (T : ∀ q, ContinuousUnitaryRepresentation G (M q))
    [irreducible : ∀ q, (T q).toRepresentation.IsIrreducible]
    (N : Q → Type*)
    (A : ∀ q, N q → N q → M q →L[ℂ] M q) :
    ∀ q i j, ((T q).twirl (A q i j)).toLinearMap =
      (LinearMap.trace ℂ (M q) (A q i j).toLinearMap /
        (Module.finrank ℂ (M q) : ℂ)) • LinearMap.id := by
  intro q i j
  exact (T q).twirl_eq_depolarizing (A q i j)

/-- Data presenting the isotypic-sector operations on an operator space.

`projection q` is `𝒫_q`, while `depolarizeTensorIdentity q` is
`𝓡_(M_q) ⊗ 𝓘_(N_q)`. -/
structure IsotypicSectorOperations (H : Type*) [NormedAddCommGroup H]
    [NormedSpace ℂ H] (Q : Type*) where
  projection : Q → (H →L[ℂ] H) →L[ℂ] H →L[ℂ] H
  depolarizeTensorIdentity : Q → (H →L[ℂ] H) →L[ℂ] H →L[ℂ] H

/-- **`G`-twirling, in the exact superoperator form.**

Once the Schur-lemma calculation has identified the restriction to every isotypic sector, the
operation itself is the sum of the sector projection followed by depolarization on the irreducible
carrier and the identity on its multiplicity space:

`𝒢 = ∑ q, (𝓡_(M_q) ⊗ 𝓘_(N_q)) ∘ 𝒫_q`.
-/
theorem groupTwirling
    {H Q : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [Fintype Q] (𝒢 : (H →L[ℂ] H) →L[ℂ] H →L[ℂ] H)
    (D : IsotypicSectorOperations H Q)
    (sector_decomposition : ∀ A,
      𝒢 A = ∑ q, D.depolarizeTensorIdentity q (D.projection q A)) :
    𝒢 = ∑ q, (D.depolarizeTensorIdentity q).comp (D.projection q) := by
  apply ContinuousLinearMap.ext
  intro A
  simpa using sector_decomposition A

end GroupTwirling
