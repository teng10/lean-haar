import LeanHaar.Circuits.HaarMoment
import LeanHaar.Circuits.LocalGate
import LeanHaar.Circuits.Brickwork
import LeanHaar.Circuits.Circuit
import LeanHaar.Applications.MagicMonotone.HaarLayers

/-!
# Circuit API regression tests

These examples exercise chronology, independent occurrences, moments above the local
dimension, and ordered periodic support through the public circuit interfaces.
-/

noncomputable section

open MeasureTheory SchurWeyl SchurWeyl.Circuits

namespace LeanHaarTest

-- This statement uses no commutativity assumption: the first listed gate acts first.
theorem scheduleChronology {M : Type*} [Monoid M] (A B : M) :
    scheduleProduct (![A, B] : Fin 2 → M) = B * A := by simp

-- Reusing one placement still samples two independent unitary variables.
theorem repeatedIndependentGate {d D k : ℕ} (J : Matrix.unitaryGroup (Fin d) ℂ →ₜ* Matrix.unitaryGroup (Fin D) ℂ) :
    (∫ samples : Fin 2 → Matrix.unitaryGroup (Fin d) ℂ,
      vecActOn (k := k) (scheduleProduct (fun i => J (samples i)))
      ∂Measure.pi (fun _ : Fin 2 => haarProb d)) = gateMoment J k := by
  rw [integral_vecActOn_placed_schedule (fun _ : Fin 2 => J)
    (fun _ => J.continuous) (fun _ => haarProb d)]
  change scheduleProduct (fun _ : Fin 2 => gateMoment J k) = _
  simp

-- A one-qubit block in a three-qubit register admits the fifth moment.
private def singleSite : (Fin 1 ↪ Fin 3) where
  toFun _ := 1
  inj' _ _ _ := Subsingleton.elim _ _

theorem aboveLocalDimensionIdempotent :
    gateMoment (placeUnitary 2 singleSite) 5 * gateMoment (placeUnitary 2 singleSite) 5 =
      gateMoment (placeUnitary 2 singleSite) 5 := by simp

theorem aboveLocalDimensionAdjoint : (gateMoment (placeUnitary 2 singleSite) 5).adjoint =
    gateMoment (placeUnitary 2 singleSite) 5 := by simp

-- Two one-site gates leave the third site uncovered.
private def partialSites (g : Fin 2) : Fin 1 ↪ Fin 3 where
  toFun _ := g.castSucc
  inj' _ _ _ := Subsingleton.elim _ _

private theorem partialDisjoint :
    Pairwise fun g h : Fin 2 => Disjoint (Set.range (partialSites g))
      (Set.range (partialSites h)) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have hv : i.val = j.val := congrArg (fun x : Fin 3 => x.val) hb.symm
  exact hij (Fin.ext hv)

-- The third moment exceeds the one-site gate dimension, and site 2 is uncovered.
-- Order independence and self-adjointness still require only disjointness.
theorem partialLayerLaws :
    ¬ (3 ≤ 2 ^ 1) ∧ (∀ g, (2 : Fin 3) ∉ Set.range (partialSites g)) ∧
    circuitMoment 2 3 (fun g => partialSites (Fin.revPerm g)) = circuitMoment 2 3 partialSites ∧
      (circuitMoment 2 3 partialSites).adjoint = circuitMoment 2 3 partialSites :=
  ⟨by decide, by decide,
    circuitMoment_comp_perm_of_disjoint 2 partialSites partialDisjoint Fin.revPerm,
    circuitMoment_adjoint_of_disjoint 2 partialSites partialDisjoint⟩

private def wrapSites : (Fin 2 ↪ Fin 4) := Function.Embedding.embFinTwo (a := 3) (b := 0) (by decide)

-- The wrapping gate takes site 3 as its first input and site 0 as its second.
theorem wrapLocalRead (x : Fin (2 ^ 4)) :
    localRead 2 wrapSites x =
      finFunctionFinEquiv ![registerEquiv 2 4 x 3, registerEquiv 2 4 x 0] := by
  simp [wrapSites]

-- A changed site outside that wrapping block forces a zero matrix entry.
theorem wrapOutsideEntry (U : Matrix.unitaryGroup (Fin (2 ^ 2)) ℂ) (x y : Fin (2 ^ 4))
    (h : registerEquiv 2 4 x 1 ≠ registerEquiv 2 4 y 1) :
    placeUnitary 2 wrapSites U x y = 0 := by
  have hout : (1 : Fin 4) ∉ Set.range wrapSites := by
    change ¬ ∃ a, wrapSites a = 1
    decide
  exact placeUnitary_apply_eq_zero 2 wrapSites U x y 1 hout h

-- Three layers on two sites retain three distinct gate occurrences.
theorem threeLayerOccurrences : List.ofFn (fun i => (brickworkSchedule 1 3 i 0, brickworkSchedule 1 3 i 1)) =
    [(0, 1), (1, 0), (0, 1)] := by decide

-- Flattening preserves the layer chronology and the oriented boundary gate.
theorem fourSiteChronology : List.ofFn (fun i => (brickworkSchedule 2 2 i 0, brickworkSchedule 2 2 i 1)) =
    [(0, 1), (2, 3), (1, 2), (3, 0)] := by decide

-- Site 0 is the least significant digit in the public register encoding.
theorem registerDigitOrder :
    finFunctionFinEquiv (![1, 0] : Fin 2 → Fin 2) = 1 ∧
      finFunctionFinEquiv (![0, 1] : Fin 2 → Fin 2) = 2 := by decide

-- General circuits accept arbitrary input operators through vectorization.
theorem circuitArbitraryInput {s n length : ℕ} (q k : ℕ) (sites : Fin length → (Fin s ↪ Fin n))
    (X : Module.End ℂ (TensV (q ^ n) k)) :
    circuitMoment q k sites (endVec X) =
      ∫ samples, endVec (actOn X (circuitUnitary q sites samples))
        ∂Measure.pi (fun _ : Fin length => haarProb (q ^ s)) :=
  circuitMoment_endVec q k sites X

-- The same ensemble formula is available directly for ordinary matrix entries.
theorem circuitMatrixEntries {s n length : ℕ} (q k : ℕ) (sites : Fin length → (Fin s ↪ Fin n))
    (X : Module.End ℂ (TensV (q ^ n) k)) (i j : Fin k → Fin (q ^ n)) :
    toEndMatrix (q ^ n) k (operatorMap (circuitMoment q k sites) X) i j =
      ∫ samples, toEndMatrix (q ^ n) k (actOn X (circuitUnitary q sites samples)) i j
        ∂Measure.pi (fun _ : Fin length => haarProb (q ^ s)) :=
  circuitChannel_entry q k sites X i j

-- Four qubits, two copies, and three literal matching layers use six fresh gates.
theorem brickworkMatrixEntries (X : Module.End ℂ (TensV (2 ^ (2 * 2)) 2))
    (i j : Fin 2 → Fin (2 ^ (2 * 2))) :
    toEndMatrix (2 ^ (2 * 2)) 2 (operatorMap (brickworkMoment 2 2 2 3) X) i j =
      ∫ samples : Fin (3 * 2) → Matrix.unitaryGroup (Fin (2 ^ 2)) ℂ,
        toEndMatrix (2 ^ (2 * 2)) 2 (actOn X (brickworkUnitary 2 2 3 samples)) i j
        ∂Measure.pi (fun _ : Fin (3 * 2) => haarProb (2 ^ 2)) :=
  brickworkChannel_entry 2 2 2 3 X i j

-- Zero copies are permitted; the public sample type needs no length casts.
theorem zeroCopyEnsemble :
    (∫ samples : Fin 6 → Matrix.unitaryGroup (Fin 4) ℂ,
      vecActOn (k := 0) (brickworkUnitary 2 2 3 samples)
      ∂Measure.pi (fun _ : Fin 6 => haarProb 4)) = brickworkMoment 2 0 2 3 :=
  integral_brickworkUnitary 2 0 2 3

theorem emptyBrickwork (q m : ℕ) : brickworkMoment q 0 m 0 = 1 := by simp

-- Three independent two-qubit gates depolarize all six qubits at one copy.
theorem oneCopyMatching :
    circuitMoment 2 1 (oddEdge 3) = (1 / 64 : ℂ) •
      InnerProductSpace.rankOne ℂ (endVec (1 : Module.End ℂ (TensV 64 1))) (endVec 1) := by
  rw [circuitMoment_oddEdge 2 3 (by decide), Fintype.sum_unique, Fintype.sum_unique]
  have hinv : (weingartenGram 4 1)⁻¹ (default : Equiv.Perm (Fin 1)) default = (1 / 4 : ℂ) := by
    rw [Matrix.inv_def, Matrix.det_unique, Matrix.adjugate_subsingleton, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, Ring.inverse_eq_inv', weingartenGram_eq_natCast,
      weingartenGramNat_diag, pow_one]
    norm_num
  have hone : (fun i => (default : Fin 3 → Equiv.Perm (Fin 1)) (oddGate 3 i)) = fun _ => 1 :=
    funext fun i => Subsingleton.elim _ _
  rw [hone, sitePerm_one]
  simp only [show 2 ^ 2 = 4 by decide, Pi.default_apply, hinv,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

-- A uniform permutation of each qubit agrees with the core permutation of the copies.
theorem regPermUniform (σ : Equiv.Perm (Fin 4)) :
    MagicMonotone.regPerm (fun _ => σ) = permOp 16 σ :=
  sitePerm_const (q := 2) (n := 4) σ

-- Each sample acts on its stated ordered pair, in the register's actual bit coordinates.
theorem layerUnitaryAEntries
    (p : Matrix.unitaryGroup (Fin 4) ℂ × Matrix.unitaryGroup (Fin 4) ℂ) (x y : Fin 16) :
    MagicMonotone.layerUnitaryA p x y =
      p.1 (finFunctionFinEquiv ![registerEquiv 2 4 x 0, registerEquiv 2 4 x 1])
        (finFunctionFinEquiv ![registerEquiv 2 4 y 0, registerEquiv 2 4 y 1]) *
      p.2 (finFunctionFinEquiv ![registerEquiv 2 4 x 2, registerEquiv 2 4 x 3])
        (finFunctionFinEquiv ![registerEquiv 2 4 y 2, registerEquiv 2 4 y 3]) := by
  have h := circuitUnitary_apply_of_disjoint 2 (oddEdge 2) (fun _ _ h => oddEdge_disjoint h)
    ![p.1, p.2] x y
  rw [if_pos (fun i hi => absurd (oddEdge_covers i).choose_spec (hi _)), mul_one,
    Fin.prod_univ_two] at h
  have hread (z : Fin 16) :
      localRead 2 (oddEdge 2 0) z =
        finFunctionFinEquiv ![registerEquiv 2 4 z 0, registerEquiv 2 4 z 1] ∧
      localRead 2 (oddEdge 2 1) z =
        finFunctionFinEquiv ![registerEquiv 2 4 z 2, registerEquiv 2 4 z 3] := by
    constructor <;> apply congrArg finFunctionFinEquiv <;> funext a <;> fin_cases a <;> rfl
  simpa only [(hread x).1, (hread x).2, (hread y).1, (hread y).2] using h

-- The second sample reads the periodic pair as `(3,0)`, preserving its input order.
theorem layerUnitaryBEntries
    (p : Matrix.unitaryGroup (Fin 4) ℂ × Matrix.unitaryGroup (Fin 4) ℂ) (x y : Fin 16) :
    MagicMonotone.layerUnitaryB p x y =
      p.1 (finFunctionFinEquiv ![registerEquiv 2 4 x 1, registerEquiv 2 4 x 2])
        (finFunctionFinEquiv ![registerEquiv 2 4 y 1, registerEquiv 2 4 y 2]) *
      p.2 (finFunctionFinEquiv ![registerEquiv 2 4 x 3, registerEquiv 2 4 x 0])
        (finFunctionFinEquiv ![registerEquiv 2 4 y 3, registerEquiv 2 4 y 0]) := by
  have h := circuitUnitary_apply_of_disjoint 2 (evenEdge 2) (fun _ _ h => evenEdge_disjoint h)
    ![p.1, p.2] x y
  rw [if_pos (fun i hi => absurd (evenEdge_covers i).choose_spec (hi _)), mul_one,
    Fin.prod_univ_two] at h
  have hread (z : Fin 16) :
      localRead 2 (evenEdge 2 0) z =
        finFunctionFinEquiv ![registerEquiv 2 4 z 1, registerEquiv 2 4 z 2] ∧
      localRead 2 (evenEdge 2 1) z =
        finFunctionFinEquiv ![registerEquiv 2 4 z 3, registerEquiv 2 4 z 0] := by
    constructor <;> apply congrArg finFunctionFinEquiv <;> funext a <;> fin_cases a <;> rfl
  simpa only [(hread x).1, (hread x).2, (hread y).1, (hread y).2] using h

end LeanHaarTest

/-- info: 'SchurWeyl.Circuits.integral_vecActOn_placed_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SchurWeyl.Circuits.integral_vecActOn_placed_schedule

/-- info: 'SchurWeyl.Circuits.placeUnitary_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SchurWeyl.Circuits.placeUnitary_apply

/-- info: 'SchurWeyl.Circuits.haarMoment_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SchurWeyl.Circuits.haarMoment_mul_self

/-- info: 'SchurWeyl.Circuits.gateMoment_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SchurWeyl.Circuits.gateMoment_adjoint

/-- info: 'SchurWeyl.Circuits.integral_brickworkUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SchurWeyl.Circuits.integral_brickworkUnitary

/-- info: 'SchurWeyl.Circuits.brickworkChannel_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SchurWeyl.Circuits.brickworkChannel_entry

/-- info: 'MagicMonotone.twoLayerMoment_eq_adjoint_brickworkMoment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MagicMonotone.twoLayerMoment_eq_adjoint_brickworkMoment
