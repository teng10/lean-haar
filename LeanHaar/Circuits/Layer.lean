/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanHaar.Circuits.Circuit
import LeanHaar.Circuits.SitePermutation
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Layers of gates on disjoint supports

Disjoint gates commute, and their independent Haar moment is unchanged by reordering.
These laws also apply to partial layers. For gates covering the register, the moment's
entries factor over gates; when `k ≤ q ^ s`, its Weingarten expansion uses one copy
permutation per gate. The coverage and stable-range hypotheses appear only on evaluation.
-/

noncomputable section
open MeasureTheory SchurWeyl InnerProductSpace
open scoped Matrix
namespace SchurWeyl.Circuits

variable {s n : ℕ}

/-- Basis indices that agree on a block have the same local index. -/
private theorem localRead_congr (q : ℕ) (sites : Fin s ↪ Fin n) {x y : Fin (q ^ n)}
    (h : ∀ a, registerEquiv q n x (sites a) = registerEquiv q n y (sites a)) :
    localRead q sites x = localRead q sites y := by
  unfold localRead
  exact congrArg _ (funext h)

/-- **Entries of a layer.** Gates on pairwise disjoint supports act independently on their
blocks and preserve every uncovered site. -/
theorem circuitUnitary_apply_of_disjoint {m : ℕ} (q : ℕ) (sites : Fin m → (Fin s ↪ Fin n))
    (hdisj : Pairwise fun g h => Disjoint (Set.range (sites g)) (Set.range (sites h)))
    (U : Fin m → Matrix.unitaryGroup (Fin (q ^ s)) ℂ) (x y : Fin (q ^ n)) :
    circuitUnitary q sites U x y =
      (∏ g, U g (localRead q (sites g) x) (localRead q (sites g) y)) *
        if (∀ i, (∀ g, i ∉ Set.range (sites g)) →
            registerEquiv q n x i = registerEquiv q n y i) then 1 else 0 := by
  classical
  induction m generalizing x y with
  | zero =>
    have h1 : circuitUnitary q sites U = 1 := by
      unfold circuitUnitary
      exact scheduleProduct_zero _
    rw [h1, Matrix.UnitaryGroup.one_apply, Matrix.one_apply]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    refine if_congr ⟨?_, fun h => ?_⟩ rfl rfl
    · rintro rfl i _
      rfl
    · exact (registerEquiv q n).injective (funext fun i => h i (fun g => g.elim0))
  | succ m ih =>
    have hdisj' : Pairwise fun g h : Fin m =>
        Disjoint (Set.range (sites g.succ)) (Set.range (sites h.succ)) :=
      fun g h hgh => hdisj ((Fin.succ_injective m).ne hgh)
    have hstep : circuitUnitary q sites U =
        circuitUnitary q (fun g => sites g.succ) (fun g => U g.succ) *
          placeUnitary q (sites 0) (U 0) := by
      unfold circuitUnitary
      rw [scheduleProduct_succ]
    -- The only intermediate index that contributes: `x` on the first block, `y` elsewhere.
    let z₀ : Fin (q ^ n) := (registerEquiv q n).symm
      (fun i => if i ∈ Set.range (sites 0) then registerEquiv q n x i else registerEquiv q n y i)
    have hz₀ : ∀ i, registerEquiv q n z₀ i =
        if i ∈ Set.range (sites 0) then registerEquiv q n x i else registerEquiv q n y i := by
      intro i
      simp [z₀]
    have hoff : ∀ (g : Fin m) {i : Fin n}, i ∈ Set.range (sites g.succ) →
        i ∉ Set.range (sites 0) :=
      fun g i hi => Set.disjoint_left.mp (hdisj (Fin.succ_ne_zero g)) hi
    rw [hstep, Matrix.UnitaryGroup.mul_apply, Matrix.mul_apply, Finset.sum_eq_single z₀]
    · have hread0 : localRead q (sites 0) z₀ = localRead q (sites 0) x :=
        localRead_congr q (sites 0) fun a => by rw [hz₀, if_pos ⟨a, rfl⟩]
      have hreadS : ∀ g : Fin m, localRead q (sites g.succ) z₀ = localRead q (sites g.succ) y :=
        fun g => localRead_congr q _ fun a => by rw [hz₀, if_neg (hoff g ⟨a, rfl⟩)]
      have hP : ∀ i, i ∉ Set.range (sites 0) →
          registerEquiv q n z₀ i = registerEquiv q n y i := by
        intro i hi
        rw [hz₀, if_neg hi]
      have hT : (∀ i, (∀ g : Fin m, i ∉ Set.range (sites g.succ)) →
            registerEquiv q n x i = registerEquiv q n z₀ i) ↔
          (∀ i, (∀ g : Fin (m + 1), i ∉ Set.range (sites g)) →
            registerEquiv q n x i = registerEquiv q n y i) := by
        constructor
        · intro h i hi
          have := h i (fun g => hi g.succ)
          rwa [hz₀, if_neg (hi 0)] at this
        · intro h i hi
          rw [hz₀]
          split_ifs with h0
          · rfl
          · exact h i (fun g => Fin.cases h0 hi g)
      rw [ih (fun g => sites g.succ) hdisj' (fun g => U g.succ) x z₀, placeUnitary_apply,
        hread0, if_pos hP, mul_one, Fin.prod_univ_succ]
      simp only [hreadS, hT]
      ring
    · intro z _ hz
      rw [ih (fun g => sites g.succ) hdisj' (fun g => U g.succ) x z, placeUnitary_apply]
      by_cases hP : ∀ i, i ∉ Set.range (sites 0) →
          registerEquiv q n z i = registerEquiv q n y i
      · by_cases hT : ∀ i, (∀ g : Fin m, i ∉ Set.range (sites g.succ)) →
            registerEquiv q n x i = registerEquiv q n z i
        · exfalso
          apply hz
          apply (registerEquiv q n).injective
          funext i
          rw [hz₀]
          split_ifs with h0
          · exact (hT i (fun g hi => hoff g hi h0)).symm
          · exact hP i h0
        · rw [if_neg hT, mul_zero, zero_mul]
      · rw [if_neg hP, mul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- **Order independence inside a layer.** Relabelling the gate occurrences of a layer
with disjoint supports does not change the sampled unitary. -/
theorem circuitUnitary_comp_perm_of_disjoint {m : ℕ} (q : ℕ) (sites : Fin m → (Fin s ↪ Fin n))
    (hdisj : Pairwise fun g h => Disjoint (Set.range (sites g)) (Set.range (sites h)))
    (U : Fin m → Matrix.unitaryGroup (Fin (q ^ s)) ℂ) (e : Equiv.Perm (Fin m)) :
    circuitUnitary q (fun g => sites (e g)) (fun g => U (e g)) = circuitUnitary q sites U := by
  have hdisj' : Pairwise fun g h => Disjoint (Set.range (sites (e g))) (Set.range (sites (e h))) :=
    fun g h hgh => hdisj (e.injective.ne hgh)
  apply Subtype.ext
  ext x y
  change circuitUnitary q (fun g => sites (e g)) (fun g => U (e g)) x y =
    circuitUnitary q sites U x y
  rw [circuitUnitary_apply_of_disjoint q _ hdisj', circuitUnitary_apply_of_disjoint q _ hdisj,
    Equiv.prod_comp e (fun g => U g (localRead q (sites g) x) (localRead q (sites g) y))]
  congr 1
  refine if_congr (forall_congr' fun i => imp_congr_left ?_) rfl rfl
  exact ⟨fun h g => by simpa using h (e.symm g), fun h g => h (e g)⟩

/-- **Gates on disjoint supports commute.** -/
theorem placeUnitary_commute_of_disjoint (q : ℕ) (sites₁ sites₂ : Fin s ↪ Fin n)
    (h : Disjoint (Set.range sites₁) (Set.range sites₂))
    (U V : Matrix.unitaryGroup (Fin (q ^ s)) ℂ) :
    Commute (placeUnitary q sites₁ U) (placeUnitary q sites₂ V) := by
  have hdisj : Pairwise fun g h : Fin 2 =>
      Disjoint (Set.range (![sites₁, sites₂] g)) (Set.range (![sites₁, sites₂] h)) := by
    intro g h' hgh
    fin_cases g <;> fin_cases h' <;> first | exact absurd rfl hgh | exact h | exact h.symm
  have key := circuitUnitary_comp_perm_of_disjoint q ![sites₁, sites₂] hdisj ![U, V]
    (Equiv.swap 0 1)
  simp only [circuitUnitary, scheduleProduct_two] at key
  simpa [Commute, SemiconjBy] using key

/-- Reordering independent Haar gates on disjoint supports does not change the moment. -/
theorem circuitMoment_comp_perm_of_disjoint {m k : ℕ} (q : ℕ) (sites : Fin m → (Fin s ↪ Fin n))
    (hdisj : Pairwise fun g h => Disjoint (Set.range (sites g)) (Set.range (sites h)))
    (e : Equiv.Perm (Fin m)) :
    circuitMoment q k (fun g => sites (e g)) = circuitMoment q k sites := by
  rw [← integral_circuitUnitary, ← integral_circuitUnitary]
  have hmp := (measurePreserving_piCongrLeft
    (fun _ : Fin m => haarProb (q ^ s)) e.symm).integral_comp'
      (fun U => vecActOn (k := k) (circuitUnitary q (fun g => sites (e g)) U))
  calc
    _ = ∫ U, vecActOn (k := k)
        (circuitUnitary q (fun g => sites (e g)) (fun g => U (e g)))
        ∂Measure.pi (fun _ : Fin m => haarProb (q ^ s)) := by
      exact hmp.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun U =>
        congrArg (fun samples => vecActOn (k := k)
          (circuitUnitary q (fun g => sites (e g)) samples)) (by
            funext g
            simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply])))
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun U =>
      congrArg (vecActOn (k := k)) (circuitUnitary_comp_perm_of_disjoint q sites hdisj U e))

/-- A layer of Haar gates on disjoint supports is self-adjoint, including partial layers. -/
theorem circuitMoment_adjoint_of_disjoint {m k : ℕ} (q : ℕ) (sites : Fin m → (Fin s ↪ Fin n))
    (hdisj : Pairwise fun g h => Disjoint (Set.range (sites g)) (Set.range (sites h))) :
    (circuitMoment q k sites).adjoint = circuitMoment q k sites := by
  rw [circuitMoment_adjoint]
  exact circuitMoment_comp_perm_of_disjoint q sites hdisj Fin.revPerm

variable {m k : ℕ}

/-! ### Entries of moment operators -/

/-- A moment operator is determined by its matrix entries. -/
private theorem momentOperator_ext {d k : ℕ} {S T : MomentOperator d k}
    (h : ∀ p r, S (EuclideanSpace.single r 1) p = T (EuclideanSpace.single r 1) p) : S = T := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun _ ℂ).toBasis.ext fun r => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  ext p
  exact h p r

/-- Entries of vectorized conjugation. -/
private theorem vecActOn_single_apply {d k : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (p r : (Fin k → Fin d) × (Fin k → Fin d)) :
    vecActOn (k := k) U (EuclideanSpace.single r 1) p =
      (∏ c, U (p.1 c) (r.1 c)) * star (∏ c, U (p.2 c) (r.2 c)) := by
  simp [vecActOn, Matrix.toLpLin_apply]

/-- Entries of a rank-one operator. -/
private theorem rankOne_single_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : EuclideanSpace ℂ ι) (p r : ι) :
    rankOne ℂ x y (EuclideanSpace.single r 1) p = x p * star (y r) := by
  rw [rankOne_apply, EuclideanSpace.inner_single_right]
  simp [mul_comm]

/-! ### A layer that covers the register -/

/-- The row or column index of gate `g`, read through its ordered block. -/
private def blockIndex (q : ℕ) (sites : Fin m → (Fin s ↪ Fin n)) (g : Fin m)
    (p : (Fin k → Fin (q ^ n)) × (Fin k → Fin (q ^ n))) :
    (Fin k → Fin (q ^ s)) × (Fin k → Fin (q ^ s)) :=
  (fun c => localRead q (sites g) (p.1 c), fun c => localRead q (sites g) (p.2 c))

private theorem circuitUnitary_apply_of_cover (q : ℕ) (sites : Fin m → (Fin s ↪ Fin n))
    (hdisj : Pairwise fun g h => Disjoint (Set.range (sites g)) (Set.range (sites h)))
    (hcover : ∀ i, ∃ g, i ∈ Set.range (sites g))
    (U : Fin m → Matrix.unitaryGroup (Fin (q ^ s)) ℂ) (x y : Fin (q ^ n)) :
    circuitUnitary q sites U x y =
      ∏ g, U g (localRead q (sites g) x) (localRead q (sites g) y) := by
  rw [circuitUnitary_apply_of_disjoint q sites hdisj, if_pos, mul_one]
  intro i hi
  obtain ⟨g, hg⟩ := hcover i
  exact absurd hg (hi g)

/-- The vectorized action of a covering layer factorizes over its gates, entry by entry. -/
private theorem vecActOn_circuitUnitary_single_apply (q : ℕ) (sites : Fin m → (Fin s ↪ Fin n))
    (hdisj : Pairwise fun g h => Disjoint (Set.range (sites g)) (Set.range (sites h)))
    (hcover : ∀ i, ∃ g, i ∈ Set.range (sites g))
    (U : Fin m → Matrix.unitaryGroup (Fin (q ^ s)) ℂ)
    (p r : (Fin k → Fin (q ^ n)) × (Fin k → Fin (q ^ n))) :
    vecActOn (k := k) (circuitUnitary q sites U) (EuclideanSpace.single r 1) p =
      ∏ g, vecActOn (k := k) (U g) (EuclideanSpace.single (blockIndex q sites g r) 1)
        (blockIndex q sites g p) := by
  simp only [vecActOn_single_apply, circuitUnitary_apply_of_cover q sites hdisj hcover,
    blockIndex, Finset.prod_mul_distrib, ← star_prod]
  rw [Finset.prod_comm, Finset.prod_comm (f := fun c g =>
    (U g) (localRead q (sites g) (p.2 c)) (localRead q (sites g) (r.2 c)))]

/-- **Entries of a covering layer moment**: a product of single-gate Haar moment entries.
No stable-range hypothesis. -/
theorem circuitMoment_single_apply_of_cover (q : ℕ) (sites : Fin m → (Fin s ↪ Fin n))
    (hdisj : Pairwise fun g h => Disjoint (Set.range (sites g)) (Set.range (sites h)))
    (hcover : ∀ i, ∃ g, i ∈ Set.range (sites g))
    (p r : (Fin k → Fin (q ^ n)) × (Fin k → Fin (q ^ n))) :
    circuitMoment q k sites (EuclideanSpace.single r 1) p =
      ∏ g, haarMoment (q ^ s) k
        (EuclideanSpace.single
          (fun c => localRead q (sites g) (r.1 c), fun c => localRead q (sites g) (r.2 c)) 1)
        (fun c => localRead q (sites g) (p.1 c), fun c => localRead q (sites g) (p.2 c)) := by
  rw [← integral_circuitUnitary,
    ContinuousLinearMap.integral_apply (integrable_circuitAction q k sites),
    eval_integral_piLp (fun i =>
      ((integrable_circuitAction q k sites).apply_continuousLinearMap _).eval_piLp i)]
  simp only [vecActOn_circuitUnitary_single_apply q sites hdisj hcover]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun g (V : Matrix.unitaryGroup (Fin (q ^ s)) ℂ) =>
      vecActOn (k := k) V (EuclideanSpace.single (blockIndex q sites g r) 1)
        (blockIndex q sites g p))]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [haarMoment, ContinuousLinearMap.integral_apply integrable_vecActOn,
    eval_integral_piLp (fun i => (integrable_vecActOn.apply_continuousLinearMap _).eval_piLp i)]
  rfl

/-! ### The stable range: a Weingarten sum over site-permutation kets -/

private theorem endVec_permOp_apply {d : ℕ} (σ : Equiv.Perm (Fin k))
    (p : (Fin k → Fin d) × (Fin k → Fin d)) :
    endVec (permOp d σ) p = if p.1 = p.2 ∘ σ.symm then 1 else 0 := by
  rw [endVec_apply]
  simp only [permOp, toEndMatrix_permAction]

/-- If every site belongs to the gate `gateOf` assigns it, the tensor product of the
gates' permutation kets is the site-permutation ket. -/
private theorem endVec_sitePerm_gateOf (q : ℕ) (sites : Fin m → (Fin s ↪ Fin n)) (gateOf : Fin n → Fin m)
    (hgate : ∀ g a, gateOf (sites g a) = g) (hcover : ∀ i, i ∈ Set.range (sites (gateOf i)))
    (σ : Fin m → Equiv.Perm (Fin k)) (p : (Fin k → Fin (q ^ n)) × (Fin k → Fin (q ^ n))) :
    endVec (sitePerm q (fun i => σ (gateOf i))) p =
      ∏ g, endVec (permOp (q ^ s) (σ g)) (blockIndex q sites g p) := by
  classical
  simp only [endVec_sitePerm_apply, endVec_permOp_apply, blockIndex]
  rw [Fintype.prod_boole]
  have hiff : (∀ j c, registerEquiv q n (p.1 c) j =
        registerEquiv q n (p.2 ((σ (gateOf j)).symm c)) j) ↔
      ∀ g, (fun c => localRead q (sites g) (p.1 c)) =
        (fun c => localRead q (sites g) (p.2 c)) ∘ (σ g).symm := by
    constructor
    · intro h g
      funext c
      exact localRead_congr q (sites g) fun a => by simpa only [hgate] using h (sites g a) c
    · intro h j c
      obtain ⟨a, ha⟩ := hcover j
      have hread := congrFun (h (gateOf j)) c
      have := congrFun (finFunctionFinEquiv.injective hread) a
      simpa only [ha, Function.comp_apply] using this
  by_cases h : ∀ j c, registerEquiv q n (p.1 c) j =
      registerEquiv q n (p.2 ((σ (gateOf j)).symm c)) j
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg fun h' => h (hiff.mpr h')]

/-- **Layer moment in the stable range.** Independent Haar gates on blocks that partition
the register average to a Weingarten sum of rank-one operators on site-permutation kets,
one permutation per gate. -/
theorem circuitMoment_eq_weingarten_sum (q : ℕ) (hk : k ≤ q ^ s)
    (sites : Fin m → (Fin s ↪ Fin n)) (gateOf : Fin n → Fin m)
    (hgate : ∀ g a, gateOf (sites g a) = g) (hcover : ∀ i, i ∈ Set.range (sites (gateOf i))) :
    circuitMoment q k sites =
      ∑ σ : Fin m → Equiv.Perm (Fin k), ∑ π : Fin m → Equiv.Perm (Fin k),
        (∏ g, (weingartenGram (q ^ s) k)⁻¹ (σ g) (π g)) •
          rankOne ℂ (endVec (sitePerm q (fun i => σ (gateOf i))))
            (endVec (sitePerm q (fun i => π (gateOf i)))) := by
  have hdisj : Pairwise fun g h => Disjoint (Set.range (sites g)) (Set.range (sites h)) := by
    intro g h hgh
    rw [Set.disjoint_left]
    rintro i ⟨a, rfl⟩ ⟨b, hb⟩
    exact hgh (by rw [← hgate g a, ← hb, hgate h b])
  have hcover' : ∀ i, ∃ g, i ∈ Set.range (sites g) := fun i => ⟨gateOf i, hcover i⟩
  apply momentOperator_ext
  intro p r
  rw [circuitMoment_single_apply_of_cover q sites hdisj hcover']
  simp only [haarMoment_eq_weingarten_sum hk, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, rankOne_single_apply,
    endVec_sitePerm_gateOf q sites gateOf hgate hcover]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.prod_mul_distrib, star_prod]
  rfl

end SchurWeyl.Circuits
