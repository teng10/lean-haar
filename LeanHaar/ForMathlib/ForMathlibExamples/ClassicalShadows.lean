import LeanHaar.ForMathlib.Defs
import LeanHaar.ForMathlib.ForMathlibExamples.k2Moment
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Classical shadows

This file formalizes the algebraic content of Observations 58 and 59 in
`classical_shadows.tex`. The probability space is represented by a finite weighted family
of snapshots. This separates the classical-shadow argument from the particular ensemble
used to produce the snapshots; Haar integration supplies the relevant moment identities.

The statements are over an arbitrary field and finite free module whenever no specifically
complex or analytic input is required.
-/

noncomputable section

namespace ClassicalShadows

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Fintype ι] [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V]

/-- A finite weighted family of classical snapshots. Positivity and normalization of the
weights are irrelevant to the algebraic moment identities, so they are not imposed here. -/
structure SnapshotEnsemble where
  weight : ι → 𝕜
  snapshot : ι → Module.End 𝕜 V

namespace SnapshotEnsemble

variable (E : SnapshotEnsemble (𝕜 := 𝕜) (V := V) (ι := ι))

/-- Born weight of an outcome, including the prior weight of that outcome. -/
def outcomeWeight (ρ : Module.End 𝕜 V) (x : ι) : 𝕜 :=
  E.weight x * LinearMap.trace 𝕜 V (ρ ∘ₗ E.snapshot x)

/-- The measurement channel associated to a finite snapshot ensemble. -/
def measurementChannel : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V where
  toFun ρ := ∑ x, E.outcomeWeight ρ x • E.snapshot x
  map_add' ρ σ := by
    simp only [outcomeWeight, LinearMap.add_comp, map_add, mul_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' c ρ := by
    simp only [outcomeWeight, LinearMap.smul_comp, map_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [smul_smul, RingHom.id_apply]
    congr 1
    simp only [smul_eq_mul]
    ring

omit [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp]
theorem measurementChannel_apply (ρ : Module.End 𝕜 V) :
    E.measurementChannel ρ = ∑ x, E.outcomeWeight ρ x • E.snapshot x := rfl

/-- The scalar contraction of the third snapshot moment against three operators. -/
def thirdMoment (A B C : Module.End 𝕜 V) : 𝕜 :=
  ∑ x, E.weight x * LinearMap.trace 𝕜 V (A ∘ₗ E.snapshot x) *
    LinearMap.trace 𝕜 V (B ∘ₗ E.snapshot x) *
    LinearMap.trace 𝕜 V (C ∘ₗ E.snapshot x)

/-- The classical-shadow state estimator associated to an invertible measurement channel. -/
def stateEstimator (hM : Function.Bijective E.measurementChannel) (x : ι) : Module.End 𝕜 V :=
  (LinearEquiv.ofBijective E.measurementChannel hM).symm (E.snapshot x)

omit [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- The classical-shadow estimator is unbiased. -/
theorem mean_estimator (hM : Function.Bijective E.measurementChannel) (ρ : Module.End 𝕜 V) :
    ∑ x, E.outcomeWeight ρ x • E.stateEstimator hM x = ρ := by
  let e := LinearEquiv.ofBijective E.measurementChannel hM
  calc
    ∑ x, E.outcomeWeight ρ x • E.stateEstimator hM x =
        e.symm (∑ x, E.outcomeWeight ρ x • E.snapshot x) := by
          simp only [map_sum, map_smul, stateEstimator, e]
    _ = e.symm (E.measurementChannel ρ) := by rw [measurementChannel_apply]
    _ = ρ := e.symm_apply_apply ρ

/-- Observable evaluated on a classical-shadow state estimator. -/
def observableEstimator (hM : Function.Bijective E.measurementChannel)
    (O : Module.End 𝕜 V) (x : ι) : 𝕜 :=
  LinearMap.trace 𝕜 V (O ∘ₗ E.stateEstimator hM x)

omit [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- Observation 58: the second moment of the scalar estimator is a contraction of the
third snapshot moment. The displayed adjointness assumption is exactly the trace
self-adjointness of the inverse measurement channel used in the paper. -/
theorem estimator_secondMoment (hM : Function.Bijective E.measurementChannel)
    (hself : ∀ A B : Module.End 𝕜 V,
      LinearMap.trace 𝕜 V
          (A ∘ₗ (LinearEquiv.ofBijective E.measurementChannel hM).symm B) =
        LinearMap.trace 𝕜 V
          ((LinearEquiv.ofBijective E.measurementChannel hM).symm A ∘ₗ B))
    (ρ O : Module.End 𝕜 V) :
    ∑ x, E.outcomeWeight ρ x * (E.observableEstimator hM O x) ^ 2 =
      E.thirdMoment ρ
        ((LinearEquiv.ofBijective E.measurementChannel hM).symm O)
        ((LinearEquiv.ofBijective E.measurementChannel hM).symm O) := by
  simp only [outcomeWeight, observableEstimator, stateEstimator, thirdMoment]
  apply Finset.sum_congr rfl
  intro x _
  rw [hself O (E.snapshot x)]
  ring

end SnapshotEnsemble

section Isotropic

variable (δ : 𝕜)

/-- The isotropic measurement channel `X ↦ (Tr(X) I + X)/(δ+1)`. -/
def depolarizingChannel : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V :=
  (δ + 1)⁻¹ • ((LinearMap.trace 𝕜 V).smulRight LinearMap.id) +
    (δ + 1)⁻¹ • LinearMap.id

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp]
theorem depolarizingChannel_apply (X : Module.End 𝕜 V) :
    depolarizingChannel (V := V) δ X =
      (δ + 1)⁻¹ • (LinearMap.trace 𝕜 V X • LinearMap.id + X) := by
  simp only [depolarizingChannel, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.id_apply, smul_add]

/-- Candidate inverse to the isotropic measurement channel. -/
def depolarizingChannelInv : Module.End 𝕜 V →ₗ[𝕜] Module.End 𝕜 V :=
  (δ + 1) • LinearMap.id - (LinearMap.trace 𝕜 V).smulRight LinearMap.id

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp]
theorem depolarizingChannelInv_apply (X : Module.End 𝕜 V) :
    depolarizingChannelInv (V := V) δ X =
      (δ + 1) • X - LinearMap.trace 𝕜 V X • LinearMap.id := by
  rfl

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- Observation 59: `X ↦ (δ+1)X-Tr(X)I` is a left inverse of the isotropic channel.
The only dimension-dependent input is `Tr(I)=δ`. -/
theorem depolarizingChannelInv_comp (hδ : LinearMap.trace 𝕜 V LinearMap.id = δ)
    (hδ1 : δ + 1 ≠ 0) :
    depolarizingChannelInv (V := V) δ ∘ₗ depolarizingChannel (V := V) δ = LinearMap.id := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, depolarizingChannel_apply, depolarizingChannelInv_apply,
    map_smul, map_add, hδ, LinearMap.id_apply]
  have hinv : (δ + 1)⁻¹ * (δ + 1) = 1 := inv_mul_cancel₀ hδ1
  have hinv' : (δ + 1) * (δ + 1)⁻¹ = 1 := mul_inv_cancel₀ hδ1
  have hcoeff : δ * (1 + δ)⁻¹ + (1 + δ)⁻¹ = 1 := by
    calc
      δ * (1 + δ)⁻¹ + (1 + δ)⁻¹ = (δ + 1) * (δ + 1)⁻¹ := by ring
      _ = 1 := hinv'
  match_scalars
  all_goals simp only [mul_one, hinv]
  all_goals field_simp [hδ1]; ring

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- The candidate is also a right inverse. -/
theorem depolarizingChannel_comp_inv (hδ : LinearMap.trace 𝕜 V LinearMap.id = δ)
    (hδ1 : δ + 1 ≠ 0) :
    depolarizingChannel (V := V) δ ∘ₗ depolarizingChannelInv (V := V) δ = LinearMap.id := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, depolarizingChannel_apply, depolarizingChannelInv_apply,
    map_sub, map_smul, hδ, LinearMap.id_apply]
  have hinv : (δ + 1)⁻¹ * (δ + 1) = 1 := inv_mul_cancel₀ hδ1
  have hinv' : (δ + 1) * (δ + 1)⁻¹ = 1 := mul_inv_cancel₀ hδ1
  have hcoeff : δ * (1 + δ)⁻¹ + (1 + δ)⁻¹ = 1 := by
    calc
      δ * (1 + δ)⁻¹ + (1 + δ)⁻¹ = (δ + 1) * (δ + 1)⁻¹ := by ring
      _ = 1 := hinv'
  match_scalars
  all_goals simp only [mul_one, hinv']
  all_goals field_simp [hδ1]; ring

/-- The simplified Haar measurement channel is invertible, with the inverse stated in
Observation 59. -/
def depolarizingChannelEquiv (hδ : LinearMap.trace 𝕜 V LinearMap.id = δ)
    (hδ1 : δ + 1 ≠ 0) : Module.End 𝕜 V ≃ₗ[𝕜] Module.End 𝕜 V :=
  LinearEquiv.ofLinear (depolarizingChannel (V := V) δ)
    (depolarizingChannelInv (V := V) δ)
    (depolarizingChannel_comp_inv δ hδ hδ1)
    (depolarizingChannelInv_comp δ hδ hδ1)

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp]
theorem depolarizingChannel_inverse (hδ : LinearMap.trace 𝕜 V LinearMap.id = δ)
    (hδ1 : δ + 1 ≠ 0) (X : Module.End 𝕜 V) :
    (depolarizingChannelEquiv (V := V) δ hδ hδ1).symm X =
      (δ + 1) • X - LinearMap.trace 𝕜 V X • LinearMap.id := by
  rfl

end Isotropic

end ClassicalShadows

namespace ClassicalShadows

open SchurWeyl

section UnitarySnapshots

/-- The computational-basis projector `|b⟩⟨b|`. -/
def basisProjector (d : ℕ) (b : Fin d) : Module.End ℂ (Fin d → ℂ) :=
  Matrix.toLin' (Matrix.single b b 1)

/-- The genuine classical snapshot `U† |b⟩⟨b| U`. -/
def unitarySnapshot {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (b : Fin d) :
    Module.End ℂ (Fin d → ℂ) :=
  endOf (star (U : Matrix (Fin d) (Fin d) ℂ)) ∘ₗ basisProjector d b ∘ₗ
    endOf (U : Matrix (Fin d) (Fin d) ℂ)

/-- Taking tensor powers commutes with forming the physical snapshot.  Thus a snapshot is
exactly a conjugation-orbit point, with the inverse unitary as group parameter. -/
theorem diagAction_unitarySnapshot {d k : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (b : Fin d) :
    diagAction d k (unitarySnapshot U b) =
      actOn (diagAction d k (basisProjector d b)) (star U) := by
  unfold unitarySnapshot actOn
  rw [← diagAction_comp, ← diagAction_comp]
  congr 1
  simp

/-- The `k`-fold Haar moment of all computational-basis projectors.  Haar invariance
under `U ↦ U†` identifies this with the average of the tensor powers of
`U† |b⟩⟨b| U`. -/
def unitarySnapshotMoment (d k : ℕ) : Module.End ℂ (TensV d k) :=
  ∑ b : Fin d, momentOp (diagAction d k (basisProjector d b))

@[simp] theorem trace_basisProjector (d : ℕ) (b : Fin d) :
    LinearMap.trace ℂ (Fin d → ℂ) (basisProjector d b) = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin d))]
  simp [basisProjector, Matrix.trace]

@[simp] theorem basisProjector_idempotent (d : ℕ) (b : Fin d) :
    basisProjector d b ∘ₗ basisProjector d b = basisProjector d b := by
  unfold basisProjector
  rw [← Matrix.toLin'_mul]
  congr 1
  ext i j
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single b]
  · simp only [Matrix.single_apply]
    split_ifs <;> aesop
  · intro c _ hcb
    simp [Matrix.single_apply]
    intro h
    exact (hcb h.symm).elim
  · simp

@[simp] theorem trace_diagAction_two_basisProjector (d : ℕ) (b : Fin d) :
    LinearMap.trace ℂ (TensV d 2) (diagAction d 2 (basisProjector d b)) = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d 2)]
  change Matrix.trace (toEndMatrix d 2 (diagAction d 2 (basisProjector d b))) = 1
  simp only [Matrix.trace]
  simp_rw [Matrix.diag_apply, toEndMatrix_diagAction]
  rw [show (LinearMap.toMatrix (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d))) = LinearMap.toMatrix' from rfl]
  unfold basisProjector
  simp_rw [LinearMap.toMatrix'_toLin']
  change (∑ x : Fin 2 → Fin d, ∏ m, Matrix.single b b 1 (x m) (x m)) = 1
  rw [Fintype.sum_eq_single (fun _ => b)]
  · simp
  · intro x hx
    simp only [Fin.prod_univ_two, Matrix.single_apply]
    by_cases h0 : b = x 0
    · by_cases h1 : b = x 1
      · exfalso
        apply hx
        funext i
        fin_cases i
        · exact h0.symm
        · exact h1.symm
      · simp [h1]
    · simp [h0]


@[simp] theorem trace_swap_comp_diagAction_two_basisProjector (d : ℕ) (b : Fin d) :
    LinearMap.trace ℂ (TensV d 2)
      (𝔽 d ∘ₗ diagAction d 2 (basisProjector d b)) = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (tensorBasis d 2)]
  change Matrix.trace (toEndMatrix d 2 (𝔽 d ∘ₗ
    diagAction d 2 (basisProjector d b))) = 1
  rw [toEndMatrix_comp]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [show 𝔽 d = (permAction d (Equiv.swap (0 : Fin 2) 1)).toLinearMap from rfl,
    toEndMatrix_permAction, toEndMatrix_diagAction]
  unfold basisProjector
  rw [show (LinearMap.toMatrix (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d))) =
    LinearMap.toMatrix' from rfl]
  simp_rw [LinearMap.toMatrix'_toLin']
  simp only [ite_mul, one_mul, zero_mul]
  have hinner (x : Fin 2 → Fin d) :
      (∑ x₁ : Fin 2 → Fin d,
        if x = x₁ ∘ Equiv.swap 0 1 then
          ∏ m, Matrix.single b b (1 : ℂ) (x₁ m) (x m) else 0) =
        ∏ m, Matrix.single b b (1 : ℂ) ((x ∘ Equiv.swap 0 1) m) (x m) := by
    have hsum := Fintype.sum_ite_eq (x ∘ Equiv.swap 0 1)
      (fun x₁ : Fin 2 → Fin d => ∏ m, Matrix.single b b (1 : ℂ) (x₁ m) (x m))
    rw [← hsum]
    apply Fintype.sum_congr
    intro x₁
    have hinvol (y : Fin 2 → Fin d) :
        (y ∘ Equiv.swap 0 1) ∘ Equiv.swap 0 1 = y := by
      funext i
      fin_cases i <;> rfl
    by_cases h : x = x₁ ∘ Equiv.swap 0 1
    · have hx₁ : x ∘ Equiv.swap 0 1 = x₁ := by
        rw [h, hinvol]
      rw [if_pos h, if_pos hx₁]
    · have hx₁ : x ∘ Equiv.swap 0 1 ≠ x₁ := by
        intro heq
        apply h
        rw [← heq, hinvol]
      rw [if_neg h, if_neg hx₁]
  change (∑ x, ∑ x₁, if x = x₁ ∘ Equiv.swap 0 1 then ∏ m, Matrix.single b b 1 (x₁ m) (x m) else 0) = 1
  rw [show (∑ x : Fin 2 → Fin d, ∑ x₁ : Fin 2 → Fin d, if x = x₁ ∘ Equiv.swap 0 1 then ∏ m : Fin 2, Matrix.single b b (1 : ℂ) (x₁ m) (x m) else 0) = ∑ x : Fin 2 → Fin d, ∏ m : Fin 2, Matrix.single b b (1 : ℂ) ((x ∘ Equiv.swap 0 1) m) (x m) from Finset.sum_congr rfl fun x _ => hinner x]
  simp only [Fin.prod_univ_two, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Fintype.sum_eq_single (fun _ => b)]
  · simp
  · intro x hx
    by_cases h0 : b = x 0
    · by_cases h1 : b = x 1
      · exfalso
        apply hx
        funext i
        fin_cases i
        · exact h0.symm
        · exact h1.symm
      · simp [h1]
    · simp [h0]

/-- The second-order representation-theoretic structure of genuine unitary snapshots.
It follows from Schur--Weyl duality: the Haar twirl lies in the span of the identity
and swap representations, and its two trace contractions determine both coefficients. -/
theorem unitarySnapshotMoment_two (d : ℕ) [NeZero d] [Fact (2 ≤ d)] :
    unitarySnapshotMoment d 2 =
      ((d : ℂ) + 1)⁻¹ • ((LinearMap.id : Module.End ℂ (TensV d 2)) + 𝔽 d) := by
  unfold unitarySnapshotMoment
  simp_rw [k2_moment]
  simp_rw [show ∀ b, LinearMap.trace ℂ (TensV d 2) (𝔽 d • diagAction d 2 (basisProjector d b)) = 1 from trace_swap_comp_diagAction_two_basisProjector d]
  simp only [smul_eq_mul, trace_diagAction_two_basisProjector]
  rw [Finset.sum_add_distrib]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdne1 : (d : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr <| by
    norm_cast
    exact Nat.ne_of_gt (Fact.out (p := 2 ≤ d))
  have hdp1 : (d : ℂ) + 1 ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_ne_zero]
    omega
  have hd2m1 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [show (d : ℂ) ^ 2 - 1 = ((d : ℂ) - 1) * ((d : ℂ) + 1) by ring]
    exact mul_ne_zero hdne1 hdp1
  have hcoeff : (d : ℂ) * ((1 - (d : ℂ)⁻¹) / ((d : ℂ)^2 - 1)) =
      ((d : ℂ) + 1)⁻¹ := by
    field_simp [hd, hd2m1, hdp1]
    ring
  simp only [mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul, hcoeff, smul_add]

end UnitarySnapshots

end ClassicalShadows

namespace ClassicalShadows

open scoped TensorProduct

section TensorMomentFormulas

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Fintype ι] [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V]

/-- The second tensor moment `∑ₓ wₓ Sₓ ⊗ Sₓ` of a snapshot ensemble. -/
def SnapshotEnsemble.secondTensorMoment
    (E : SnapshotEnsemble (𝕜 := 𝕜) (V := V) (ι := ι)) :
    (Module.End 𝕜 V) ⊗[𝕜] (Module.End 𝕜 V) :=
  ∑ x, E.weight x • (E.snapshot x ⊗ₜ[𝕜] E.snapshot x)

/-- The linear functional `X ↦ Tr(A X)`. -/
def traceMulLeft (A : Module.End 𝕜 V) : Module.End 𝕜 V →ₗ[𝕜] 𝕜 where
  toFun X := LinearMap.trace 𝕜 V (A ∘ₗ X)
  map_add' X Y := by simp only [LinearMap.comp_add, map_add]
  map_smul' c X := by simp only [LinearMap.comp_smul, map_smul, RingHom.id_apply]

/-- Partial trace against `ρ` in the first tensor factor.  On a pure tensor it is
`A ⊗ B ↦ Tr(ρA) B`. -/
def partialTraceFirst (ρ : Module.End 𝕜 V) :
    (Module.End 𝕜 V) ⊗[𝕜] (Module.End 𝕜 V) →ₗ[𝕜] Module.End 𝕜 V :=
  TensorProduct.lift
    { toFun := fun A => (traceMulLeft ρ A) • LinearMap.id
      map_add' := by intros; ext; simp only [map_add, add_smul]
      map_smul' := by intros; ext; simp only [map_smul, smul_eq_mul, smul_smul,
        RingHom.id_apply] }

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp] theorem partialTraceFirst_tmul (ρ A B : Module.End 𝕜 V) :
    partialTraceFirst ρ (A ⊗ₜ[𝕜] B) = LinearMap.trace 𝕜 V (ρ ∘ₗ A) • B := by
  rfl

namespace SnapshotEnsemble

omit [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- Tensor form of the measurement-channel identity:
`M(ρ) = Tr₁ ((ρ ⊗ I) ∑ₓ wₓ Sₓ ⊗ Sₓ)`.  The multiplication by `ρ ⊗ I`
is incorporated into `partialTraceFirst ρ`. -/
theorem measurementChannel_eq_partialTrace_secondTensorMoment
    (E : SnapshotEnsemble (𝕜 := 𝕜) (V := V) (ι := ι)) (ρ : Module.End 𝕜 V) :
    E.measurementChannel ρ = partialTraceFirst ρ E.secondTensorMoment := by
  simp [measurementChannel_apply, outcomeWeight, secondTensorMoment, smul_smul]

end SnapshotEnsemble

/-- The third tensor moment `∑ₓ wₓ Sₓ ⊗ Sₓ ⊗ Sₓ`. -/
def SnapshotEnsemble.thirdTensorMoment
    (E : SnapshotEnsemble (𝕜 := 𝕜) (V := V) (ι := ι)) :
    (Module.End 𝕜 V) ⊗[𝕜] ((Module.End 𝕜 V) ⊗[𝕜] (Module.End 𝕜 V)) :=
  ∑ x, E.weight x •
    (E.snapshot x ⊗ₜ[𝕜] (E.snapshot x ⊗ₜ[𝕜] E.snapshot x))

/-- Trace contraction of a three-fold tensor, characterized on pure tensors by
`Tr(A X) Tr(B Y) Tr(C Z)`. -/
def tripleTraceContract (A B C : Module.End 𝕜 V) :
    (Module.End 𝕜 V) ⊗[𝕜] ((Module.End 𝕜 V) ⊗[𝕜] (Module.End 𝕜 V)) →ₗ[𝕜] 𝕜 :=
  let inner : (Module.End 𝕜 V) ⊗[𝕜] (Module.End 𝕜 V) →ₗ[𝕜] 𝕜 :=
    TensorProduct.lift
      { toFun := fun Y => (traceMulLeft B Y) • traceMulLeft C
        map_add' := by intros; ext; simp only [map_add, add_smul, LinearMap.add_apply]
        map_smul' := by intros; ext; simp only [map_smul, smul_eq_mul, smul_smul,
          LinearMap.smul_apply, RingHom.id_apply] }
  TensorProduct.lift
    { toFun := fun X => (traceMulLeft A X) • inner
      map_add' := by intros; ext; simp only [map_add, add_smul]
      map_smul' := by intros; ext; simp only [map_smul, smul_eq_mul, smul_smul,
        RingHom.id_apply] }

omit [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
@[simp] theorem tripleTraceContract_tmul (A B C X Y Z : Module.End 𝕜 V) :
    tripleTraceContract A B C (X ⊗ₜ[𝕜] (Y ⊗ₜ[𝕜] Z)) =
      LinearMap.trace 𝕜 V (A ∘ₗ X) * LinearMap.trace 𝕜 V (B ∘ₗ Y) *
        LinearMap.trace 𝕜 V (C ∘ₗ Z) := by
  simp [tripleTraceContract, traceMulLeft, mul_assoc]

/-- The variance of the observable shadow estimator under the Born-weighted outcome
law, written as its second moment minus the square of its true mean. -/
def SnapshotEnsemble.observableEstimatorVariance
    (E : SnapshotEnsemble (𝕜 := 𝕜) (V := V) (ι := ι))
    (hM : Function.Bijective E.measurementChannel) (ρ O : Module.End 𝕜 V) : 𝕜 :=
  (∑ x, E.outcomeWeight ρ x * (E.observableEstimator hM O x) ^ 2) -
    (LinearMap.trace 𝕜 V (O ∘ₗ ρ)) ^ 2

namespace SnapshotEnsemble

omit [DecidableEq ι] [Module.Free 𝕜 V] [Module.Finite 𝕜 V] in
/-- Tensor form of the classical-shadow variance identity. -/
theorem observableEstimatorVariance_eq_thirdTensorMoment
    (E : SnapshotEnsemble (𝕜 := 𝕜) (V := V) (ι := ι))
    (hM : Function.Bijective E.measurementChannel)
    (hself : ∀ A B : Module.End 𝕜 V,
      LinearMap.trace 𝕜 V
          (A ∘ₗ (LinearEquiv.ofBijective E.measurementChannel hM).symm B) =
        LinearMap.trace 𝕜 V
          ((LinearEquiv.ofBijective E.measurementChannel hM).symm A ∘ₗ B))
    (ρ O : Module.End 𝕜 V) :
    E.observableEstimatorVariance hM ρ O =
      tripleTraceContract ρ
        ((LinearEquiv.ofBijective E.measurementChannel hM).symm O)
        ((LinearEquiv.ofBijective E.measurementChannel hM).symm O)
        E.thirdTensorMoment - (LinearMap.trace 𝕜 V (O ∘ₗ ρ)) ^ 2 := by
  rw [SnapshotEnsemble.observableEstimatorVariance,
    E.estimator_secondMoment hM hself ρ O]
  congr 1
  simp only [SnapshotEnsemble.thirdMoment, SnapshotEnsemble.thirdTensorMoment,
    map_sum, map_smul, tripleTraceContract_tmul]
  apply Finset.sum_congr rfl
  intro x _
  simp only [smul_eq_mul]
  ring

end SnapshotEnsemble

end TensorMomentFormulas

end ClassicalShadows
