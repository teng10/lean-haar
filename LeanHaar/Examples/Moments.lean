import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Pi

open Complex
open Matrix
open MeasureTheory
open intervalIntegral

/-- Define the Pauli-Z operator -/
noncomputable def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0],![0, -1]]

/-- Define the parameterized version of the 2x2 unitary matrix U -/
noncomputable def U (ϕ θ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![exp (-I * (↑ϕ + ↑ω) / 2) * ↑(Real.cos (θ / 2)), -exp (I * (↑ϕ - ↑ω) / 2) * ↑(Real.sin (θ / 2))],
    ![exp (-I * (↑ϕ - ↑ω) / 2) * ↑(Real.sin (θ / 2)), exp (I * (↑ϕ + ↑ω) / 2) * ↑(Real.cos (θ / 2))]]

/-- Take the conjugate transpose of U -/
noncomputable def U_dagger (ϕ θ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![exp (I * (↑ϕ + ↑ω) / 2) * ↑(Real.cos (θ / 2)), exp (I * (↑ϕ - ↑ω) / 2) * ↑(Real.sin (θ / 2))],
    ![-exp (-I * (↑ϕ - ↑ω) / 2) * ↑(Real.sin (θ / 2)), exp (-I * (↑ϕ + ↑ω) / 2) * ↑(Real.cos (θ / 2))]]

/-- Trace of Pauli-Z is 0 -/
lemma trace_sigmaZ_eq_zero :
  Matrix.trace sigmaZ = 0 := by
  simp [sigmaZ, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Expected value component for trace of sigmaZ -/
lemma trace_sigmaZ_smul_one :
  (Matrix.trace sigmaZ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  rw [trace_sigmaZ_eq_zero]
  simp

/-- Explicit calculation of the inner matrix multiplication U * sigmaZ * U_dagger -/
lemma U_sigmaZ_U_dagger_eq (ϕ θ ω : ℝ) :
  (U ϕ θ ω) * sigmaZ * (U_dagger ϕ θ ω) =
    ![![↑(Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2),
       exp (-I * ↑ω) * ↑(Real.cos (θ / 2) * Real.sin (θ / 2)) + exp (-I * ↑ω) * ↑(Real.sin (θ / 2) * Real.cos (θ / 2))],
      ![exp (I * ↑ω) * ↑(Real.sin (θ / 2) * Real.cos (θ / 2)) + exp (I * ↑ω) * ↑(Real.cos (θ / 2) * Real.sin (θ / 2)),
       ↑(Real.sin (θ / 2) ^ 2 - Real.cos (θ / 2) ^ 2)]] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [U, sigmaZ, U_dagger, Matrix.mul_apply, Fin.sum_univ_two]
    have h1 : exp (-I * (↑ϕ + ↑ω) / 2) * exp (I * (↑ϕ + ↑ω) / 2) = 1 := by
      rw [← exp_add]
      have : -I * (↑ϕ + ↑ω) / 2 + I * (↑ϕ + ↑ω) / 2 = 0 := by ring
      rw [this, exp_zero]
    have h2 : exp (I * (↑ϕ - ↑ω) / 2) * exp (-I * (↑ϕ - ↑ω) / 2) = 1 := by
      rw [← exp_add]
      have : I * (↑ϕ - ↑ω) / 2 + -I * (↑ϕ - ↑ω) / 2 = 0 := by ring
      rw [this, exp_zero]
    trans (exp (-I * (↑ϕ + ↑ω) / 2) * exp (I * (↑ϕ + ↑ω) / 2)) * (↑(Real.cos (θ / 2)) : ℂ) ^ 2 -
          (exp (I * (↑ϕ - ↑ω) / 2) * exp (-I * (↑ϕ - ↑ω) / 2)) * (↑(Real.sin (θ / 2)) : ℂ) ^ 2
    · push_cast; ring
    · rw [h1, h2]; push_cast; ring
  · simp [U, sigmaZ, U_dagger, Matrix.mul_apply, Fin.sum_univ_two]
    have h3 : exp (-I * (↑ϕ + ↑ω) / 2) * exp (I * (↑ϕ - ↑ω) / 2) = exp (-I * ↑ω) := by
      rw [← exp_add]
      have : -I * (↑ϕ + ↑ω) / 2 + I * (↑ϕ - ↑ω) / 2 = -I * ↑ω := by ring
      rw [this]
    have h4 : exp (I * (↑ϕ - ↑ω) / 2) * exp (-I * (↑ϕ + ↑ω) / 2) = exp (-I * ↑ω) := by
      rw [← exp_add]
      have : I * (↑ϕ - ↑ω) / 2 + -I * (↑ϕ + ↑ω) / 2 = -I * ↑ω := by ring
      rw [this]
    trans (exp (-I * (↑ϕ + ↑ω) / 2) * exp (I * (↑ϕ - ↑ω) / 2)) * ↑(Real.cos (θ / 2)) * ↑(Real.sin (θ / 2)) +
          (exp (I * (↑ϕ - ↑ω) / 2) * exp (-I * (↑ϕ + ↑ω) / 2)) * ↑(Real.sin (θ / 2)) * ↑(Real.cos (θ / 2))
    · push_cast; ring_nf
    · rw [h3, h4]; push_cast; ring
  · simp [U, sigmaZ, U_dagger, Matrix.mul_apply, Fin.sum_univ_two]
    have h5 : exp (-I * (↑ϕ - ↑ω) / 2) * exp (I * (↑ϕ + ↑ω) / 2) = exp (I * ↑ω) := by
      rw [← exp_add]
      have : -I * (↑ϕ - ↑ω) / 2 + I * (↑ϕ + ↑ω) / 2 = I * ↑ω := by ring
      rw [this]
    have h6 : exp (I * (↑ϕ + ↑ω) / 2) * exp (-I * (↑ϕ - ↑ω) / 2) = exp (I * ↑ω) := by
      rw [← exp_add]
      have : I * (↑ϕ + ↑ω) / 2 + -I * (↑ϕ - ↑ω) / 2 = I * ↑ω := by ring
      rw [this]
    trans (exp (-I * (↑ϕ - ↑ω) / 2) * exp (I * (↑ϕ + ↑ω) / 2)) * ↑(Real.sin (θ / 2)) * ↑(Real.cos (θ / 2)) +
          (exp (I * (↑ϕ + ↑ω) / 2) * exp (-I * (↑ϕ - ↑ω) / 2)) * ↑(Real.cos (θ / 2)) * ↑(Real.sin (θ / 2))
    · push_cast; ring_nf
    · rw [h5, h6]; push_cast; ring
  · simp [U, sigmaZ, U_dagger, Matrix.mul_apply, Fin.sum_univ_two]
    have h7 : exp (-I * (↑ϕ - ↑ω) / 2) * exp (I * (↑ϕ - ↑ω) / 2) = 1 := by
      rw [← exp_add]
      have : -I * (↑ϕ - ↑ω) / 2 + I * (↑ϕ - ↑ω) / 2 = 0 := by ring
      rw [this, exp_zero]
    have h8 : exp (I * (↑ϕ + ↑ω) / 2) * exp (-I * (↑ϕ + ↑ω) / 2) = 1 := by
      rw [← exp_add]
      have : I * (↑ϕ + ↑ω) / 2 + -I * (↑ϕ + ↑ω) / 2 = 0 := by ring
      rw [this, exp_zero]
    trans (exp (-I * (↑ϕ - ↑ω) / 2) * exp (I * (↑ϕ - ↑ω) / 2)) * (↑(Real.sin (θ / 2)) : ℂ) ^ 2 -
          (exp (I * (↑ϕ + ↑ω) / 2) * exp (-I * (↑ϕ + ↑ω) / 2)) * (↑(Real.cos (θ / 2)) : ℂ) ^ 2
    · push_cast; ring_nf
    · rw [h7, h8]; push_cast; ring

/-- Lemma: Integral of exp(I * x) from 0 to 2π is 0 -/
lemma integral_exp_I_mul_self :
    ∫ x in (0 : ℝ)..2 * Real.pi, exp (I * ↑x) = 0 := by
  let f (y : ℝ) : ℂ := exp (I * ↑y) / I
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt f (exp (I * ↑x)) x := by
    intro x _
    have h1 : HasDerivAt (fun z => exp z / I) (exp (I * ↑x) / I) (I * ↑x) :=
      (hasDerivAt_exp (I * ↑x)).div_const I
    have h3 : HasDerivAt (fun (y : ℝ) => I * ↑y) I x := by
      have := ((hasDerivAt_id x).ofReal_comp).const_mul I
      simpa using this
    have h4 := h1.comp x h3
    have eq_deriv : exp (I * ↑x) / I * I = exp (I * ↑x) := by
      rw [div_mul_cancel₀ _ I_ne_zero]
    rw [eq_deriv] at h4
    exact h4
  have h_cont : ContinuousOn (fun (x : ℝ) => exp (I * ↑x)) (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    fun_prop
  have h_int : IntervalIntegrable (fun x => exp (I * ↑x)) volume 0 (2 * Real.pi) :=
    h_cont.intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt h_deriv h_int]
  have h5 : exp (I * ↑(2 * Real.pi)) = 1 := by
    have eq : I * ↑(2 * Real.pi) = 2 * ↑Real.pi * I := by push_cast; ring
    rw [eq]
    exact Complex.exp_two_pi_mul_I
  change exp (I * ↑(2 * Real.pi)) / I - exp (I * ↑(0 : ℝ)) / I = 0
  have h_zero : exp (I * ↑(0 : ℝ)) = 1 := by
    rw [Complex.ofReal_zero, mul_zero, exp_zero]
  rw [h5, h_zero, sub_self]

/-- Lemma: Integral of exp(-I * x) from 0 to 2π is 0 -/
lemma integral_exp_neg_I_mul_self :
    ∫ x in (0 : ℝ)..2 * Real.pi, exp (-I * ↑x) = 0 := by
  let f (y : ℝ) : ℂ := exp (-I * ↑y) / -I
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt f (exp (-I * ↑x)) x := by
    intro x _
    have h1 : HasDerivAt (fun z => exp z / -I) (exp (-I * ↑x) / -I) (-I * ↑x) :=
      (hasDerivAt_exp (-I * ↑x)).div_const (-I)
    have h3 : HasDerivAt (fun (y : ℝ) => -I * ↑y) (-I) x := by
      have := ((hasDerivAt_id x).ofReal_comp).const_mul (-I)
      simpa using this
    have h4 := h1.comp x h3
    have eq_deriv : exp (-I * ↑x) / -I * -I = exp (-I * ↑x) := by
      rw [div_mul_cancel₀ _ (neg_ne_zero.mpr I_ne_zero)]
    rw [eq_deriv] at h4
    exact h4
  have h_cont : ContinuousOn (fun (x : ℝ) => exp (-I * ↑x)) (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    fun_prop
  have h_int : IntervalIntegrable (fun x => exp (-I * ↑x)) volume 0 (2 * Real.pi) :=
    h_cont.intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt h_deriv h_int]
  have h5 : exp (-I * ↑(2 * Real.pi)) = 1 := by
    have eq : -I * ↑(2 * Real.pi) = -(2 * ↑Real.pi * I) := by push_cast; ring
    rw [eq, exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  change exp (-I * ↑(2 * Real.pi)) / -I - exp (-I * ↑(0 : ℝ)) / -I = 0
  have h_zero : exp (-I * ↑(0 : ℝ)) = 1 := by
    rw [Complex.ofReal_zero, mul_zero, exp_zero]
  rw [h5, h_zero, sub_self]

/-- Lemma: Integral of (cos^2(x/2) - sin^2(x/2)) * sin(x) from 0 to π is 0 -/
lemma integral_cos_sq_sub_sin_sq_mul_sin :
    ∫ x in (0 : ℝ)..Real.pi, (↑((Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2) * Real.sin x) : ℂ) = 0 := by
  have eq1 : (fun x => (↑((Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2) * Real.sin x) : ℂ)) =
             (fun x => (1 / 2 : ℂ) * ↑(Real.sin (2 * x))) := by
    ext x
    have h_cos : Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 = Real.cos x := by
      have h1 := Real.cos_two_mul (x / 2)
      have h2 := Real.sin_sq_add_cos_sq (x / 2)
      have h3 : 2 * (x / 2) = x := by ring
      rw [h3] at h1
      linarith
    rw [h_cos]
    -- Apply sin double angle identity
    have h_sin : Real.cos x * Real.sin x = 1 / 2 * Real.sin (2 * x) := by
      have := Real.sin_two_mul x
      linarith
    rw [h_sin]
    push_cast
    ring
  -- Replace the integrand with its simplified form
  rw [eq1]
  -- Pull the constant factor 1/2 outside the integral
  rw [intervalIntegral.integral_const_mul]
  -- Show the antiderivative of sin(2x) is -cos(2x)/2
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi, HasDerivAt (fun x => (↑(-Real.cos (2 * x) / 2) : ℂ)) (↑(Real.sin (2 * x))) x := by
    intro x _
    -- Outer derivative
    have h1 : HasDerivAt (fun y => -Real.cos y / 2) (Real.sin (2 * x) / 2) (2 * x) := by
      have : HasDerivAt Real.cos (-Real.sin (2 * x)) (2 * x) := Real.hasDerivAt_cos (2 * x)
      have h_mul := this.const_mul (-1 / 2 : ℝ)
      have eq_left : (fun y => (-1 / 2 : ℝ) * Real.cos y) = (fun y => -Real.cos y / 2) := by ext y; ring
      have eq_right : (-1 / 2 : ℝ) * -Real.sin (2 * x) = Real.sin (2 * x) / 2 := by ring
      rw [eq_left, eq_right] at h_mul
      exact h_mul
    -- Inner derivative
    have h2 : HasDerivAt (fun x => -Real.cos (2 * x) / 2) (Real.sin (2 * x)) x := by
      have hd_inner : HasDerivAt (fun (x : ℝ) => 2 * x) 2 x := by
        have := (hasDerivAt_id x).const_mul 2
        simpa using this
      have hd_comp := h1.comp x hd_inner
      have eq3 : Real.sin (2 * x) / 2 * 2 = Real.sin (2 * x) := by ring
      rw [eq3] at hd_comp
      exact hd_comp
    exact h2.ofReal_comp
  -- Confirm integrand continuity
  have h_cont : ContinuousOn (fun x => (↑(Real.sin (2 * x)) : ℂ)) (Set.uIcc 0 Real.pi) := by
    fun_prop
  -- Confirm integrability
  have h_int : IntervalIntegrable (fun x => (↑(Real.sin (2 * x)) : ℂ)) volume 0 Real.pi :=
    h_cont.intervalIntegrable
  -- Evaluate via FTC
  rw [integral_eq_sub_of_hasDerivAt h_deriv h_int]
  -- Bound evaluations
  have h_pi : Real.cos (2 * Real.pi) = 1 := Real.cos_two_pi
  have h_zero : Real.cos (2 * 0) = 1 := by rw [mul_zero, Real.cos_zero]
  change (1 / 2 : ℂ) * (↑(-Real.cos (2 * Real.pi) / 2) - ↑(-Real.cos (2 * 0) / 2)) = 0
  -- Compute final zero result
  rw [h_pi, h_zero]
  norm_num

/-- Define the single-qubit Haar measure integral (unnormalized) component-wise -/
-- Applies the integration measure sin(θ) over Euler angles ϕ, θ, ω
noncomputable def haarIntegral (f : ℝ → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of (fun i j =>
  ∫ ϕ in (0 : ℝ)..2 * Real.pi,
    ∫ θ in (0 : ℝ)..Real.pi,
      ∫ ω in (0 : ℝ)..2 * Real.pi,
          (↑(Real.sin θ) : ℂ) * f ϕ θ ω i j)

/-- Theorem: The first moment of the Pauli-Z operator is the zero matrix -/
-- Averages the Pauli-Z operator across all single-qubit unitary operations
theorem expectation_sigmaZ_eq_zero :
    haarIntegral (fun ϕ θ ω => U ϕ θ ω * sigmaZ * U_dagger ϕ θ ω) = 0 := by
  -- Check the outcome for each index of the 2x2 matrix
  ext i j
  fin_cases i <;> fin_cases j
  · -- case 0 0
    -- Unfold definition of the integral and substitute the matrix product calculation
    simp_rw [haarIntegral, U_sigmaZ_U_dagger_eq]
    -- Display the explicit nested integral expression
    change ∫ ϕ in (0 : ℝ)..2 * Real.pi, ∫ θ in (0 : ℝ)..Real.pi, ∫ ω in (0 : ℝ)..2 * Real.pi,
      (↑(Real.sin θ) : ℂ) * ↑(Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) = 0
    -- Group integrand terms algebraically
    have eq1 : ∀ θ : ℝ, (↑(Real.sin θ) : ℂ) * ↑(Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) =
               ↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) := by intro θ; push_cast; ring
    simp_rw [eq1]
    -- Evaluate the innermost integral with respect to ω (constant factor)
    have eq2 : ∀ θ : ℝ, ∫ (ω : ℝ) in (0 : ℝ)..2 * Real.pi, ↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) =
               (↑(2 * Real.pi) : ℂ) * ↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) := by
      intro θ
      rw [intervalIntegral.integral_const]
      have : (2 * Real.pi - 0 : ℝ) = 2 * Real.pi := by ring
      rw [this]
      change (↑(2 * Real.pi) : ℂ) * _ = _
      rfl
    simp_rw [eq2]
    -- Pull constants out of the θ integral
    have eq4 : ∫ (θ : ℝ) in (0 : ℝ)..Real.pi, (↑(2 * Real.pi) : ℂ) * ↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) =
               (↑(2 * Real.pi) : ℂ) * ∫ (θ : ℝ) in (0 : ℝ)..Real.pi, ↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) := by rw [intervalIntegral.integral_const_mul]
    simp_rw [eq4, integral_cos_sq_sub_sin_sq_mul_sin]
    -- Resolve the evaluated zero to collapse the nested integration
    have eq5 : (↑(2 * Real.pi) : ℂ) * (0 : ℂ) = 0 := by ring
    simp_rw [eq5, intervalIntegral.integral_zero]
  · -- case 0 1
    -- Unfold definition of the integral and substitute the matrix product calculation
    simp_rw [haarIntegral, U_sigmaZ_U_dagger_eq]
    change ∫ ϕ in (0 : ℝ)..2 * Real.pi, ∫ θ in (0 : ℝ)..Real.pi, ∫ ω in (0 : ℝ)..2 * Real.pi,
      (↑(Real.sin θ) : ℂ) * (exp (-I * ↑ω) * ↑(Real.cos (θ / 2) * Real.sin (θ / 2)) + exp (-I * ↑ω) * ↑(Real.sin (θ / 2) * Real.cos (θ / 2))) = 0
    -- Factor out the exp(-I*ω) term for integration over ω
    have eq1 : ∀ θ ω : ℝ, (↑(Real.sin θ) : ℂ) * (exp (-I * ↑ω) * ↑(Real.cos (θ / 2) * Real.sin (θ / 2)) + exp (-I * ↑ω) * ↑(Real.sin (θ / 2) * Real.cos (θ / 2))) =
               exp (-I * ↑ω) * ((↑(Real.sin θ) : ℂ) * (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) + ↑(Real.sin (θ / 2) * Real.cos (θ / 2)))) := by intros; push_cast; ring
    simp_rw [eq1]
    -- Evaluate the ω integral which results in zero
    have eq2 : ∀ θ : ℝ, ∫ (ω : ℝ) in (0 : ℝ)..2 * Real.pi, exp (-I * ↑ω) * ((↑(Real.sin θ) : ℂ) * (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) + ↑(Real.sin (θ / 2) * Real.cos (θ / 2)))) =
               (∫ (ω : ℝ) in (0 : ℝ)..2 * Real.pi, exp (-I * ↑ω)) * ((↑(Real.sin θ) : ℂ) * (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) + ↑(Real.sin (θ / 2) * Real.cos (θ / 2)))) := by intro θ; rw [intervalIntegral.integral_mul_const]
    simp_rw [eq2, integral_exp_neg_I_mul_self]
    -- Resolve the evaluated zero to collapse the nested integration
    have eq3 : ∀ θ : ℝ, (0 : ℂ) * ((↑(Real.sin θ) : ℂ) * (↑(Real.cos (θ / 2) * Real.sin (θ / 2)) + ↑(Real.sin (θ / 2) * Real.cos (θ / 2)))) = 0 := by intro θ; ring
    simp_rw [eq3, intervalIntegral.integral_zero]
  · -- case 1 0
    -- Unfold definition of the integral and substitute the matrix product calculation
    simp_rw [haarIntegral, U_sigmaZ_U_dagger_eq]
    change ∫ ϕ in (0 : ℝ)..2 * Real.pi, ∫ θ in (0 : ℝ)..Real.pi, ∫ ω in (0 : ℝ)..2 * Real.pi,
      (↑(Real.sin θ) : ℂ) * (exp (I * ↑ω) * ↑(Real.sin (θ / 2) * Real.cos (θ / 2)) + exp (I * ↑ω) * ↑(Real.cos (θ / 2) * Real.sin (θ / 2))) = 0
    -- Factor out the exp(I*ω) term for integration over ω
    have eq1 : ∀ θ ω : ℝ, (↑(Real.sin θ) : ℂ) * (exp (I * ↑ω) * ↑(Real.sin (θ / 2) * Real.cos (θ / 2)) + exp (I * ↑ω) * ↑(Real.cos (θ / 2) * Real.sin (θ / 2))) =
               exp (I * ↑ω) * ((↑(Real.sin θ) : ℂ) * (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) + ↑(Real.cos (θ / 2) * Real.sin (θ / 2)))) := by intros; push_cast; ring
    simp_rw [eq1]
    -- Evaluate the ω integral which results in zero
    have eq2 : ∀ θ : ℝ, ∫ (ω : ℝ) in (0 : ℝ)..2 * Real.pi, exp (I * ↑ω) * ((↑(Real.sin θ) : ℂ) * (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) + ↑(Real.cos (θ / 2) * Real.sin (θ / 2)))) =
               (∫ (ω : ℝ) in (0 : ℝ)..2 * Real.pi, exp (I * ↑ω)) * ((↑(Real.sin θ) : ℂ) * (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) + ↑(Real.cos (θ / 2) * Real.sin (θ / 2)))) := by intro θ; rw [intervalIntegral.integral_mul_const]
    simp_rw [eq2, integral_exp_I_mul_self]
    -- Resolve the evaluated zero to collapse the nested integration
    have eq3 : ∀ θ : ℝ, (0 : ℂ) * ((↑(Real.sin θ) : ℂ) * (↑(Real.sin (θ / 2) * Real.cos (θ / 2)) + ↑(Real.cos (θ / 2) * Real.sin (θ / 2)))) = 0 := by intro θ; ring
    simp_rw [eq3, intervalIntegral.integral_zero]
  · -- case 1 1
    -- Unfold definition of the integral and substitute the matrix product calculation
    simp_rw [haarIntegral, U_sigmaZ_U_dagger_eq]
    change ∫ ϕ in (0 : ℝ)..2 * Real.pi, ∫ θ in (0 : ℝ)..Real.pi, ∫ ω in (0 : ℝ)..2 * Real.pi,
      (↑(Real.sin θ) : ℂ) * ↑(Real.sin (θ / 2) ^ 2 - Real.cos (θ / 2) ^ 2) = 0
    -- Group integrand terms algebraically (note negative sign extraction)
    have eq1 : ∀ θ : ℝ, (↑(Real.sin θ) : ℂ) * ↑(Real.sin (θ / 2) ^ 2 - Real.cos (θ / 2) ^ 2) =
               -↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) := by intro θ; push_cast; ring
    simp_rw [eq1]
    -- Evaluate the innermost integral with respect to ω (constant factor)
    have eq2 : ∀ θ : ℝ, ∫ (ω : ℝ) in (0 : ℝ)..2 * Real.pi, -↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) =
               -(↑(2 * Real.pi) : ℂ) * ↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) := by
      intro θ
      rw [intervalIntegral.integral_neg]
      rw [intervalIntegral.integral_const]
      have : (2 * Real.pi - 0 : ℝ) = 2 * Real.pi := by ring
      rw [this]
      change -((↑(2 * Real.pi) : ℂ) * _) = _
      ring
    simp_rw [eq2]
    -- Pull constants out of the θ integral
    have eq4 : ∫ (θ : ℝ) in (0 : ℝ)..Real.pi, -(↑(2 * Real.pi) : ℂ) * ↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) =
               -(↑(2 * Real.pi) : ℂ) * ∫ (θ : ℝ) in (0 : ℝ)..Real.pi, ↑((Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * Real.sin θ) := by rw [intervalIntegral.integral_const_mul]
    simp_rw [eq4, integral_cos_sq_sub_sin_sq_mul_sin]
    -- Resolve the evaluated zero to collapse the nested integration
    have eq5 : -(↑(2 * Real.pi) : ℂ) * (0 : ℂ) = 0 := by ring
    simp_rw [eq5, intervalIntegral.integral_zero]

theorem expectation_sigmaZ_eq_trace_sigmaZ :
    haarIntegral (fun ϕ θ ω => U ϕ θ ω * sigmaZ * U_dagger ϕ θ ω) = (Matrix.trace sigmaZ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [expectation_sigmaZ_eq_zero, trace_sigmaZ_smul_one]
