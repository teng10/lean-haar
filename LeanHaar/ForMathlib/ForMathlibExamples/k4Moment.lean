import LeanHaar.ForMathlib.Haar
import LeanHaar.ForMathlib.Weingarten
import LeanHaar.ForMathlib.WeingartenInverse

import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Example: Computing moments for `k = 4`
This file carries out, inside the `LeanHaar/ForMathlib` framework, the computation performed
numerically in `kCoefficients.ipynb` for the fourth Haar moment.
It provides:

* **(Part 1)** the explicit **Weingarten function values** `wgVal` for `S₄` (one rational
  function of the dimension `d` per cycle type of `S₄`), together with a proof
  (`wgVal_inverts_gram`) that they invert the Weingarten Gram matrix
  `Tr(V_d^†(σ) V_d(π)) = d^{#cycles(σ⁻¹π)}`. Inverting the Gram matrix is the *defining*
  property of the Weingarten coefficients, so this validates the numbers used in the notebook.

* **(Part 2)** the fourth moment operator itself (`k4_moment`): for `4 ≤ d`,
  `momentOp O = ∑_{π ∈ S₄} c_π(O) • V_d(π)`, where the coefficient `c_π(O)` is assembled
  exactly as in the notebook, `c_π(O) = ∑_{σ ∈ S₄} Wg(π⁻¹σ) · Tr(V_d^†(σ) O)`.

The notebook groups the traces `Tr(V_d^†(σ) O)` by the cycle type of `σ`, using a single symbol
`Tr(V_j O)` per cycle type. That grouping is exact only when `σ ↦ Tr(V_d^†(σ) O)` is constant
on conjugacy classes; for a general operator `O` the six four-cycles (say) contribute six
genuinely different traces. We therefore keep all `24` traces distinct in the general theorem
`k4_moment` (which is then true for *every* `O`).

## The Weingarten values (Part 1)

Writing `P d = (d-3)(d-2)(d-1)(d+1)(d+2)(d+3) = (d²-1)(d²-4)(d²-9)`, the Weingarten function of
`S₄` takes the following values (over the common denominator `d² · P d`), matching the values
computed in `kCoefficients.ipynb`:

| cycle type      | representative | `Wg`                       |
|-----------------|----------------|----------------------------|
| `(1,1,1,1)`     | `id`           | `(d⁴ - 8d² + 6)/(d² P)`    |
| `(2,1,1)`       | `(0 1)`        | `(-d³ + 4d)/(d² P)`        |
| `(2,2)`         | `(0 1)(2 3)`   | `(d² + 6)/(d² P)`          |
| `(3,1)`         | `(0 1 2)`      | `(2d² - 3)/(d² P)`         |
| `(4)`           | `(0 1 2 3)`    | `(-5d)/(d² P)`             |
-/

open SchurWeyl

open scoped Matrix

namespace SchurWeyl.K4

/-! ### Combinatorial data on `S₄` -/
/-- The number of cycles of a permutation of `Fin 4`, **including** fixed points.
`Equiv.Perm.cycleType` lists only the non-trivial cycles, so we add back the fixed points. -/
def numCyc (σ : Equiv.Perm (Fin 4)) : ℕ := σ.cycleType.card + (4 - σ.cycleType.sum)
/-- The index `0,…,4` of the cycle type of a permutation of `Fin 4`:
`0 ↦ (4)`, `1 ↦ (3,1)`, `2 ↦ (2,2)`, `3 ↦ (2,1,1)`, `4 ↦ (1,1,1,1)`. -/
def ctIdx (σ : Equiv.Perm (Fin 4)) : ℕ :=
  if σ.cycleType = {4} then 0
  else if σ.cycleType = {3} then 1
  else if σ.cycleType = {2, 2} then 2
  else if σ.cycleType = {2} then 3
  else 4


/-! ### Part 1: the Weingarten function values for `S₄` -/

/-- The common denominator factor `P d = (d-3)(d-2)(d-1)(d+1)(d+2)(d+3)`. -/
noncomputable def Pden (d : ℂ) : ℂ := (d - 3) * (d - 2) * (d - 1) * (d + 1) * (d + 2) * (d + 3)
/-- The numerator of the Weingarten value, as a function of the cycle-type index. -/

noncomputable def wgNum (i : ℕ) (d : ℂ) : ℂ :=
  if i = 0 then -5 * d                    -- (4)
  else if i = 1 then 2 * d ^ 2 - 3        -- (3,1)
  else if i = 2 then d ^ 2 + 6            -- (2,2)
  else if i = 3 then -d ^ 3 + 4 * d       -- (2,1,1)
  else d ^ 4 - 8 * d ^ 2 + 6              -- (1,1,1,1)

/-- The **Weingarten function** `Wg(σ, d)` for `S₄`, depending only on the cycle type of `σ`.
These are exactly the values computed in `kCoefficients.ipynb`. -/
noncomputable def wgVal (d : ℂ) (σ : Equiv.Perm (Fin 4)) : ℂ :=
  wgNum (ctIdx σ) d / (d ^ 2 * Pden d)

/-! ### Basic operator lemmas -/
/-- `V_d^†(σ) V_d(π) = V_d(σ⁻¹π)`: the permutation operators form a representation. -/
lemma permDual_comp_permOp (d : ℕ) (σ π : Equiv.Perm (Fin 4)) :
    permDual d σ ∘ₗ permOp d π = permOp d (σ⁻¹ * π) := by
  have h1 : permDual d σ = permMonoidHom d 4 σ⁻¹ := rfl
  have h2 : permOp d π = permMonoidHom d 4 π := rfl
  have h3 : permOp d (σ⁻¹ * π) = permMonoidHom d 4 (σ⁻¹ * π) := rfl
  rw [h1, h2, h3, map_mul]; rfl

/-- `weingartenGramNat d 4 1 τ` counts the `τ`-invariant index functions. -/
lemma wgnat_one_eq (d : ℕ) (τ : Equiv.Perm (Fin 4)) :
    weingartenGramNat d 4 1 τ = Fintype.card {J : Fin 4 → Fin d // J = J ∘ τ.symm} := by
  unfold weingartenGramNat
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro J
  constructor
  · intro h; funext x; have := congr_fun h x; simpa using this
  · intro h; funext x; have := congr_fun h x; simpa using this

/-- Conjugation invariance of the count of `τ`-invariant index functions. -/
lemma card_inv_conj (d : ℕ) (g τ : Equiv.Perm (Fin 4)) :
    Fintype.card {J : Fin 4 → Fin d // J = J ∘ (g * τ * g⁻¹).symm}
      = Fintype.card {J : Fin 4 → Fin d // J = J ∘ τ.symm} := by
  have hp : (g * τ * g⁻¹).symm = g * τ.symm * g⁻¹ := by
    simp only [← Equiv.Perm.inv_def]; group
  apply Fintype.card_congr
  refine ⟨fun J => ⟨J.1 ∘ (g : Fin 4 → Fin 4), ?_⟩,
          fun K => ⟨K.1 ∘ (g⁻¹ : Equiv.Perm (Fin 4)), ?_⟩, ?_, ?_⟩
  · obtain ⟨J, hJ⟩ := J
    funext x
    have h := congr_fun hJ (g x)
    simp only [Function.comp_apply, hp, Equiv.Perm.mul_apply] at h ⊢
    simpa using h
  · obtain ⟨K, hK⟩ := K
    funext x
    have h := congr_fun hK (g⁻¹ x)
    simp only [Function.comp_apply, hp, Equiv.Perm.mul_apply] at h ⊢
    simpa using h
  · rintro ⟨J, hJ⟩
    simp only [Subtype.mk.injEq]
    funext x
    simp [Function.comp_apply]
  · rintro ⟨K, hK⟩
    simp only [Subtype.mk.injEq]
    funext x
    simp [Function.comp_apply]

/-- `numCyc` is a class function of `τ`. -/
lemma numCyc_conj' (g κ : Equiv.Perm (Fin 4)) : numCyc (g * κ * g⁻¹) = numCyc κ := by
  native_decide +revert

lemma card_rep_id (d : ℕ) :
    Fintype.card {J : Fin 4 → Fin d // J = J ∘ (1 : Equiv.Perm (Fin 4)).symm} = d ^ 4 := by
  have e : {J : Fin 4 → Fin d // J = J ∘ (1 : Equiv.Perm (Fin 4)).symm} ≃ (Fin 4 → Fin d) :=
    Equiv.subtypeUnivEquiv (fun J => by funext x; simp [pull_end])
  rw [Fintype.card_congr e, Fintype.card_fun]; simp [Fintype.card_fin]

lemma card_rep_swap (d : ℕ) :
    Fintype.card {J : Fin 4 → Fin d // J = J ∘ (Equiv.swap (0 : Fin 4) 1).symm} = d ^ 3 := by
  have e : {J : Fin 4 → Fin d // J = J ∘ (Equiv.swap (0 : Fin 4) 1).symm} ≃
      (Fin d × Fin d × Fin d) := by
    refine ⟨fun J => (J.1 0, J.1 2, J.1 3), fun p => ⟨![p.1, p.1, p.2.1, p.2.2], ?_⟩, ?_, ?_⟩
    · funext x; fin_cases x <;> simp [Equiv.swap_apply_def]
    · rintro ⟨J, hJ⟩
      simp only [Subtype.mk.injEq]; funext x
      have h0 : J 0 = J 1 := by have h := congr_fun hJ 1; simp at h; exact h.symm
      fin_cases x <;> simp [h0]
    · rintro ⟨a, b, c⟩; simp
  rw [Fintype.card_congr e]; simp only [Fintype.card_prod, Fintype.card_fin]; ring

lemma card_rep_dt (d : ℕ) :
    Fintype.card {J : Fin 4 → Fin d // J = J ∘ (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3).symm}
      = d ^ 2 := by
  have e : {J : Fin 4 → Fin d // J = J ∘ (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3).symm} ≃
      (Fin d × Fin d) := by
    refine ⟨fun J => (J.1 0, J.1 2), fun p => ⟨![p.1, p.1, p.2, p.2], ?_⟩, ?_, ?_⟩
    · funext x; fin_cases x <;>
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def]
    · rintro ⟨J, hJ⟩
      simp only [Subtype.mk.injEq]; funext x
      have h0 : J 0 = J 1 := by
        have h := congr_fun hJ 1
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def] at h
        exact h.symm
      have h1 : J 2 = J 3 := by
        have h := congr_fun hJ 3
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def] at h
        exact h.symm
      fin_cases x <;> simp [h0, h1]
    · rintro ⟨a, b⟩; simp
  rw [Fintype.card_congr e]; simp only [Fintype.card_prod, Fintype.card_fin]; ring

lemma card_rep_3cyc (d : ℕ) :
    Fintype.card {J : Fin 4 → Fin d // J = J ∘ (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2).symm}
      = d ^ 2 := by
  have e : {J : Fin 4 → Fin d // J = J ∘ (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2).symm} ≃
      (Fin d × Fin d) := by
    refine ⟨fun J => (J.1 0, J.1 3), fun p => ⟨![p.1, p.1, p.1, p.2], ?_⟩, ?_, ?_⟩
    · funext x; fin_cases x <;>
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def]
    · rintro ⟨J, hJ⟩
      simp only [Subtype.mk.injEq]; funext x
      have h0 : J 0 = J 1 := by
        have h := congr_fun hJ 1
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def] at h
        exact h.symm
      have h1 : J 1 = J 2 := by
        have h := congr_fun hJ 2
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def] at h
        exact h.symm
      fin_cases x <;> simp [h0, h1]
    · rintro ⟨a, b⟩; simp
  rw [Fintype.card_congr e]; simp only [Fintype.card_prod, Fintype.card_fin]; ring

lemma card_rep_4cyc (d : ℕ) :
    Fintype.card {J : Fin 4 → Fin d //
        J = J ∘ (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2 * Equiv.swap 2 3).symm} = d ^ 1 := by
  have e : {J : Fin 4 → Fin d //
      J = J ∘ (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2 * Equiv.swap 2 3).symm} ≃ (Fin d) := by
    refine ⟨fun J => J.1 0, fun a => ⟨![a, a, a, a], ?_⟩, ?_, ?_⟩
    · funext x; fin_cases x <;>
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def]
    · rintro ⟨J, hJ⟩
      simp only [Subtype.mk.injEq]; funext x
      have h0 : J 0 = J 1 := by
        have h := congr_fun hJ 1
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def] at h
        exact h.symm
      have h1 : J 1 = J 2 := by
        have h := congr_fun hJ 2
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def] at h
        exact h.symm
      have h2 : J 2 = J 3 := by
        have h := congr_fun hJ 3
        simp [← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.swap_apply_def] at h
        exact h.symm
      fin_cases x <;> simp [h0, h1, h2]
    · intro a; simp
  rw [Fintype.card_congr e]; simp only [Fintype.card_fin, pow_one]

/-- **Combinatorial core.** The number of index functions `J : Fin 4 → Fin d` that are
invariant under `τ` (equivalently constant on the cycles of `τ`) is `d^{#cycles(τ)}`.
Proved by reducing to the five conjugacy-class representatives of `S₄`. -/
lemma weingartenGramNat_one (d : ℕ) (τ : Equiv.Perm (Fin 4)) :
    weingartenGramNat d 4 1 τ = d ^ numCyc τ := by
  have hex : ∀ τ : Equiv.Perm (Fin 4),
      ∃ τ' ∈ ([1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3,
               Equiv.swap 0 1 * Equiv.swap 1 2,
               Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3] : List _),
        ∃ g, τ = g * τ' * g⁻¹ := by native_decide
  obtain ⟨τ', hmem, g, rfl⟩ := hex τ
  rw [wgnat_one_eq, card_inv_conj, ← wgnat_one_eq, numCyc_conj', wgnat_one_eq]
  fin_cases hmem
  · rw [card_rep_id, show numCyc (1 : Equiv.Perm (Fin 4)) = 4 from by decide]
  · rw [card_rep_swap, show numCyc (Equiv.swap (0 : Fin 4) 1) = 3 from by decide]
  · rw [card_rep_dt, show numCyc (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = 2 from by decide]
  · rw [card_rep_3cyc, show numCyc (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) = 2 from by decide]
  · rw [card_rep_4cyc,
      show numCyc (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2 * Equiv.swap 2 3) = 1 from by decide]

/-- The trace of the permutation operator is `d^{#cycles}`. -/
lemma trace_permOp (d : ℕ) (τ : Equiv.Perm (Fin 4)) :
    LinearMap.trace ℂ (TensV d 4) (permOp d τ) = (d : ℂ) ^ (numCyc τ) := by
  have h : weingartenGram d 4 1 τ = LinearMap.trace ℂ (TensV d 4) (permOp d τ) := by
    unfold weingartenGram
    rw [permDual_comp_permOp]
    simp
  rw [← h, weingartenGram_eq_natCast, weingartenGramNat_one]
  push_cast
  ring

/-- **Closed form of the Weingarten Gram matrix entries** for `k = 4`:
`Tr(V_d^†(σ) V_d(π)) = d^{#cycles(σ⁻¹π)}`. -/
lemma weingartenGram_closed (d : ℕ) (σ π : Equiv.Perm (Fin 4)) :
    weingartenGram d 4 σ π = (d : ℂ) ^ (numCyc (σ⁻¹ * π)) := by
  unfold weingartenGram
  rw [permDual_comp_permOp, trace_permOp]

/-! ### The core inversion identity (Part 1)
The heart of the computation is the identity `∑_μ Wg(μ⁻¹ν) · d^{#cycles(μ)} = [ν = 1]`
(`wg_class_sum`). We prove it by reducing to the five conjugacy-class representatives of `S₄`
and, for each representative, grouping the 24 summands by the pair
`(ctIdx (μ⁻¹ ν₀), numCyc μ)` and clearing denominators. -/
lemma ctIdx_lt (x : Equiv.Perm (Fin 4)) : ctIdx x < 5 := by
  unfold ctIdx
  split_ifs <;> omega

/-- Generic reduction of the class sum to a fibered sum over the 25 possible values of the
key `5 * numCyc μ + ctIdx (μ⁻¹ ν0)`. -/
lemma wg_rep_reduce (d : ℕ) (ν0 : Equiv.Perm (Fin 4)) :
    (∑ μ : Equiv.Perm (Fin 4), wgVal (d : ℂ) (μ⁻¹ * ν0) * (d : ℂ) ^ (numCyc μ))
      = ∑ j ∈ Finset.range 25,
          (Finset.univ.filter
              (fun i : Equiv.Perm (Fin 4) => 5 * numCyc i + ctIdx (i⁻¹ * ν0) = j)).card
            • (wgNum (j % 5) (d : ℂ) / ((d : ℂ) ^ 2 * Pden (d : ℂ)) * (d : ℂ) ^ (j / 5)) := by
  have hkey : ∀ μ : Equiv.Perm (Fin 4),
      5 * numCyc μ + ctIdx (μ⁻¹ * ν0) ∈ Finset.range 25 := by
    intro μ
    have h1 : numCyc μ ≤ 4 := by decide +revert
    have h2 : ctIdx (μ⁻¹ * ν0) < 5 := ctIdx_lt _
    simp only [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to (fun x _ => hkey x)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨_, hij⟩ := hi
  have hlt : ctIdx (i⁻¹ * ν0) < 5 := ctIdx_lt _
  have hnc : numCyc i = j / 5 := by omega
  have hci : ctIdx (i⁻¹ * ν0) = j % 5 := by omega
  rw [wgVal, hci, hnc]

/-- Nonzero denominator facts for `4 ≤ d`. -/
lemma denom_facts (d : ℕ) (hd : 4 ≤ d) : (d : ℂ) ≠ 0 ∧ Pden (d : ℂ) ≠ 0 := by
  have hne : ∀ m : ℕ, m < 4 → (d : ℂ) - m ≠ 0 := by
    intro m hm h
    have : d = m := by exact_mod_cast (sub_eq_zero.mp h)
    omega
  have hd0 : (d : ℂ) ≠ 0 := by have := hne 0 (by norm_num); simpa using this
  refine ⟨hd0, ?_⟩
  unfold Pden
  have h1 : (d : ℂ) - 1 ≠ 0 := by have := hne 1 (by norm_num); simpa using this
  have h2 : (d : ℂ) - 2 ≠ 0 := by have := hne 2 (by norm_num); simpa using this
  have h3 : (d : ℂ) - 3 ≠ 0 := by have := hne 3 (by norm_num); simpa using this
  have h4 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (show ((d : ℤ) + 1) ≠ 0 by omega)
  have h5 : (d : ℂ) + 2 ≠ 0 := by exact_mod_cast (show ((d : ℤ) + 2) ≠ 0 by omega)
  have h6 : (d : ℂ) + 3 ≠ 0 := by exact_mod_cast (show ((d : ℤ) + 3) ≠ 0 by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h3 h2) h1) h4) h5) h6

lemma wg_rep_id (d : ℕ) (hd : 4 ≤ d) :
    ∑ μ : Equiv.Perm (Fin 4), wgVal (d : ℂ) (μ⁻¹ * 1) * (d : ℂ) ^ (numCyc μ) = 1 := by
  obtain ⟨hd0, hP⟩ := denom_facts d hd
  rw [wg_rep_reduce d 1]
  have hc : ∀ j ∈ Finset.range 25,
      (Finset.univ.filter
          (fun i : Equiv.Perm (Fin 4) => 5 * numCyc i + ctIdx (i⁻¹ * 1) = j)).card
      = [0,0,0,0,0,6,0,0,0,0,0,8,3,0,0,0,0,0,6,0,0,0,0,0,1].getD j 0 := by decide
  rw [Finset.sum_congr rfl (fun j hj => by rw [hc j hj])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wgNum]
  field_simp [hd0, hP]
  unfold Pden
  ring

lemma wg_rep_swap (d : ℕ) (hd : 4 ≤ d) :
    ∑ μ : Equiv.Perm (Fin 4),
      wgVal (d : ℂ) (μ⁻¹ * (Equiv.swap 0 1)) * (d : ℂ) ^ (numCyc μ) = 0 := by
  obtain ⟨hd0, hP⟩ := denom_facts d hd
  rw [wg_rep_reduce d (Equiv.swap 0 1)]
  have hc : ∀ j ∈ Finset.range 25,
      (Finset.univ.filter
          (fun i : Equiv.Perm (Fin 4) => 5 * numCyc i + ctIdx (i⁻¹ * (Equiv.swap 0 1)) = j)).card
      = [0,0,0,0,0,0,4,2,0,0,6,0,0,5,0,0,4,1,0,1,0,0,0,1,0].getD j 0 := by decide
  rw [Finset.sum_congr rfl (fun j hj => by rw [hc j hj])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wgNum]
  field_simp [hd0, hP]
  unfold Pden
  ring

lemma wg_rep_dt (d : ℕ) (hd : 4 ≤ d) :
    ∑ μ : Equiv.Perm (Fin 4),
      wgVal (d : ℂ) (μ⁻¹ * (Equiv.swap 0 1 * Equiv.swap 2 3)) * (d : ℂ) ^ (numCyc μ) = 0 := by
  obtain ⟨hd0, hP⟩ := denom_facts d hd
  rw [wg_rep_reduce d (Equiv.swap 0 1 * Equiv.swap 2 3)]
  have hc : ∀ j ∈ Finset.range 25,
      (Finset.univ.filter (fun i : Equiv.Perm (Fin 4) =>
          5 * numCyc i + ctIdx (i⁻¹ * (Equiv.swap 0 1 * Equiv.swap 2 3)) = j)).card
      = [0,0,0,0,0,2,0,0,4,0,0,8,2,0,1,4,0,0,2,0,0,0,1,0,0].getD j 0 := by decide
  rw [Finset.sum_congr rfl (fun j hj => by rw [hc j hj])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wgNum]
  field_simp [hd0, hP]
  unfold Pden
  ring

lemma wg_rep_3cyc (d : ℕ) (hd : 4 ≤ d) :
    ∑ μ : Equiv.Perm (Fin 4),
      wgVal (d : ℂ) (μ⁻¹ * (c[0,1,2] : Equiv.Perm (Fin 4))) * (d : ℂ) ^ (numCyc μ) = 0 := by
  obtain ⟨hd0, hP⟩ := denom_facts d hd
  rw [wg_rep_reduce d (c[0,1,2] : Equiv.Perm (Fin 4))]
  have hc : ∀ j ∈ Finset.range 25,
      (Finset.univ.filter (fun i : Equiv.Perm (Fin 4) =>
          5 * numCyc i + ctIdx (i⁻¹ * (c[0,1,2] : Equiv.Perm (Fin 4))) = j)).card
      = [0,0,0,0,0,3,0,0,3,0,0,7,3,0,1,3,0,0,3,0,0,1,0,0,0].getD j 0 := by decide
  rw [Finset.sum_congr rfl (fun j hj => by rw [hc j hj])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wgNum]
  field_simp [hd0, hP]
  unfold Pden
  ring

lemma wg_rep_4cyc (d : ℕ) (hd : 4 ≤ d) :
    ∑ μ : Equiv.Perm (Fin 4),
      wgVal (d : ℂ) (μ⁻¹ * (c[0,1,2,3] : Equiv.Perm (Fin 4))) * (d : ℂ) ^ (numCyc μ) = 0 := by
  obtain ⟨hd0, hP⟩ := denom_facts d hd
  rw [wg_rep_reduce d (c[0,1,2,3] : Equiv.Perm (Fin 4))]
  have hc : ∀ j ∈ Finset.range 25,
      (Finset.univ.filter (fun i : Equiv.Perm (Fin 4) =>
          5 * numCyc i + ctIdx (i⁻¹ * (c[0,1,2,3] : Equiv.Perm (Fin 4))) = j)).card
      = [0,0,0,0,0,0,4,1,0,1,5,0,0,6,0,0,4,2,0,0,1,0,0,0,0].getD j 0 := by decide
  rw [Finset.sum_congr rfl (fun j hj => by rw [hc j hj])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [wgNum]
  field_simp [hd0, hP]
  unfold Pden
  ring

lemma numCyc_conj (g κ : Equiv.Perm (Fin 4)) : numCyc (g * κ * g⁻¹) = numCyc κ := by
  native_decide +revert

lemma ctIdx_conj (g κ : Equiv.Perm (Fin 4)) : ctIdx (g * κ * g⁻¹) = ctIdx κ := by
  native_decide +revert

lemma wgVal_conj (d : ℂ) (g τ : Equiv.Perm (Fin 4)) :
    wgVal d (g * τ * g⁻¹) = wgVal d τ := by
  unfold wgVal
  rw [ctIdx_conj]

/-- **Conjugation invariance of the class sum.** -/
lemma wg_Hsum_conj (d : ℕ) (g κ : Equiv.Perm (Fin 4)) :
    (∑ μ : Equiv.Perm (Fin 4),
        wgVal (d : ℂ) (μ⁻¹ * (g * κ * g⁻¹)) * (d : ℂ) ^ (numCyc μ))
      = ∑ μ : Equiv.Perm (Fin 4), wgVal (d : ℂ) (μ⁻¹ * κ) * (d : ℂ) ^ (numCyc μ) := by
  symm
  refine Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ (fun ρ => ?_)
  have e1 : ((MulAut.conj g).toEquiv ρ)⁻¹ * (g * κ * g⁻¹) = g * (ρ⁻¹ * κ) * g⁻¹ := by
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    group
  rw [e1, wgVal_conj]
  congr 1
  rw [show (MulAut.conj g).toEquiv ρ = g * ρ * g⁻¹ by
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply], numCyc_conj]

/-- The key per-cycle-type sum: `∑_μ Wg(μ⁻¹ν) · d^{#cycles(μ)} = [ν = 1]`. -/
lemma wg_class_sum (d : ℕ) (hd : 4 ≤ d) (ν : Equiv.Perm (Fin 4)) :
    ∑ μ : Equiv.Perm (Fin 4), wgVal (d : ℂ) (μ⁻¹ * ν) * (d : ℂ) ^ (numCyc μ)
      = if ν = 1 then 1 else 0 := by
  have hex : ∀ ν : Equiv.Perm (Fin 4),
      ∃ ν' ∈ ([1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3,
                (c[0,1,2] : Equiv.Perm (Fin 4)), (c[0,1,2,3] : Equiv.Perm (Fin 4))] : List _),
        ∃ g, ν = g * ν' * g⁻¹ := by native_decide
  obtain ⟨ν', hmem, g, rfl⟩ := hex ν
  rw [wg_Hsum_conj]
  have hone : (g * ν' * g⁻¹ = 1) ↔ ν' = 1 := by rw [mul_inv_eq_one, mul_eq_left]
  rw [if_congr hone rfl rfl]
  fin_cases hmem
  · exact wg_rep_id d hd
  · rw [if_neg (by decide)]; exact wg_rep_swap d hd
  · rw [if_neg (by decide)]; exact wg_rep_dt d hd
  · rw [if_neg (by decide)]; exact wg_rep_3cyc d hd
  · rw [if_neg (by decide)]; exact wg_rep_4cyc d hd

/-- **Part 1: the Weingarten values invert the Gram matrix.** For `4 ≤ d`,
`∑_{π} Wg(π⁻¹ρ) · Tr(V_d^†(σ) V_d(π)) = [σ = ρ]`, i.e. the matrix `Wg(σ⁻¹π)` is the inverse
of the Gram matrix `Tr(V_d^†(σ) V_d(π))`. This is the defining property of the Weingarten
coefficients, so it certifies that `wgVal` are the correct coefficients for `k = 4`. -/
lemma wgVal_inverts_gram (d : ℕ) (hd : 4 ≤ d) (σ ρ : Equiv.Perm (Fin 4)) :
    ∑ π : Equiv.Perm (Fin 4), wgVal (d : ℂ) (π⁻¹ * ρ) * weingartenGram d 4 σ π
      = if σ = ρ then 1 else 0 := by
  simp only [weingartenGram_closed]
  -- reindex π = σ * μ
  rw [← Equiv.sum_comp (Equiv.mulLeft σ)
      (fun π => wgVal (d : ℂ) (π⁻¹ * ρ) * (d : ℂ) ^ (numCyc (σ⁻¹ * π)))]
  have hkey : ∀ μ : Equiv.Perm (Fin 4),
      wgVal (d : ℂ) (((Equiv.mulLeft σ) μ)⁻¹ * ρ)
          * (d : ℂ) ^ (numCyc (σ⁻¹ * ((Equiv.mulLeft σ) μ)))
        = wgVal (d : ℂ) (μ⁻¹ * (σ⁻¹ * ρ)) * (d : ℂ) ^ (numCyc μ) := by
    intro μ
    simp only [Equiv.coe_mulLeft]
    rw [show σ⁻¹ * (σ * μ) = μ by group, show (σ * μ)⁻¹ * ρ = μ⁻¹ * (σ⁻¹ * ρ) by group]
  simp only [hkey]
  rw [wg_class_sum d hd (σ⁻¹ * ρ)]
  simp only [inv_mul_eq_one]

/-! ### Part 2: the fourth moment operator -/
/-- The notebook coefficient `c_π(O) = ∑_σ Wg(π⁻¹σ) · Tr(V_d^†(σ) O)`. -/
noncomputable def coeff (d : ℕ) (O : Module.End ℂ (TensV d 4))
    (π : Equiv.Perm (Fin 4)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin 4), wgVal (d : ℂ) (π⁻¹ * σ) * weingartenVec d 4 O σ

/-- The notebook coefficient vector solves the Weingarten linear system. -/
lemma coeff_mem_solutionSet (d : ℕ) (hd : 4 ≤ d) (O : Module.End ℂ (TensV d 4)) :
    (coeff d O) ∈ weingartenSolutionSet d 4 O := by
  show ∀ σ : Equiv.Perm (Fin 4),
      weingartenVec d 4 O σ = ∑ π : Equiv.Perm (Fin 4), coeff d O π * weingartenGram d 4 σ π
  intro σ
  have hrhs : (∑ π : Equiv.Perm (Fin 4), coeff d O π * weingartenGram d 4 σ π)
      = ∑ ρ : Equiv.Perm (Fin 4), weingartenVec d 4 O ρ
          * (∑ π : Equiv.Perm (Fin 4), wgVal (d : ℂ) (π⁻¹ * ρ) * weingartenGram d 4 σ π) := by
    simp only [coeff, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun π _ => ?_)
    ring
  rw [hrhs]
  simp only [wgVal_inverts_gram d hd]
  simp

/-- **Part 2: the fourth Haar moment.** For `4 ≤ d` and any operator `O`, the Haar moment
operator is the explicit linear combination of permutation operators
`momentOp O = ∑_{π ∈ S₄} c_π(O) • V_d(π)`, with the coefficients `c_π(O)` computed exactly as
expected. -/
theorem k4_moment (d : ℕ) (hd : 4 ≤ d) (O : Module.End ℂ (TensV d 4)) :
    momentOp O = ∑ π : Equiv.Perm (Fin 4), (coeff d O π) • permOp d π := by
  obtain ⟨c, hmom, hsys⟩ := weingarten_moment_haar O
  -- `c` solves the Weingarten system
  have hc_mem : c ∈ weingartenSolutionSet d 4 O := hsys
  -- so does the notebook coefficient vector
  have hcoeff_mem : (coeff d O) ∈ weingartenSolutionSet d 4 O := coeff_mem_solutionSet d hd O
  -- uniqueness of the solution for `4 ≤ d`
  obtain ⟨c0, _hc0, huniq⟩ := weingarten_solution_unique hd O
  have h1 : c = c0 := huniq c hc_mem
  have h2 : coeff d O = c0 := huniq (coeff d O) hcoeff_mem
  have hcc : c = coeff d O := by rw [h1, h2]
  rw [hmom, hcc]
end SchurWeyl.K4
