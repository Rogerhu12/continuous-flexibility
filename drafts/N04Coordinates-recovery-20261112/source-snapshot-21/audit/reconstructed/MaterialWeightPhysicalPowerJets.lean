import ContinuousFlexibility.Analysis.MaterialOrdinaryJets
import ContinuousFlexibility.Analysis.N07aMaterialPowerJets

/-!
# Actual physical derivatives of material height and material powers

The genuine material-coordinate power bounds retain their weight. The
actual radial expansion converts them to ordinary physical derivatives
with a coefficient power of E0, before any component or sample is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- A selector for the two actual material weights, without replacing
either function or its underlying material data. -/
def materialHMWeight (T : MaterialData) (useM : Bool) : ℝ → ℝ :=
  if useM then T.M else T.H

theorem materialHMWeight_pos {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (useM : Bool) {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    0 < materialHMWeight T useM r := by
  cases useM with
  | false => exact (hT.2.1 r hr).2.1
  | true => exact zero_lt_one.trans_le (hT.2.1 r hr).2.2.2

theorem materialHMWeight_contDiffOn {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (useM : Bool) :
    ContDiffOn ℝ ∞ (materialHMWeight T useM) (Ioo D.a D.b) := by
  cases useM with
  | false => exact hT.1 T.H (by simp)
  | true => exact hT.1 T.M (by simp)

/-- The exponent gamma is unchanged. The extra factor is an actual E0
power from the supplied radial material expansion, not an M loss. -/
theorem materialHMWeight_rpow_physical_jet_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (useM : Bool) (γ : ℝ) (n : ℕ) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv n (fun t => materialHMWeight T useM t ^ γ) r| ≤
        B * materialHMWeight T useM r ^ γ * T.E0 r ^ A := by
  let w := materialHMWeight T useM
  let f : ℝ → ℝ := fun r => w r ^ γ
  have hw (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < w r :=
    materialHMWeight_pos hT useM hr
  have hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b) :=
    (materialHMWeight_contDiffOn hT useM).rpow_const_of_ne (fun r hr => (hw r hr).ne')
  have hmaterial (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |iteratedDeriv j (fun t => f (T.radius t)) x| ≤ B * w (T.radius x) ^ γ := by
    cases useM with
    | false =>
      simpa only [f, w, materialHMWeight, Bool.false_eq_true, ite_false] using
        iteratedDeriv_materialH_rpow_bound hT γ j
    | true =>
      simpa only [f, w, materialHMWeight, ite_true] using
        n07a_iteratedDeriv_materialM_rpow_bound hT γ j
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, hinverse, _, _, _, _, _, hexpansion, _⟩ := hdata
  obtain ⟨c, _, ⟨C, A, hC, hA, hc⟩, hformula⟩ := hexpansion n
  choose B hB hbound using fun j : Fin (n + 1) => hmaterial j.val
  let K : ℝ := ∑ j : Fin (n + 1), C * B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => mul_nonneg hC (hB j))
  refine ⟨K, A, hK, hA, ?_⟩
  intro r hr
  have hmat (j : Fin (n + 1)) :
      |materialDerivativeIterate T j.val f r| ≤ B j * w r ^ γ := by
    have h := hbound j (T.rho r)
    rw [iteratedDeriv_comp_materialRadius hT hf, hinverse r hr] at h
    exact h
  change |iteratedDeriv n f r| ≤ K * w r ^ γ * T.E0 r ^ A
  rw [hformula f hf r hr]
  calc
    _ ≤ ∑ j : Fin (n + 1), |c j r * materialDerivativeIterate T j.val f r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (n + 1), (C * B j) * w r ^ γ * T.E0 r ^ A := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul (hc j r hr) (hmat j) (abs_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (hT.2.1 r hr).2.2.1.le _))).trans_eq (by ring)
    _ = K * w r ^ γ * T.E0 r ^ A := by
      rw [Finset.sum_mul, Finset.sum_mul]

end ContinuousFlexibility.Analysis
