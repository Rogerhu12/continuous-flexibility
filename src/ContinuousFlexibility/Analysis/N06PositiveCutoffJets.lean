import ContinuousFlexibility.Analysis.PositiveEndpointCutoff
import ContinuousFlexibility.Analysis.N06RadialGeometryJets
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Uniform scaled jets of the actual endpoint cutoff

One fixed smooth bump is used on both ends of every positive piece.
Its derivatives have fixed bounds; affine rescaling introduces precisely
the inverse collar width to the corresponding power. In particular a
polynomial bound for that reciprocal controls all finite cutoff jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n06_boundaryTaylorCutoff_jet_bounded (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x,
      |iteratedDeriv n (boundaryTaylorCutoff : ℝ → ℝ) x| ≤ C := by
  have hs : ∀ k : ℕ, HasCompactSupport
      (iteratedDeriv k (boundaryTaylorCutoff : ℝ → ℝ)) := by
    intro k
    induction k with
    | zero => exact boundaryTaylorCutoff.hasCompactSupport
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hχ : ContDiff ℝ ∞ (boundaryTaylorCutoff : ℝ → ℝ) := boundaryTaylorCutoff.contDiff
  obtain ⟨C, hC⟩ := (hs n).exists_bound_of_continuous
    (hχ.continuous_iteratedDeriv n (by simp))
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro x
  have hx : |iteratedDeriv n (boundaryTaylorCutoff : ℝ → ℝ) x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_right _ _)

theorem n06_iteratedDeriv_positiveEndpointCutoff
    (n : ℕ) (c δ x : ℝ) :
    iteratedDeriv n (positiveEndpointCutoff c δ) x =
      δ⁻¹ ^ n * iteratedDeriv n (boundaryTaylorCutoff : ℝ → ℝ) ((x - c) / δ) := by
  have he : positiveEndpointCutoff c δ =
      fun t => (boundaryTaylorCutoff : ℝ → ℝ) (δ⁻¹ * (t - c)) := by
    funext t
    simp only [positiveEndpointCutoff, div_eq_mul_inv, mul_comm]
  have hχ : ContDiff ℝ (n : ℕ∞ω) (boundaryTaylorCutoff : ℝ → ℝ) :=
    boundaryTaylorCutoff.contDiff
  rw [he, iteratedDeriv_comp_sub_const n
    (fun t => (boundaryTaylorCutoff : ℝ → ℝ) (δ⁻¹ * t)) c,
    iteratedDeriv_comp_const_mul hχ δ⁻¹]
  simp only [div_eq_mul_inv, mul_comm δ⁻¹]

theorem n06_positiveEndpointCutoff_jet_bound (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ c δ x : ℝ, 0 < δ →
      |iteratedDeriv n (positiveEndpointCutoff c δ) x| ≤ C * δ⁻¹ ^ n := by
  obtain ⟨C, hC, hbound⟩ := n06_boundaryTaylorCutoff_jet_bounded n
  refine ⟨C, hC, ?_⟩
  intro c δ x hδ
  rw [n06_iteratedDeriv_positiveEndpointCutoff, abs_mul, abs_pow,
    abs_of_pos (inv_pos.mpr hδ)]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (hbound ((x - c) / δ))
      (pow_nonneg (inv_nonneg.mpr hδ.le) n)

/-- One fixed constant controls the actual value and first two
derivatives on every collar whose reciprocal is bounded by B. -/
theorem n06_positiveEndpointCutoff_twoJet_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ c δ B x : ℝ, 0 < δ → 1 ≤ B → δ⁻¹ ≤ B →
      N06ScalarJetTwoBound (positiveEndpointCutoff c δ) x (C * B ^ 2) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := n06_positiveEndpointCutoff_jet_bound 1
  obtain ⟨C₂, hC₂, hb₂⟩ := n06_positiveEndpointCutoff_jet_bound 2
  let C := max C₁ C₂
  have hC : 1 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro c δ B x hδ hB hδB
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  constructor
  · have hv : |positiveEndpointCutoff c δ x| ≤ 1 := by
      rw [abs_of_nonneg (positiveEndpointCutoff_nonneg c δ x)]
      exact positiveEndpointCutoff_le_one c δ x
    exact hv.trans (le_trans hB2 (le_mul_of_one_le_left (sq_nonneg B) hC))
  · have hder : |deriv (positiveEndpointCutoff c δ) x| ≤ C₁ * δ⁻¹ := by
      simpa only [iteratedDeriv_one, pow_one] using hb₁ c δ x hδ
    calc
      _ ≤ C₁ * δ⁻¹ := hder
      _ ≤ C * B := mul_le_mul (le_max_left _ _) hδB
        (inv_nonneg.mpr hδ.le) hC0
      _ ≤ C * B ^ 2 := mul_le_mul_of_nonneg_left hBB hC0
  · have hder : |deriv (deriv (positiveEndpointCutoff c δ)) x| ≤ C₂ * δ⁻¹ ^ 2 := by
      simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one, iteratedDeriv_zero] using hb₂ c δ x hδ
    exact hder.trans (mul_le_mul (le_max_right _ _)
      (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδB 2)
      (sq_nonneg δ⁻¹) hC0)

end ContinuousFlexibility.Analysis
