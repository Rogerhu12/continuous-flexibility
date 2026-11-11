import ContinuousFlexibility.Radial.TerminalMorseLiftEnergy

/-!
# Separation of the two actual terminal cutoff lifts

The left cutoff is zero beyond its layer and the right cutoff is zero
before its layer. The physical order of those layers therefore separates
their closed supports, their actual mixed energy, and their source pairing.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff

theorem terminalPhysicalCutoff_closed_support (rising : Bool) {a b : ℝ} (hab : a < b) :
    tsupport (terminalPhysicalCutoff rising a b) ⊆ if rising then Ici a else Iic b := by
  cases rising
  · apply closure_minimal ?_ isClosed_Iic
    intro x hx
    have hxb : x < b := by
      simpa only [Bool.false_eq_true, ite_false, mem_Iio] using
        terminalPhysicalCutoff_support false hab hx
    exact hxb.le
  · apply closure_minimal ?_ isClosed_Ici
    intro x hx
    have hax : a < x := by
      simpa only [eq_self_iff_true, ite_true, mem_Ioi] using
        terminalPhysicalCutoff_support true hab hx
    exact hax.le

theorem terminalPhysicalCutoff_opposite_disjoint {aₗ bₗ aᵣ bᵣ : ℝ}
    (hleft : aₗ < bₗ) (hright : aᵣ < bᵣ) (hsep : bₗ < aᵣ) :
    Disjoint (tsupport (terminalPhysicalCutoff false aₗ bₗ))
      (tsupport (terminalPhysicalCutoff true aᵣ bᵣ)) := by
  apply Set.disjoint_left.mpr
  intro x hl hr
  have hl' := terminalPhysicalCutoff_closed_support false hleft hl
  have hr' := terminalPhysicalCutoff_closed_support true hright hr
  exact (not_le_of_gt hsep) (hr'.trans hl')

theorem terminalCapLift_source_mixed_zero {lamLeft lamRight x : ℝ}
    {w χ η u v : ℝ → ℝ} (hsep : Disjoint (tsupport χ) (tsupport η)) :
    terminalCapLift lamLeft χ u x * terminalCapHilbertSource lamRight w η v x = 0 := by
  by_cases hL : terminalCapLift lamLeft χ u x = 0
  · rw [hL, zero_mul]
  · have hχ : x ∈ tsupport χ := subset_tsupport χ (terminalCapLift_support lamLeft χ u hL)
    have hF : terminalCapHilbertSource lamRight w η v x = 0 := by
      by_contra hF
      have hη : x ∈ tsupport η := tsupport_deriv_subset
        (terminalCapHilbertSource_support lamRight w η v hF)
      exact Set.disjoint_left.mp hsep hχ hη
    rw [hF, mul_zero]

theorem terminalCapLift_source_mixed_integral_zero (ν : Measure ℝ)
    {lamLeft lamRight : ℝ} {w χ η u v : ℝ → ℝ}
    (hsep : Disjoint (tsupport χ) (tsupport η)) :
    (∫ x, terminalCapLift lamLeft χ u x * terminalCapHilbertSource lamRight w η v x ∂ν) = 0 := by
  simp_rw [terminalCapLift_source_mixed_zero hsep]
  simp only [integral_zero]

/-- The two physical layer endpoints provide the separation; no
orthogonality or disjoint-support conclusion is assumed. -/
theorem terminalMorse_opposite_cutoffs_disjoint
    {Aₗ Bₗ sₗ Aᵣ Bᵣ sᵣ : ℝ} {rₗ rᵣ : ℝ → ℝ}
    (hBₗ : 0 < Bₗ) (hABₗ : 4 * Bₗ < Aₗ) (hsₗ : 0 < sₗ)
    (hrₗ : IsNormalizedMorseCell Aₗ Bₗ rₗ)
    (hBᵣ : 0 < Bᵣ) (hABᵣ : 4 * Bᵣ < Aᵣ) (hsᵣ : 0 < sᵣ)
    (hrᵣ : IsNormalizedMorseCell Aᵣ Bᵣ rᵣ)
    (hsep : terminalMorseLayerRight false Aₗ Bₗ sₗ rₗ <
      terminalMorseLayerLeft true Aᵣ Bᵣ sᵣ rᵣ) :
    Disjoint (tsupport (terminalMorsePhysicalCutoff false Aₗ Bₗ sₗ rₗ))
      (tsupport (terminalMorsePhysicalCutoff true Aᵣ Bᵣ sᵣ rᵣ)) :=
  terminalPhysicalCutoff_opposite_disjoint
    (terminalMorseLayer_order false hBₗ hABₗ hsₗ hrₗ)
    (terminalMorseLayer_order true hBᵣ hABᵣ hsᵣ hrᵣ) hsep

theorem terminalMorse_opposite_lifts_mixed_energy_zero
    {Aₗ Bₗ sₗ Aᵣ Bᵣ sᵣ lamLeft lamRight J a b : ℝ}
    {rₗ rᵣ w u v : ℝ → ℝ}
    (hBₗ : 0 < Bₗ) (hABₗ : 4 * Bₗ < Aₗ) (hsₗ : 0 < sₗ)
    (hrₗ : IsNormalizedMorseCell Aₗ Bₗ rₗ)
    (hBᵣ : 0 < Bᵣ) (hABᵣ : 4 * Bᵣ < Aᵣ) (hsᵣ : 0 < sᵣ)
    (hrᵣ : IsNormalizedMorseCell Aᵣ Bᵣ rᵣ)
    (hsep : terminalMorseLayerRight false Aₗ Bₗ sₗ rₗ <
      terminalMorseLayerLeft true Aᵣ Bᵣ sᵣ rᵣ) :
    (∫ x in a..b,
      w x * deriv (terminalCapLift lamLeft (terminalMorsePhysicalCutoff false Aₗ Bₗ sₗ rₗ) u) x *
        deriv (terminalCapLift lamRight (terminalMorsePhysicalCutoff true Aᵣ Bᵣ sᵣ rᵣ) v) x +
      J * deriv w x / x *
        terminalCapLift lamLeft (terminalMorsePhysicalCutoff false Aₗ Bₗ sₗ rₗ) u x *
        terminalCapLift lamRight (terminalMorsePhysicalCutoff true Aᵣ Bᵣ sᵣ rᵣ) v x) = 0 :=
  terminalCapLift_mixed_energy_integral_zero
    (terminalMorse_opposite_cutoffs_disjoint hBₗ hABₗ hsₗ hrₗ hBᵣ hABᵣ hsᵣ hrᵣ hsep)

end ContinuousFlexibility.Radial

