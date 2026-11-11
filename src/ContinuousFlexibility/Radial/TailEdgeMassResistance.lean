import ContinuousFlexibility.Radial.TailEdgeEnergy

/-!
# The diagonal Green integral in terms of mass and resistance

In resistance coordinates the lengths of the two pieces are the two
resistances. The diagonal integral is bounded by the corresponding
length times mass on each piece.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

theorem tailEdgeGreen_self_le_left {a b s : ℝ} (hab : a < b) (hs : s ∈ Icc a b) :
    tailEdgeGreen a b s s ≤ s - a := by
  rw [tailEdgeGreen_self]
  exact (div_le_iff₀ (sub_pos.mpr hab)).mpr
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hs.1 b) (sub_nonneg.mpr hs.1))

theorem tailEdgeGreen_self_le_right {a b s : ℝ} (hab : a < b) (hs : s ∈ Icc a b) :
    tailEdgeGreen a b s s ≤ b - s := by
  rw [tailEdgeGreen_self]
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  calc
    _ ≤ (b - a) * (b - s) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hs.2 a) (sub_nonneg.mpr hs.2)
    _ = _ := mul_comm _ _

/-- With (c) separating the mass interval from the resistance interval,
the two mass-resistance products bound the actual Green diagonal integral. -/
theorem tailEdge_green_diagonal_le_mass_resistance {a b c Λ : ℝ} {density : ℝ → ℝ}
    (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) (hΛ : 0 ≤ Λ)
    (hcont : ContinuousOn density (Icc a b)) (hpos : ∀ s ∈ Icc a b, 0 ≤ density s) :
    Λ * (∫ s in a..b, density s * tailEdgeGreen a b s s) ≤
      Λ * ((c - a) * (∫ s in a..c, density s) + (b - c) * ∫ s in c..b, density s) := by
  have hL : Icc a c ⊆ Icc a b := fun _ hs => ⟨hs.1, hs.2.trans hcb⟩
  have hR : Icc c b ⊆ Icc a b := fun _ hs => ⟨hac.trans hs.1, hs.2⟩
  have hG : Continuous (fun s => tailEdgeGreen a b s s) := by
    simp only [tailEdgeGreen_self]
    exact (((continuous_id.sub continuous_const).mul
      (continuous_const.sub continuous_id)).div_const _)
  have hGint : ContinuousOn (fun s => density s * tailEdgeGreen a b s s) (Icc a b) :=
    hcont.mul hG.continuousOn
  have hGL := (hGint.mono hL).intervalIntegrable_of_Icc (μ := volume) hac
  have hGR := (hGint.mono hR).intervalIntegrable_of_Icc (μ := volume) hcb
  have hCL : IntervalIntegrable (fun s => (c - a) * density s) volume a c :=
    (continuousOn_const.mul (hcont.mono hL)).intervalIntegrable_of_Icc hac
  have hCR : IntervalIntegrable (fun s => (b - c) * density s) volume c b :=
    (continuousOn_const.mul (hcont.mono hR)).intervalIntegrable_of_Icc hcb
  have hbl := intervalIntegral.integral_mono_on hac hGL hCL (fun s hs => by
    rw [mul_comm (c - a)]
    exact mul_le_mul_of_nonneg_left
      ((tailEdgeGreen_self_le_left hab (hL hs)).trans (sub_le_sub_right hs.2 a))
      (hpos s (hL hs)))
  have hbr := intervalIntegral.integral_mono_on hcb hGR hCR (fun s hs => by
    rw [mul_comm (b - c)]
    exact mul_le_mul_of_nonneg_left
      ((tailEdgeGreen_self_le_right hab (hR hs)).trans (sub_le_sub_left hs.1 b))
      (hpos s (hR hs)))
  rw [intervalIntegral.integral_const_mul] at hbl hbr
  rw [← intervalIntegral.integral_add_adjacent_intervals hGL hGR]
  exact mul_le_mul_of_nonneg_left (add_le_add hbl hbr) hΛ

end ContinuousFlexibility.Radial
