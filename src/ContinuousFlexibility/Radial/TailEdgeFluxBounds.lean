import ContinuousFlexibility.Radial.TailEdgeFluxMatrix

/-!
# Quantitative bounds for the actual edge flux coefficients

The off-diagonal flux coefficient is controlled by the same Green diagonal
integral that controls the Poisson problem. No separate bound on the maximum
of the density is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

/-- A common weighted comparison for either Poisson height on any subedge.
The constants bound the affine height there, so the same lemma handles the
mass and gap pieces and both endpoints. -/
theorem tail_poisson_pairing_integral_bounds {l r low high δ : ℝ}
    {w h u : ℝ → ℝ} (hlr : l ≤ r) (hδ : δ < 1)
    (hw : ContinuousOn w (Icc l r)) (hh : ContinuousOn h (Icc l r))
    (hu : ContinuousOn u (Icc l r)) (hw₀ : ∀ s ∈ Icc l r, 0 ≤ w s)
    (hlow : 0 ≤ low) (hhigh : 0 ≤ high)
    (hb : ∀ s ∈ Icc l r, low ≤ h s ∧ h s ≤ high)
    (hp : ∀ s ∈ Icc l r, h s ≤ u s ∧ u s ≤ h s / (1 - δ)) :
    low ^ 2 * (∫ s in l..r, w s) ≤ ∫ s in l..r, w s * h s * u s ∧
      (∫ s in l..r, w s * h s * u s) ≤
        (high ^ 2 / (1 - δ)) * (∫ s in l..r, w s) := by
  have hden : 0 < 1 - δ := sub_pos.mpr hδ
  have hint := ((hw.mul hh).mul hu).intervalIntegrable_of_Icc hlr
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hlr
      ((continuousOn_const.mul hw).intervalIntegrable_of_Icc hlr) hint
    intro s hs
    have hprod : low ^ 2 ≤ h s * u s := by
      simpa only [pow_two] using mul_le_mul (hb s hs).1
        ((hb s hs).1.trans (hp s hs).1) hlow (hlow.trans (hb s hs).1)
    calc
      low ^ 2 * w s = w s * low ^ 2 := mul_comm _ _
      _ ≤ w s * (h s * u s) := mul_le_mul_of_nonneg_left hprod (hw₀ s hs)
      _ = _ := by ring
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hlr hint
      ((continuousOn_const.mul hw).intervalIntegrable_of_Icc hlr)
    intro s hs
    have hu₀ : 0 ≤ u s := (hlow.trans (hb s hs).1).trans (hp s hs).1
    have hprod : h s * u s ≤ high ^ 2 / (1 - δ) := by
      calc
        h s * u s ≤ high * (high / (1 - δ)) :=
          mul_le_mul (hb s hs).2 ((hp s hs).2.trans
            (div_le_div_of_nonneg_right (hb s hs).2 hden.le)) hu₀ hhigh
        _ = _ := by ring
    calc
      w s * h s * u s = w s * (h s * u s) := by ring
      _ ≤ w s * (high ^ 2 / (1 - δ)) := mul_le_mul_of_nonneg_left hprod (hw₀ s hs)
      _ = _ := mul_comm _ _

theorem tailEdgeLeftHeight_nonneg {a b s : ℝ} (hab : a < b)
    (hs : s ∈ Icc a b) : 0 ≤ tailEdgeLeftHeight a b s :=
  div_nonneg (sub_nonneg.mpr hs.2) (sub_pos.mpr hab).le

theorem tailEdgeRightHeight_nonneg {a b s : ℝ} (hab : a < b)
    (hs : s ∈ Icc a b) : 0 ≤ tailEdgeRightHeight a b s :=
  div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hab).le

theorem tailEdgeLeftHeight_mul_right (a b s : ℝ) :
    tailEdgeLeftHeight a b s * tailEdgeRightHeight a b s =
      tailEdgeGreen a b s s / (b - a) := by
  rw [tailEdgeGreen_self]
  dsimp only [tailEdgeLeftHeight, tailEdgeRightHeight]
  ring

/-- The off-diagonal coefficient lies between the free coefficient and its
Green-series majorant. The Poisson function is the actual right height. -/
theorem tailEdge_flux_coupling_bounds {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ s, 0 ≤ q s)
    (hδ : tailEdgeDiagonalSize hab q < 1) {u : ℝ → ℝ} (hu : Continuous u)
    (hheight : ∀ s ∈ Icc a b,
      tailEdgeRightHeight a b s ≤ u s ∧
        u s ≤ tailEdgeRightHeight a b s / (1 - tailEdgeDiagonalSize hab q)) :
    (b - a)⁻¹ ≤ (b - a)⁻¹ +
        (∫ s in a..b, tailEdgeLeftHeight a b s * IccExtend hab.le q s * u s) ∧
      (b - a)⁻¹ +
        (∫ s in a..b, tailEdgeLeftHeight a b s * IccExtend hab.le q s * u s) ≤
        1 / ((b - a) * (1 - tailEdgeDiagonalSize hab q)) := by
  let δ : ℝ := tailEdgeDiagonalSize hab q
  have hL : 0 < b - a := sub_pos.mpr hab
  have hden : 0 < 1 - δ := sub_pos.mpr hδ
  let f : ℝ → ℝ := fun s => tailEdgeLeftHeight a b s * IccExtend hab.le q s * u s
  let g : ℝ → ℝ := fun s => tailEdgeGreen a b s s * IccExtend hab.le q s
  have hqcont : Continuous (IccExtend hab.le q) := q.continuous.Icc_extend'
  have hlcont : Continuous (tailEdgeLeftHeight a b) :=
    (continuous_const.sub continuous_id).div_const _
  have hf : Continuous f := (hlcont.mul hqcont).mul hu
  have hg : Continuous g := by
    have hc : Continuous (fun s => tailEdgeGreen a b s s) := by
      simp only [tailEdgeGreen_self]
      exact ((continuous_id.sub continuous_const).mul
        (continuous_const.sub continuous_id)).div_const _
    exact hc.mul hqcont
  have hnonneg : 0 ≤ ∫ s in a..b, f s := by
    apply intervalIntegral.integral_nonneg hab.le
    intro s hs
    exact mul_nonneg
      (mul_nonneg (tailEdgeLeftHeight_nonneg hab hs)
        (by rw [IccExtend_of_mem hab.le q hs]; exact hq ⟨s, hs⟩))
      ((tailEdgeRightHeight_nonneg hab hs).trans (hheight s hs).1)
  have hupper : (∫ s in a..b, f s) ≤ δ / ((b - a) * (1 - δ)) := by
    have hpoint (s : ℝ) (hs : s ∈ Icc a b) :
        f s ≤ g s / ((b - a) * (1 - δ)) := by
      have hqs : 0 ≤ IccExtend hab.le q s := by
        rw [IccExtend_of_mem hab.le q hs]
        exact hq ⟨s, hs⟩
      calc
        f s ≤ (tailEdgeLeftHeight a b s * IccExtend hab.le q s) *
            (tailEdgeRightHeight a b s / (1 - δ)) :=
          mul_le_mul_of_nonneg_left (hheight s hs).2
            (mul_nonneg (tailEdgeLeftHeight_nonneg hab hs) hqs)
        _ = (tailEdgeLeftHeight a b s * tailEdgeRightHeight a b s) *
            IccExtend hab.le q s / (1 - δ) := by ring
        _ = g s / ((b - a) * (1 - δ)) := by
          rw [tailEdgeLeftHeight_mul_right]
          dsimp only [g]
          ring
    have hi := intervalIntegral.integral_mono_on hab.le (hf.intervalIntegrable a b)
      ((hg.div_const _).intervalIntegrable a b) hpoint
    rw [intervalIntegral.integral_div] at hi
    exact hi
  refine ⟨le_add_of_nonneg_right hnonneg, ?_⟩
  calc
    _ ≤ (b - a)⁻¹ + δ / ((b - a) * (1 - δ)) := add_le_add_left hupper _
    _ = 1 / ((b - a) * (1 - δ)) := by
      field_simp [hL.ne', hden.ne']
      ring

/-- A half-size Green diagonal gives a factor-two coupling comparison. -/
theorem tailEdge_flux_coupling_le_two {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ s, 0 ≤ q s)
    (hδ : tailEdgeDiagonalSize hab q ≤ 1 / 2) {u : ℝ → ℝ} (hu : Continuous u)
    (hheight : ∀ s ∈ Icc a b,
      tailEdgeRightHeight a b s ≤ u s ∧
        u s ≤ tailEdgeRightHeight a b s / (1 - tailEdgeDiagonalSize hab q)) :
    (b - a)⁻¹ +
        (∫ s in a..b, tailEdgeLeftHeight a b s * IccExtend hab.le q s * u s) ≤
      2 / (b - a) := by
  have hδ' : tailEdgeDiagonalSize hab q < 1 := lt_of_le_of_lt hδ (by norm_num)
  apply (tailEdge_flux_coupling_bounds hab hq hδ' hu hheight).2.trans
  apply (div_le_div_iff₀
    (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hδ')) (sub_pos.mpr hab)).mpr
  nlinarith [mul_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr hδ)]

end ContinuousFlexibility.Radial
