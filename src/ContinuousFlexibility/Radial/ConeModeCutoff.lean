import ContinuousFlexibility.Radial.ConeSlopeAsymptotics

/-!
# A safe cutoff of an actual cone solution to a pure mode

The cutoff has support entirely in a region where the actual cone
solution does not vanish and its logarithmic slope has a small C1
error.  A product of retain weights removes the irrelevant cone pole
from the globally defined slope.  The reconstructed profile therefore
has positive derivative everywhere.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

structure ConeModeCutoff (s A B Q : ℝ) where
  mode : ℝ
  base : ℝ
  stop : ℝ
  slope : ℝ → ℝ
  mode_sq : mode ^ 2 = 4
  base_deep : Q < s * base
  stop_after : s * base < stop
  base_nonzero : coneModePair s A B base ≠ 0
  smooth : ContDiff ℝ ∞ slope
  below_four : ∀ y, slope y < 4
  positive : ∀ y, (3 / 4 : ℝ) ≤
    (slope y ^ 2 - slope y + deriv slope y) / (4 - slope y)
  slope_germ : slope =ᶠ[𝓝 base]
    fun y => deriv (coneModePair s A B) y / coneModePair s A B y
  pure : ∀ y, stop ≤ s * y → slope y = mode

private theorem exists_coneModeCutoff_dominant {s A B Q : ℝ}
    (hs : s ^ 2 = 4) (hA : A ≠ 0) :
    Nonempty (ConeModeCutoff s A B Q) := by
  have hsne : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hsabs : |s| = 2 := by
    have hsq : |s| ^ 2 = 4 := by simpa only [sq_abs] using hs
    nlinarith [abs_nonneg s]
  obtain ⟨C, hC, hCd⟩ := exists_connectorRetainWeight_derivative_bound
  have h4C : 0 ≤ 4 * C := by positivity
  obtain ⟨T, hT⟩ := exists_coneModeSlope_tail_control (s := s) (B := B) hA
    (connectorInterpolationTolerance_pos h4C)
  let L : ℝ := max T Q + 3
  let H : ℝ := L + 2
  let y₀ : ℝ := L / s
  have hsy : s * y₀ = L := by dsimp only [y₀]; field_simp [hsne]
  have hTL : T < L - 1 := by dsimp only [L]; linarith [le_max_left T Q]
  have hQL : Q < L := by dsimp only [L]; linarith [le_max_right T Q]
  let χ₀ : ℝ → ℝ := fun t =>
    connectorRetainWeight false L t * connectorRetainWeight true H t
  let χ : ℝ → ℝ := fun y => χ₀ (s * y)
  let k : ℝ → ℝ := connectorInterpolatedSlope χ (coneModeSlope s (B / A)) s
  have hχ₀ : ContDiff ℝ ∞ χ₀ :=
    (connectorRetainWeight_contDiff false L).mul (connectorRetainWeight_contDiff true H)
  have hχ : ContDiff ℝ ∞ χ :=
    hχ₀.comp (contDiff_const.mul contDiff_id)
  have hχBounds (y : ℝ) : 0 ≤ χ y ∧ χ y ≤ 1 := by
    obtain ⟨hl0, hl1⟩ := connectorRetainWeight_bounds false L (s * y)
    obtain ⟨hr0, hr1⟩ := connectorRetainWeight_bounds true H (s * y)
    exact ⟨mul_nonneg hl0 hr0, (mul_le_mul hl1 hr1 hr0 zero_le_one).trans_eq (one_mul 1)⟩
  have hχ₀d (t : ℝ) : |deriv χ₀ t| ≤ 2 * C := by
    have hdl := (connectorRetainWeight_contDiff false L).differentiable (by simp) t
    have hdr := (connectorRetainWeight_contDiff true H).differentiable (by simp) t
    have hd : HasDerivAt χ₀
        (deriv (connectorRetainWeight false L) t * connectorRetainWeight true H t +
          connectorRetainWeight false L t * deriv (connectorRetainWeight true H) t) t :=
      hdl.hasDerivAt.mul hdr.hasDerivAt
    have hl : |connectorRetainWeight false L t| ≤ 1 := by
      simpa only [abs_of_nonneg (connectorRetainWeight_bounds false L t).1] using
        (connectorRetainWeight_bounds false L t).2
    have hr : |connectorRetainWeight true H t| ≤ 1 := by
      simpa only [abs_of_nonneg (connectorRetainWeight_bounds true H t).1] using
        (connectorRetainWeight_bounds true H t).2
    rw [hd.deriv]
    calc
      _ ≤ |deriv (connectorRetainWeight false L) t * connectorRetainWeight true H t| +
          |connectorRetainWeight false L t * deriv (connectorRetainWeight true H) t| :=
        abs_add_le _ _
      _ = |deriv (connectorRetainWeight false L) t| * |connectorRetainWeight true H t| +
          |connectorRetainWeight false L t| * |deriv (connectorRetainWeight true H) t| := by
        rw [abs_mul, abs_mul]
      _ ≤ C * 1 + 1 * C :=
        add_le_add (mul_le_mul (hCd false L t) hr (abs_nonneg _) hC.le)
          (mul_le_mul hl (hCd true H t) (abs_nonneg _) zero_le_one)
      _ = 2 * C := by ring
  have hχd (y : ℝ) : |deriv χ y| ≤ 4 * C := by
    have hd : HasDerivAt χ (deriv χ₀ (s * y) * s) y :=
      ((hχ₀.differentiable (by simp) (s * y)).hasDerivAt.comp y (hasDerivAt_const_mul s))
    rw [hd.deriv, abs_mul, hsabs]
    nlinarith [hχ₀d (s * y)]
  have hcoord : Continuous (fun y : ℝ => s * y) := continuous_const.mul continuous_id
  have hzero (y : ℝ) (hy : s * y < L - 1) : χ =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [(isOpen_Iio.preimage hcoord).mem_nhds hy] with t ht
    dsimp only [χ, χ₀]
    rw [connectorRetainWeight_zero false L (s * t) ht.le, zero_mul]
  have hsmooth : ContDiff ℝ ∞ k := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : s * y < L - 1
    · exact contDiffAt_const.congr_of_eventuallyEq
        (connectorInterpolatedSlope_germ_of_zero (hzero y hy))
    · have hsafe : T ≤ s * y := hTL.le.trans (le_of_not_gt hy)
      have hd := hT y hsafe
      exact contDiffAt_const.add
        (hχ.contDiffAt.mul (hd.2.1.sub contDiffAt_const))
  have hpositive (y : ℝ) : k y < 4 ∧
      (3 / 4 : ℝ) ≤ (k y ^ 2 - k y + deriv k y) / (4 - k y) := by
    by_cases hy : s * y < L - 1
    · have hg : k =ᶠ[𝓝 y] fun _ => s :=
        connectorInterpolatedSlope_germ_of_zero (hzero y hy)
      have hv : k y = s := hg.eq_of_nhds
      have hd : deriv k y = 0 := by simpa only [deriv_const] using hg.deriv_eq
      simpa only [hv, hd] using
        connector_ratio_ge_three_quarters (a := s) (k := s) (d := 0) hs
          (by norm_num) (by norm_num)
    · have hsafe : T ≤ s * y := hTL.le.trans (le_of_not_gt hy)
      have hd := hT y hsafe
      exact connectorInterpolatedSlope_admissible
        (hχ.differentiable (by simp) y) (hd.2.1.differentiableAt (by simp))
        hs h4C (hχBounds y).1 (hχBounds y).2 (hχd y) hd.2.2.2.1 hd.2.2.2.2
  have hwindow : s * y₀ ∈ Ioo (L - 1 / 2) (H + 1 / 2) := by
    rw [hsy]
    constructor
    · linarith
    · change L < L + 2 + 1 / 2
      linarith
  have hone : χ =ᶠ[𝓝 y₀] fun _ => 1 := by
    filter_upwards [(isOpen_Ioo.preimage hcoord).mem_nhds hwindow] with y hy
    dsimp only [χ, χ₀]
    rw [connectorRetainWeight_one false L (s * y) hy.1.le,
      connectorRetainWeight_one true H (s * y) hy.2.le, one_mul]
  have hbaseSafe : T < s * y₀ := by rw [hsy]; linarith
  have hactual : coneModeSlope s (B / A) =ᶠ[𝓝 y₀]
      fun y => deriv (coneModePair s A B) y / coneModePair s A B y := by
    filter_upwards [(isOpen_Ioi.preimage hcoord).mem_nhds hbaseSafe] with y hy
    exact (hT y hy.le).2.2.1
  refine ⟨⟨s, y₀, H + 1, k, hs, ?_, ?_, (hT y₀ hbaseSafe.le).1,
    hsmooth, fun y => (hpositive y).1, fun y => (hpositive y).2,
    (connectorInterpolatedSlope_germ_of_one hone).trans hactual, ?_⟩⟩
  · rw [hsy]
    exact hQL
  · rw [hsy]
    dsimp only [H]
    linarith
  · intro y hy
    apply connectorInterpolatedSlope_eq_of_zero
    dsimp only [χ, χ₀]
    rw [connectorRetainWeight_zero true H (s * y) hy, mul_zero]

/-- The exceptional vanishing dominant coefficient is already a pure
mode.  The same signed-frequency theorem handles both inward directions. -/
theorem exists_coneModeCutoff {s A B Q : ℝ}
    (hs : s ^ 2 = 4) (hAB : (A, B) ≠ (0, 0)) :
    Nonempty (ConeModeCutoff s A B Q) := by
  by_cases hA : A = 0
  · subst A
    have hB : B ≠ 0 := by
      intro h
      apply hAB
      simp only [h]
    have hsne : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have hmode : (-s) ^ 2 = 4 := by simpa only [neg_sq] using hs
    have hnonzero (y : ℝ) : coneModePair s 0 B y ≠ 0 := by
      simp only [coneModePair, zero_mul, zero_add]
      exact mul_ne_zero hB (exp_pos _).ne'
    have hratio (y : ℝ) :
        deriv (coneModePair s 0 B) y / coneModePair s 0 B y = -s := by
      rw [(hasDerivAt_coneModePair s 0 B y).deriv]
      simp only [coneModePair, zero_mul, zero_sub, zero_add]
      field_simp [hB, (exp_pos (-s * y)).ne']
      <;> ring
    let y₀ : ℝ := (Q + 1) / s
    have hsy : s * y₀ = Q + 1 := by dsimp only [y₀]; field_simp [hsne]
    have hp : -s < 4 ∧ (3 / 4 : ℝ) ≤ ((-s) ^ 2 - (-s) + 0) / (4 - (-s)) :=
      connector_ratio_ge_three_quarters hmode (by norm_num) (by norm_num)
    refine ⟨⟨-s, y₀, Q + 2, fun _ => -s, hmode, ?_, ?_, hnonzero y₀,
      contDiff_const, fun _ => hp.1, ?_, ?_, fun _ _ => rfl⟩⟩
    · rw [hsy]
      linarith
    · rw [hsy]
      linarith
    · intro y
      simpa only [deriv_const] using hp.2
    · exact Eventually.of_forall fun y => (hratio y).symm
  · exact exists_coneModeCutoff_dominant hs hA

end ContinuousFlexibility.Radial
