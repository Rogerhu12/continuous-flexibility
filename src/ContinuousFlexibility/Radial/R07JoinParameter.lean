import ContinuousFlexibility.Radial.MorseJoinActualGerms

/-!
# Parameter identities for the actual positive joins

Only the endpoint values and the supported collar derivatives enter the
positive-join formula.  Thus the values on the actual join do not depend on
the arbitrary smooth extensions used to globalize the endpoint germs.

Adding constants to the two logarithmic endpoint profiles gives an explicit
affine formula.  This is the parameter dependence needed in R07: multiplying
both heights by the same positive number multiplies the whole join by that
number, while changing their ratio changes one fixed smooth coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

private theorem weighted_deriv_eqOn_of_germs {s t : Set ℝ} {q f g : ℝ → ℝ}
    (hg : ∀ x ∈ t, f =ᶠ[𝓝 x] g)
    (hs : ∀ x ∈ s, q x ≠ 0 → x ∈ t) :
    EqOn (fun x => q x * deriv f x) (fun x => q x * deriv g x) s := by
  intro x hx
  by_cases hq : q x = 0
  · rw [hq, zero_mul, zero_mul]
  · rw [(hg x (hs x hx hq)).deriv_eq]

private theorem morseJoin_supported_slopes_eqOn {a b hL hR : ℝ}
    {fL fR FL FR : ℝ → ℝ} (hhL : 0 < hL) (hhR : 0 < hR)
    (hLg : ∀ x ∈ Icc a (a + hL), FL =ᶠ[𝓝 x] fL)
    (hRg : ∀ x ∈ Icc (b - hR) b, FR =ᶠ[𝓝 x] fR) :
    EqOn (morseJoinLeftSlope a hL FL) (morseJoinLeftSlope a hL fL) (Icc a b) ∧
      EqOn (morseJoinRightSlope b hR FR) (morseJoinRightSlope b hR fR) (Icc a b) := by
  constructor
  · apply weighted_deriv_eqOn_of_germs hLg
    intro x hx hq
    exact ⟨hx.1, le_of_lt (lt_of_not_ge fun h => hq (morseJoinLeftWeight_zero hhL h))⟩
  · apply weighted_deriv_eqOn_of_germs hRg
    intro x hx hq
    exact ⟨le_of_lt (lt_of_not_ge fun h => hq (morseJoinRightWeight_zero hhR h)), hx.2⟩

/-- The join constant depends only on the prescribed endpoint collar germs. -/
theorem morseJoinConstant_congr_of_germs {a b hL hR : ℝ}
    {fL fR FL FR : ℝ → ℝ} (hab : a ≤ b) (hhL : 0 < hL) (hhR : 0 < hR)
    (hLg : ∀ x ∈ Icc a (a + hL), FL =ᶠ[𝓝 x] fL)
    (hRg : ∀ x ∈ Icc (b - hR) b, FR =ᶠ[𝓝 x] fR) :
    morseJoinConstant a b hL hR FL FR = morseJoinConstant a b hL hR fL fR := by
  obtain ⟨hsL, hsR⟩ := morseJoin_supported_slopes_eqOn hhL hhR hLg hRg
  have hLi : (∫ x in a..b, morseJoinLeftSlope a hL FL x) =
      ∫ x in a..b, morseJoinLeftSlope a hL fL x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hsL (by simpa only [uIcc_of_le hab] using hx)
  have hRi : (∫ x in a..b, morseJoinRightSlope b hR FR x) =
      ∫ x in a..b, morseJoinRightSlope b hR fR x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hsR (by simpa only [uIcc_of_le hab] using hx)
  have hLa : FL a = fL a :=
    (hLg a ⟨le_rfl, le_add_of_nonneg_right hhL.le⟩).eq_of_nhds
  have hRb : FR b = fR b :=
    (hRg b ⟨sub_le_self _ hhR.le, le_rfl⟩).eq_of_nhds
  simp only [morseJoinConstant, hLa, hRb, hLi, hRi]

/-- Changing the global extensions of the same collar germs does not change
the logarithmic slope at any point of the actual join. -/
theorem morseJoinSlope_eqOn_of_germs {a b hL hR : ℝ}
    {fL fR FL FR : ℝ → ℝ} (hab : a ≤ b) (hhL : 0 < hL) (hhR : 0 < hR)
    (hLg : ∀ x ∈ Icc a (a + hL), FL =ᶠ[𝓝 x] fL)
    (hRg : ∀ x ∈ Icc (b - hR) b, FR =ᶠ[𝓝 x] fR) :
    EqOn (morseJoinSlope a b hL hR FL FR)
      (morseJoinSlope a b hL hR fL fR) (Icc a b) := by
  obtain ⟨hsL, hsR⟩ := morseJoin_supported_slopes_eqOn hhL hhR hLg hRg
  intro x hx
  rw [morseJoinSlope, morseJoinSlope, hsL hx, hsR hx,
    morseJoinConstant_congr_of_germs hab hhL hhR hLg hRg]

/-- The logarithmic profile on the actual join is independent of all choices
of smooth extensions outside the two prescribed support collars. -/
theorem morseJoinLog_eqOn_of_germs {a b hL hR : ℝ}
    {fL fR FL FR : ℝ → ℝ} (hab : a ≤ b) (hhL : 0 < hL) (hhR : 0 < hR)
    (hLg : ∀ x ∈ Icc a (a + hL), FL =ᶠ[𝓝 x] fL)
    (hRg : ∀ x ∈ Icc (b - hR) b, FR =ᶠ[𝓝 x] fR) :
    EqOn (morseJoinLog a b hL hR FL FR)
      (morseJoinLog a b hL hR fL fR) (Icc a b) := by
  have hS := morseJoinSlope_eqOn_of_germs hab hhL hhR hLg hRg
  have hLa : FL a = fL a :=
    (hLg a ⟨le_rfl, le_add_of_nonneg_right hhL.le⟩).eq_of_nhds
  intro x hx
  have hi : (∫ t in a..x, morseJoinSlope a b hL hR FL FR t) =
      ∫ t in a..x, morseJoinSlope a b hL hR fL fR t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    exact hS ⟨ht.1, ht.2.trans hx.2⟩
  simp only [morseJoinLog, hLa, hi]

/-- The corresponding choice independence for the positive physical height. -/
theorem morseJoinProfile_eqOn_of_germs {a b hL hR : ℝ}
    {fL fR FL FR : ℝ → ℝ} (hab : a ≤ b) (hhL : 0 < hL) (hhR : 0 < hR)
    (hLg : ∀ x ∈ Icc a (a + hL), FL =ᶠ[𝓝 x] fL)
    (hRg : ∀ x ∈ Icc (b - hR) b, FR =ᶠ[𝓝 x] fR) :
    EqOn (morseJoinProfile a b hL hR FL FR)
      (morseJoinProfile a b hL hR fL fR) (Icc a b) := by
  intro x hx
  exact congrArg exp (morseJoinLog_eqOn_of_germs hab hhL hhR hLg hRg hx)

/-- The fixed smooth coordinate through which the relative endpoint height
enters the positive join. -/
def morseJoinHeightCoordinate (a b hL hR x : ℝ) : ℝ :=
  (∫ t in a..x, morseJoinRemainder a b hL hR t) / morseJoinDenominator a b hL hR

theorem contDiff_morseJoinHeightCoordinate (a b hL hR : ℝ) :
    ContDiff ℝ ∞ (morseJoinHeightCoordinate a b hL hR) := by
  have hq : ContDiff ℝ ∞ (morseJoinRemainder a b hL hR) :=
    (contDiff_const.sub (contDiff_morseJoinLeftWeight a hL)).sub
      (contDiff_morseJoinRightWeight b hR)
  have hd (x : ℝ) : HasDerivAt (morseJoinHeightCoordinate a b hL hR)
      (morseJoinRemainder a b hL hR x / morseJoinDenominator a b hL hR) x := by
    exact (intervalIntegral.integral_hasDerivAt_right (hq.continuous.intervalIntegrable a x)
      hq.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hq.continuous.continuousAt).div_const _
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt, ?_⟩
  rw [show deriv (morseJoinHeightCoordinate a b hL hR) =
    (fun x => morseJoinRemainder a b hL hR x / morseJoinDenominator a b hL hR) from
    funext fun x => (hd x).deriv]
  exact hq.div_const _

theorem morseJoinConstant_add_const (a b hL hR cL cR : ℝ) (fL fR : ℝ → ℝ) :
    morseJoinConstant a b hL hR (fun x => fL x + cL) (fun x => fR x + cR) =
      morseJoinConstant a b hL hR fL fR +
        (cR - cL) / morseJoinDenominator a b hL hR := by
  simp only [morseJoinConstant, morseJoinLeftSlope, morseJoinRightSlope, deriv_add_const]
  ring

theorem morseJoinSlope_add_const (a b hL hR cL cR : ℝ) (fL fR : ℝ → ℝ) (x : ℝ) :
    morseJoinSlope a b hL hR (fun y => fL y + cL) (fun y => fR y + cR) x =
      morseJoinSlope a b hL hR fL fR x +
        ((cR - cL) / morseJoinDenominator a b hL hR) *
          morseJoinRemainder a b hL hR x := by
  simp only [morseJoinSlope, morseJoinConstant_add_const,
    morseJoinLeftSlope, morseJoinRightSlope, deriv_add_const]
  ring

/-- Logarithmic endpoint shifts have affine dependence through one fixed
smooth coordinate, uniformly on the whole real line. -/
theorem morseJoinLog_add_const {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) (cL cR x : ℝ) :
    morseJoinLog a b hL hR (fun y => fL y + cL) (fun y => fR y + cR) x =
      morseJoinLog a b hL hR fL fR x + cL +
        (cR - cL) * morseJoinHeightCoordinate a b hL hR x := by
  have hS : Continuous (morseJoinSlope a b hL hR fL fR) :=
    (contDiff_morseJoinSlope hfL hfR).continuous
  have hq : Continuous (morseJoinRemainder a b hL hR) :=
    (continuous_const.sub (contDiff_morseJoinLeftWeight a hL).continuous).sub
      (contDiff_morseJoinRightWeight b hR).continuous
  simp only [morseJoinLog, morseJoinSlope_add_const]
  rw [intervalIntegral.integral_add (hS.intervalIntegrable a x)
      ((continuous_const.mul hq).intervalIntegrable a x),
    intervalIntegral.integral_const_mul]
  unfold morseJoinHeightCoordinate
  ring

/-- Equal logarithmic shifts leave every relative shape unchanged. -/
theorem morseJoinLog_add_same_const {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) (c x : ℝ) :
    morseJoinLog a b hL hR (fun y => fL y + c) (fun y => fR y + c) x =
      morseJoinLog a b hL hR fL fR x + c := by
  simpa only [sub_self, zero_mul, add_zero] using morseJoinLog_add_const hfL hfR c c x

/-- Scaling both physical endpoint heights by the same positive number
scales the complete join by exactly that number. -/
theorem morseJoinProfile_add_log_same {a b hL hR scale : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) (hs : 0 < scale) (x : ℝ) :
    morseJoinProfile a b hL hR (fun y => fL y + log scale) (fun y => fR y + log scale) x =
      scale * morseJoinProfile a b hL hR fL fR x := by
  rw [morseJoinProfile, morseJoinLog_add_same_const hfL hfR, exp_add, exp_log hs,
    morseJoinProfile, mul_comm]

/-- The full logarithmic join varies continuously with its two endpoint
log-heights and with its spatial coordinate. -/
theorem continuous_morseJoinLog_add_const {X : Type*} [TopologicalSpace X]
    {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR)
    {cL cR x : X → ℝ} (hCL : Continuous cL) (hCR : Continuous cR) (hx : Continuous x) :
    Continuous (fun z => morseJoinLog a b hL hR
      (fun y => fL y + cL z) (fun y => fR y + cR z) (x z)) := by
  have he : (fun z => morseJoinLog a b hL hR
      (fun y => fL y + cL z) (fun y => fR y + cR z) (x z)) =
      (fun z => morseJoinLog a b hL hR fL fR (x z) + cL z +
        (cR z - cL z) * morseJoinHeightCoordinate a b hL hR (x z)) :=
    funext fun z => morseJoinLog_add_const hfL hfR _ _ _
  rw [he]
  exact (((contDiff_morseJoinLog hfL hfR).continuous.comp hx).add hCL).add
    ((hCR.sub hCL).mul ((contDiff_morseJoinHeightCoordinate a b hL hR).continuous.comp hx))

/-- The corresponding joint continuity for the positive physical profile. -/
theorem continuous_morseJoinProfile_add_const {X : Type*} [TopologicalSpace X]
    {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR)
    {cL cR x : X → ℝ} (hCL : Continuous cL) (hCR : Continuous cR) (hx : Continuous x) :
    Continuous (fun z => morseJoinProfile a b hL hR
      (fun y => fL y + cL z) (fun y => fR y + cR z) (x z)) :=
  (continuous_morseJoinLog_add_const hfL hfR hCL hCR hx).exp

end ContinuousFlexibility.Radial
