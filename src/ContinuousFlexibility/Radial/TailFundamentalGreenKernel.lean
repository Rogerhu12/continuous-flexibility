import ContinuousFlexibility.Radial.TailClassicalRegularity
import ContinuousFlexibility.Radial.TailTestPairing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.LinearCombination

/-!+# The actual Green kernel from a pair of fundamental solutions

The left solution is evaluated at the smaller argument and the natural
solution at the larger argument. Zero extension outside the open interval
makes the kernel symmetric on all of the plane. Each row splits into a
compact left part and a multiple of the integrable natural solution.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def tailFundamentalGreenKernel (a b : ℝ) (w u : ℝ → ℝ) (W x y : ℝ) : ℝ :=
  if x ∈ Ioo a b ∧ y ∈ Ioo a b then w (min x y) * u (max x y) / W else 0

theorem tailFundamentalGreenKernel_eq {a b W x y : ℝ} {w u : ℝ → ℝ}
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    tailFundamentalGreenKernel a b w u W x y = w (min x y) * u (max x y) / W := by
  simp only [tailFundamentalGreenKernel, hx, hy, and_self, if_true]

theorem tailFundamentalGreenKernel_eq_zero_of_notMem_left
    {a b W x : ℝ} {w u : ℝ → ℝ} (hx : x ∉ Ioo a b) (y : ℝ) :
    tailFundamentalGreenKernel a b w u W x y = 0 := by
  simp only [tailFundamentalGreenKernel, hx, false_and, if_false]

theorem tailFundamentalGreenKernel_eq_zero_of_notMem_right
    {a b W y : ℝ} {w u : ℝ → ℝ} (hy : y ∉ Ioo a b) (x : ℝ) :
    tailFundamentalGreenKernel a b w u W x y = 0 := by
  simp only [tailFundamentalGreenKernel, hy, and_false, if_false]

theorem tailFundamentalGreenKernel_symm (a b W x y : ℝ) (w u : ℝ → ℝ) :
    tailFundamentalGreenKernel a b w u W x y =
      tailFundamentalGreenKernel a b w u W y x := by
  simp only [tailFundamentalGreenKernel, and_comm, min_comm, max_comm]

/-- Interior continuity of the two solutions gives joint measurability,
without any assumption about their values outside the interval. -/
theorem measurable_tailFundamentalGreenKernel {a b W : ℝ} {w u : ℝ → ℝ}
    (hw : ContinuousOn w (Ioo a b)) (hu : ContinuousOn u (Ioo a b)) :
    Measurable (fun z : ℝ × ℝ => tailFundamentalGreenKernel a b w u W z.1 z.2) := by
  classical
  have hmin : MapsTo (fun z : ℝ × ℝ => min z.1 z.2)
      (Ioo a b ×ˢ Ioo a b) (Ioo a b) := by
    intro z hz
    exact ⟨lt_min hz.1.1 hz.2.1, (min_le_left _ _).trans_lt hz.1.2⟩
  have hmax : MapsTo (fun z : ℝ × ℝ => max z.1 z.2)
      (Ioo a b ×ˢ Ioo a b) (Ioo a b) := by
    intro z hz
    exact ⟨hz.1.1.trans_le (le_max_left _ _), max_lt hz.1.2 hz.2.2⟩
  have hc : ContinuousOn (fun z : ℝ × ℝ => w (min z.1 z.2) * u (max z.1 z.2) / W)
      (Ioo a b ×ˢ Ioo a b) :=
    ((hw.comp (continuous_fst.min continuous_snd).continuousOn hmin).mul
      (hu.comp (continuous_fst.max continuous_snd).continuousOn hmax)).div_const W
  simpa only [tailFundamentalGreenKernel, Set.piecewise, Set.mem_prod] using
    hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
      (measurableSet_Ioo.prod measurableSet_Ioo)

/-- Exact row decomposition. The right interval includes the diagonal,
so this identity holds pointwise even for measures with atoms. -/
theorem tailFundamentalGreenKernel_row_split {a b W x : ℝ} {w u : ℝ → ℝ}
    (hx : x ∈ Ioo a b) (y : ℝ) :
    tailFundamentalGreenKernel a b w u W x y =
      (Ioo a x).indicator (fun t => (u x / W) * w t) y +
        (Ico x b).indicator (fun t => (w x / W) * u t) y := by
  classical
  by_cases hy : y ∈ Ioo a b
  · rw [tailFundamentalGreenKernel_eq hx hy]
    by_cases hyx : y < x
    · have hyl : y ∈ Ioo a x := ⟨hy.1, hyx⟩
      have hyr : y ∉ Ico x b := fun h => (not_le.mpr hyx) h.1
      rw [Set.indicator_of_mem hyl, Set.indicator_of_notMem hyr,
        min_eq_right hyx.le, max_eq_left hyx.le, add_zero]
      ring
    · have hxy : x ≤ y := not_lt.mp hyx
      have hyl : y ∉ Ioo a x := fun h => hyx h.2
      have hyr : y ∈ Ico x b := ⟨hxy, hy.2⟩
      rw [Set.indicator_of_notMem hyl, Set.indicator_of_mem hyr,
        min_eq_left hxy, max_eq_right hxy, zero_add]
      ring
  · have hyl : y ∉ Ioo a x := fun h => hy ⟨h.1, h.2.trans hx.2⟩
    have hyr : y ∉ Ico x b := fun h => hy ⟨hx.1.trans_le h.1, h.2⟩
    simp only [tailFundamentalGreenKernel, hy, and_false, if_false,
      Set.indicator_of_notMem hyl, Set.indicator_of_notMem hyr, zero_add]

/-- Only the left solution on a compact initial segment is needed for a
row integral; the entire right tail is controlled by the natural solution. -/
theorem tailFundamentalGreenKernel_integrable_row
    {μ : Measure ℝ} {a b W x : ℝ} {w u : ℝ → ℝ}
    (hx : x ∈ Ioo a b) (hw : IntegrableOn w (Ioo a x) μ) (hu : Integrable u μ) :
    Integrable (fun y => tailFundamentalGreenKernel a b w u W x y) μ := by
  have hleft := (hw.const_mul (u x / W)).integrable_indicator measurableSet_Ioo
  have hright := ((hu.integrableOn (s := Ico x b)).const_mul (w x / W)).integrable_indicator
    measurableSet_Ico
  apply (hleft.add hright).congr
  exact Eventually.of_forall fun y => (tailFundamentalGreenKernel_row_split hx y).symm

/-- A continuous density and a continuous left solution give a finite
weighted integral on every compact segment before the singular endpoint. -/
theorem tail_left_solution_integrableOn {T : DeepTailData} {w : ℝ → ℝ} {x : ℝ}
    (hp : ContinuousOn T.p (Ico T.entrance T.endpoint))
    (hp₀ : ∀ y ∈ Ico T.entrance T.endpoint, 0 ≤ T.p y)
    (hw : ContinuousOn w (Ico T.entrance T.endpoint))
    (hx : x ∈ Ioo T.entrance T.endpoint) :
    IntegrableOn w (Ioo T.entrance x) (deepTailMeasure T) := by
  have hsub : Icc T.entrance x ⊆ Ico T.entrance T.endpoint :=
    fun _ hy => ⟨hy.1, hy.2.trans_lt hx.2⟩
  have hsub' : Ioo T.entrance x ⊆ Ioo T.entrance T.endpoint :=
    fun _ hy => ⟨hy.1, hy.2.trans hx.2⟩
  have hpc := hp.mono hsub
  have hwc := hw.mono hsub
  have hcont : ContinuousOn (fun y => T.p y * w y) (Icc T.entrance x) := by
    simpa only [Pi.mul_apply] using hpc.mul hwc
  have hi : IntegrableOn (fun y => T.p y * w y) (Ioo T.entrance x) :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hpa : AEMeasurable (fun y => ENNReal.ofReal (T.p y))
      (volume.restrict (Ioo T.entrance x)) :=
    ((hpc.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo).ennreal_ofReal
  rw [IntegrableOn, deepTailMeasure, restrict_withDensity measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hsub',
    integrable_withDensity_iff_integrable_smul₀' hpa (by simp)]
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  simp only [ENNReal.toReal_ofReal (hp₀ y (hsub (Ioo_subset_Icc_self hy))), smul_eq_mul]

theorem tailFundamentalGreenKernel_weighted_integrable_row
    {T : DeepTailData} {w u : ℝ → ℝ} {W : ℝ}
    (hp : ContinuousOn T.p (Ico T.entrance T.endpoint))
    (hp₀ : ∀ y ∈ Ico T.entrance T.endpoint, 0 ≤ T.p y)
    (hw : ContinuousOn w (Ico T.entrance T.endpoint))
    (hu : Integrable u (deepTailMeasure T)) (x : ℝ) :
    Integrable (fun y => tailFundamentalGreenKernel T.entrance T.endpoint w u W x y)
      (deepTailMeasure T) := by
  by_cases hx : x ∈ Ioo T.entrance T.endpoint
  · exact tailFundamentalGreenKernel_integrable_row hx
      (tail_left_solution_integrableOn hp hp₀ hw hx) hu
  · have heq : (fun y => tailFundamentalGreenKernel T.entrance T.endpoint w u W x y) =
        fun _ => (0 : ℝ) := funext (tailFundamentalGreenKernel_eq_zero_of_notMem_left hx)
    rw [heq]
    exact integrable_zero _ _ _

/-- Bounded measurable sources are admissible in every row, including
smooth tests whose ordinary support approaches the singular endpoint. -/
theorem tailFundamentalGreenKernel_mul_integrable_of_bounded
    {T : DeepTailData} {w u ψ : ℝ → ℝ} {W C : ℝ}
    (hp : ContinuousOn T.p (Ico T.entrance T.endpoint))
    (hp₀ : ∀ y ∈ Ico T.entrance T.endpoint, 0 ≤ T.p y)
    (hw : ContinuousOn w (Ico T.entrance T.endpoint))
    (hu : Integrable u (deepTailMeasure T))
    (hψ : AEStronglyMeasurable ψ (deepTailMeasure T))
    (hbound : ∀ᵐ y ∂deepTailMeasure T, ‖ψ y‖ ≤ C) (x : ℝ) :
    Integrable (fun y => tailFundamentalGreenKernel T.entrance T.endpoint w u W x y * ψ y)
      (deepTailMeasure T) :=
  (tailFundamentalGreenKernel_weighted_integrable_row hp hp₀ hw hu x).mul_bdd hψ hbound

theorem tailFundamentalGreenKernel_mul_integrable_test
    {T : DeepTailData} {w u ψ : ℝ → ℝ} {W : ℝ}
    (hp : ContinuousOn T.p (Ico T.entrance T.endpoint))
    (hp₀ : ∀ y ∈ Ico T.entrance T.endpoint, 0 ≤ T.p y)
    (hw : ContinuousOn w (Ico T.entrance T.endpoint))
    (hu : Integrable u (deepTailMeasure T))
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (x : ℝ) :
    Integrable (fun y => tailFundamentalGreenKernel T.entrance T.endpoint w u W x y * ψ y)
      (deepTailMeasure T) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ
  exact tailFundamentalGreenKernel_mul_integrable_of_bounded hp hp₀ hw hu
    hψ.aestronglyMeasurable (Eventually.of_forall hC) x

/-- A continuous coefficient on the interval becomes globally continuous
after multiplication by a test supported compactly inside that interval. -/
theorem tail_continuous_source_product {a b : ℝ} {g ψ : ℝ → ℝ}
    (hg : ContinuousOn g (Ioo a b)) (hψ : Continuous ψ)
    (hs : tsupport ψ ⊆ Ioo a b) : Continuous (fun x => g x * ψ x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport ψ
  · exact (hg.continuousAt (isOpen_Ioo.mem_nhds (hs hx))).mul hψ.continuousAt
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, mul_zero]

def tailFundamentalGreenSolve (a b W : ℝ) (p w u ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (u x * (∫ t in a..x, p t * w t * ψ t) +
    w x * (∫ t in x..b, p t * u t * ψ t)) / W

def tailFundamentalGreenFlux (a b W : ℝ) (p w u z q ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (q x * (∫ t in a..x, p t * w t * ψ t) +
    z x * (∫ t in x..b, p t * u t * ψ t)) / W

/-- The actual weighted kernel integral equals its split primitive formula. -/
theorem tailFundamentalGreenKernel_integral_eq_solve
    {T : DeepTailData} {w u ψ : ℝ → ℝ} {W x : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hp₀ : ∀ y ∈ Ioo T.entrance T.endpoint, 0 < T.p y)
    (hwψ : Integrable (fun y => T.p y * w y * ψ y))
    (huψ : Integrable (fun y => T.p y * u y * ψ y))
    (hx : x ∈ Ioo T.entrance T.endpoint) :
    (∫ y, tailFundamentalGreenKernel T.entrance T.endpoint w u W x y * ψ y
      ∂deepTailMeasure T) =
      tailFundamentalGreenSolve T.entrance T.endpoint W T.p w u ψ x := by
  classical
  let A : ℝ → ℝ := fun y => (Ioo T.entrance x).indicator
    (fun t => (u x / W) * (T.p t * w t * ψ t)) y
  let B : ℝ → ℝ := fun y => (Ico x T.endpoint).indicator
    (fun t => (w x / W) * (T.p t * u t * ψ t)) y
  have hA : Integrable A := (hwψ.const_mul (u x / W)).indicator measurableSet_Ioo
  have hB : Integrable B := (huψ.const_mul (w x / W)).indicator measurableSet_Ico
  have hsplit (y : ℝ) :
      T.p y * (tailFundamentalGreenKernel T.entrance T.endpoint w u W x y * ψ y) =
        A y + B y := by
    rw [tailFundamentalGreenKernel_row_split hx]
    dsimp only [A, B]
    by_cases hl : y ∈ Ioo T.entrance x <;> by_cases hr : y ∈ Ico x T.endpoint <;>
      simp [Set.indicator, hl, hr] <;> ring
  rw [tail_integral_density hp hp₀]
  calc
    (∫ y in Ioo T.entrance T.endpoint,
        T.p y * (tailFundamentalGreenKernel T.entrance T.endpoint w u W x y * ψ y)) =
        ∫ y, T.p y * (tailFundamentalGreenKernel T.entrance T.endpoint w u W x y * ψ y) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        rw [tailFundamentalGreenKernel_eq_zero_of_notMem_right hy]
        simp only [zero_mul, mul_zero])
    _ = ∫ y, A y + B y := integral_congr_ae (Eventually.of_forall hsplit)
    _ = (∫ y, A y) + ∫ y, B y := integral_add hA hB
    _ = (u x / W) * (∫ y in T.entrance..x, T.p y * w y * ψ y) +
        (w x / W) * (∫ y in x..T.endpoint, T.p y * u y * ψ y) := by
      dsimp only [A, B]
      rw [integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ico,
        integral_const_mul, integral_const_mul,
        intervalIntegral.integral_of_le hx.1.le, intervalIntegral.integral_of_le hx.2.le,
        integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioc]
    _ = tailFundamentalGreenSolve T.entrance T.endpoint W T.p w u ψ x := by
      dsimp only [tailFundamentalGreenSolve]
      ring

/-- Differentiating the split formula cancels the two moving-boundary
terms, while its flux jump contributes exactly the prescribed source. -/
theorem tailFundamentalGreenSolve_firstOrder
    {a b Λ W x : ℝ} {p w u z q ψ : ℝ → ℝ}
    (hp₀ : p x ≠ 0) (hW₀ : W ≠ 0)
    (hw : HasDerivAt w (z x / p x) x)
    (hu : HasDerivAt u (q x / p x) x)
    (hz : HasDerivAt z (-Λ * p x * w x) x)
    (hq : HasDerivAt q (-Λ * p x * u x) x)
    (hW : z x * u x - w x * q x = W)
    (hwψ : Continuous (fun y => p y * w y * ψ y))
    (huψ : Continuous (fun y => p y * u y * ψ y)) :
    HasDerivAt (tailFundamentalGreenSolve a b W p w u ψ)
      (tailFundamentalGreenFlux a b W p w u z q ψ x / p x) x ∧
    HasDerivAt (tailFundamentalGreenFlux a b W p w u z q ψ)
      (-p x * (ψ x + Λ * tailFundamentalGreenSolve a b W p w u ψ x)) x := by
  have hA := (hwψ.integral_hasStrictDerivAt a x).hasDerivAt
  have hB := intervalIntegral.integral_hasDerivAt_left (huψ.intervalIntegrable x b)
    huψ.aestronglyMeasurable.stronglyMeasurableAtFilter huψ.continuousAt
  constructor
  · have h := (((hu.mul hA).add (hw.mul hB)).div_const W)
    apply HasDerivAt.congr_deriv (by
      simpa only [tailFundamentalGreenSolve, Pi.mul_apply, Pi.add_apply] using h)
    dsimp only [tailFundamentalGreenFlux]
    field_simp [hp₀, hW₀]
    ring
  · have h := (((hq.mul hA).add (hz.mul hB)).div_const W)
    apply HasDerivAt.congr_deriv (by
      simpa only [tailFundamentalGreenFlux, Pi.mul_apply, Pi.add_apply] using h)
    dsimp only [tailFundamentalGreenSolve]
    field_simp [hW₀]
    linear_combination -(p x * ψ x) * hW

theorem tailFundamentalGreenSolve_entrance {a b W : ℝ} {p w u ψ : ℝ → ℝ}
    (hw : w a = 0) : tailFundamentalGreenSolve a b W p w u ψ a = 0 := by
  simp only [tailFundamentalGreenSolve, intervalIntegral.integral_same, hw,
    mul_zero, zero_mul, zero_add, zero_div]

end ContinuousFlexibility.Radial
