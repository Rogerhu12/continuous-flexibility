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
  convert hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
    (measurableSet_Ioo.prod measurableSet_Ioo) using 1
  funext z
  simp only [tailFundamentalGreenKernel, Set.piecewise, Set.mem_prod]

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
  have hleft := IntegrableOn.integrable_indicator
    (hw.const_mul (u x / W)) measurableSet_Ioo
  have hright := IntegrableOn.integrable_indicator
    ((hu.integrableOn (s := Ico x b)).const_mul (w x / W)) measurableSet_Ico
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
    convert hpc.mul hwc using 1
    funext y
    simp only [Pi.mul_apply]
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
  · apply (show ContinuousAt (fun _ : ℝ => (0 : ℝ)) x from
      continuousAt_const).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, mul_zero]

theorem tail_integrable_source_product {a b : ℝ} {g ψ : ℝ → ℝ}
    (hg : ContinuousOn g (Ioo a b)) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioo a b) : Integrable (fun x => g x * ψ x) := by
  have hcompact : HasCompactSupport (fun x => g x * ψ x) := by
    convert hc.mul_left (f := g) using 1
    funext x
    simp only [Pi.mul_apply]
  exact (tail_continuous_source_product hg hψ hs).integrable_of_hasCompactSupport hcompact

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
      convert h using 1
      funext y
      simp only [tailFundamentalGreenSolve, Pi.mul_apply, Pi.add_apply])
    dsimp only [tailFundamentalGreenFlux]
    field_simp [hp₀, hW₀]
    ring
  · have h := (((hq.mul hA).add (hz.mul hB)).div_const W)
    apply HasDerivAt.congr_deriv (by
      convert h using 1
      funext y
      simp only [tailFundamentalGreenFlux, Pi.mul_apply, Pi.add_apply])
    dsimp only [tailFundamentalGreenSolve]
    field_simp [hW₀]
    linear_combination -(ψ x) * hW

theorem tailFundamentalGreenSolve_entrance {a b W : ℝ} {p w u ψ : ℝ → ℝ}
    (hw : w a = 0) : tailFundamentalGreenSolve a b W p w u ψ a = 0 := by
  simp only [tailFundamentalGreenSolve, intervalIntegral.integral_same, hw,
    mul_zero, zero_mul, zero_add, zero_div]

theorem continuousOn_tailFundamentalGreenSolve
    {a b W : ℝ} {p w u ψ : ℝ → ℝ}
    (hw : ContinuousOn w (Ico a b)) (hu : ContinuousOn u (Ico a b))
    (hwψ : Continuous (fun y => p y * w y * ψ y))
    (huψ : Continuous (fun y => p y * u y * ψ y)) :
    ContinuousOn (tailFundamentalGreenSolve a b W p w u ψ) (Ico a b) := by
  have hA : Continuous (fun x => ∫ t in a..x, p t * w t * ψ t) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hwψ.integral_hasStrictDerivAt a x).hasDerivAt.continuousAt)
  have hB : Continuous (fun x => ∫ t in x..b, p t * u t * ψ t) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (intervalIntegral.integral_hasDerivAt_left (huψ.intervalIntegrable x b)
      huψ.aestronglyMeasurable.stronglyMeasurableAtFilter huψ.continuousAt).continuousAt
  convert ((hu.mul hA.continuousOn).add (hw.mul hB.continuousOn)).div_const W using 1
  funext x
  simp only [tailFundamentalGreenSolve, Pi.mul_apply, Pi.add_apply]

/-- Beyond the source, the Green solution is exactly a multiple of the
natural solution, with no asymptotic error term. -/
theorem tailFundamentalGreenSolve_eq_mul_on_tail
    {a b c W : ℝ} {p w u ψ : ℝ → ℝ}
    (hwψ : Continuous (fun y => p y * w y * ψ y))
    (hψzero : ∀ y ∈ Icc c b, ψ y = 0) :
    EqOn (tailFundamentalGreenSolve a b W p w u ψ)
      (fun x => ((∫ y in a..c, p y * w y * ψ y) / W) * u x) (Ico c b) := by
  intro x hx
  have hleft : (∫ y in c..x, p y * w y * ψ y) = 0 := by
    calc
      _ = ∫ _y in c..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hx.1] at hy
        rw [hψzero y ⟨hy.1, hy.2.trans hx.2.le⟩, mul_zero]
      _ = 0 := by simp
  have hright : (∫ y in x..b, p y * u y * ψ y) = 0 := by
    calc
      _ = ∫ _y in x..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hx.2.le] at hy
        rw [hψzero y ⟨hx.1.trans hy.1, hy.2⟩, mul_zero]
      _ = 0 := by simp
  have hprimitive : (∫ y in a..x, p y * w y * ψ y) =
      ∫ y in a..c, p y * w y * ψ y := by
    simpa only [hleft, add_zero] using
      (intervalIntegral.integral_add_adjacent_intervals
        (hwψ.intervalIntegrable a c) (hwψ.intervalIntegrable c x)).symm
  rw [tailFundamentalGreenSolve, hprimitive, hright, mul_zero, add_zero]
  ring

/-- Compact regularity at the entrance and agreement with an `L²` tail
preserve weighted `L²` membership. The weighted measure need not be finite. -/
theorem tail_memLp_of_continuousOn_eq_mul_tail
    {T : DeepTailData} {U u : ℝ → ℝ} {c C : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ico T.entrance T.endpoint))
    (hp₀ : ∀ x ∈ Ico T.entrance T.endpoint, 0 < T.p x)
    (hU : ContinuousOn U (Ico T.entrance T.endpoint))
    (hc : c ∈ Ioo T.entrance T.endpoint)
    (hu : MemLp u 2 (deepTailMeasure T))
    (heq : EqOn U (fun x => C * u x) (Ico c T.endpoint)) :
    MemLp U 2 (deepTailMeasure T) := by
  have hp' := hp.mono Ioo_subset_Ico_self
  have hp₀' (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :=
    hp₀ x (Ioo_subset_Ico_self hx)
  have hmeas : AEStronglyMeasurable U (deepTailMeasure T) :=
    AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
      ((hU.mono Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo)
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  apply (tail_integrable_density_iff hp' hp₀' _).mpr
  have hsub : Icc T.entrance c ⊆ Ico T.entrance T.endpoint :=
    fun _ hx => ⟨hx.1, hx.2.trans_lt hc.2⟩
  have hcont : ContinuousOn (fun x => T.p x * U x ^ 2) (Icc T.entrance c) := by
    convert (hp.continuousOn.mono hsub).mul ((hU.mono hsub).pow 2) using 1
    funext x
    simp only [Pi.mul_apply]
  have hleft := hcont.integrableOn_Icc
  have hCu := hu.const_mul C
  have hright₀ := (tail_integrable_density_iff hp' hp₀' _).mp
    ((memLp_two_iff_integrable_sq hCu.aestronglyMeasurable).mp hCu)
  have hright : IntegrableOn (fun x => T.p x * U x ^ 2) (Ico c T.endpoint) := by
    apply (hright₀.mono_set (fun x hx => ⟨hc.1.trans_le hx.1, hx.2⟩)).congr_fun
      _ measurableSet_Ico
    intro x hx
    dsimp only
    rw [heq hx]
  apply (hleft.union hright).mono_set
  intro x hx
  by_cases hxc : x ≤ c
  · exact Or.inl ⟨hx.1.le, hxc⟩
  · exact Or.inr ⟨(not_le.mp hxc).le, hx.2⟩

theorem tail_test_vanishes_on_final_interval {a b : ℝ} {ψ : ℝ → ℝ}
    (hab : a < b) (hs : tsupport ψ ⊆ Ioo a b) :
    ∃ c ∈ Ioo a b, ∀ y ∈ Icc c b, ψ y = 0 := by
  have hb : b ∉ tsupport ψ := fun h => (lt_irrefl b) (hs h).2
  have hzero : ∀ᶠ y in 𝓝[<] b, ψ y = 0 := by
    simpa only [Pi.zero_apply] using
      (notMem_tsupport_iff_eventuallyEq.mp hb).filter_mono nhdsWithin_le_nhds
  obtain ⟨l, ⟨hal, hlb⟩, hz⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hab).mp hzero
  obtain ⟨c, hlc, hcb⟩ := exists_between hlb
  refine ⟨c, ⟨hal.trans_lt hlc, hcb⟩, ?_⟩
  intro y hy
  rcases lt_or_eq_of_le hy.2 with hyb | hyb
  · exact hz ⟨hlc.trans_le hy.1, hyb⟩
  · subst y
    exact Function.notMem_support.mp (fun h => hb ((subset_tsupport ψ) h))

/-- For a compact interior source the actual kernel gives a classical
weighted `L²` solution with zero entrance value. Only the right fundamental
solution is required to lie in the weighted Hilbert space. -/
theorem exists_tailFundamentalGreen_compact_solution
    {T : DeepTailData} {w u z q ψ : ℝ → ℝ} {W : ℝ}
    (hab : T.entrance < T.endpoint)
    (hp : ContDiffOn ℝ ∞ T.p (Ico T.entrance T.endpoint))
    (hp₀ : ∀ x ∈ Ico T.entrance T.endpoint, 0 < T.p x)
    (hwc : ContinuousOn w (Ico T.entrance T.endpoint))
    (huc : ContinuousOn u (Ico T.entrance T.endpoint))
    (hw : TailFirstOrderSystem T.p T.Λ w z (Ioo T.entrance T.endpoint))
    (hu : TailFirstOrderSystem T.p T.Λ u q (Ioo T.entrance T.endpoint))
    (hw₀ : w T.entrance = 0) (hW₀ : W ≠ 0)
    (hW : ∀ x ∈ Ioo T.entrance T.endpoint, z x * u x - w x * q x = W)
    (huL2 : MemLp u 2 (deepTailMeasure T))
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ Ioo T.entrance T.endpoint) :
    ∃ U Q : ℝ → ℝ,
      EqOn U (fun x => ∫ y,
        tailFundamentalGreenKernel T.entrance T.endpoint w u W x y * ψ y
          ∂deepTailMeasure T) (Ioo T.entrance T.endpoint) ∧
      MemLp U 2 (deepTailMeasure T) ∧
      ContinuousOn U (Ico T.entrance T.endpoint) ∧ U T.entrance = 0 ∧
      ∀ x ∈ Ioo T.entrance T.endpoint,
        HasDerivAt U (Q x / T.p x) x ∧
        HasDerivAt Q (-T.p x * (ψ x + T.Λ * U x)) x := by
  have hp' := hp.mono Ioo_subset_Ico_self
  have hp₀' (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :=
    hp₀ x (Ioo_subset_Ico_self hx)
  have hpw : ContinuousOn (fun x => T.p x * w x) (Ioo T.entrance T.endpoint) := by
    convert hp'.continuousOn.mul (hwc.mono Ioo_subset_Ico_self) using 1
    funext x
    simp only [Pi.mul_apply]
  have hpu : ContinuousOn (fun x => T.p x * u x) (Ioo T.entrance T.endpoint) := by
    convert hp'.continuousOn.mul (huc.mono Ioo_subset_Ico_self) using 1
    funext x
    simp only [Pi.mul_apply]
  have hwψ := tail_continuous_source_product hpw hψ hsψ
  have huψ := tail_continuous_source_product hpu hψ hsψ
  have hwψi := tail_integrable_source_product hpw hψ hcψ hsψ
  have huψi := tail_integrable_source_product hpu hψ hcψ hsψ
  have hcont := continuousOn_tailFundamentalGreenSolve (W := W) hwc huc hwψ huψ
  obtain ⟨c, hc, hψzero⟩ := tail_test_vanishes_on_final_interval hab hsψ
  have htail := tailFundamentalGreenSolve_eq_mul_on_tail (a := T.entrance) (W := W)
    (u := u) hwψ hψzero
  refine ⟨tailFundamentalGreenSolve T.entrance T.endpoint W T.p w u ψ,
    tailFundamentalGreenFlux T.entrance T.endpoint W T.p w u z q ψ, ?_,
    tail_memLp_of_continuousOn_eq_mul_tail hp hp₀ hcont hc huL2 htail,
    hcont, tailFundamentalGreenSolve_entrance hw₀, ?_⟩
  · intro x hx
    exact (tailFundamentalGreenKernel_integral_eq_solve hp' hp₀' hwψi huψi hx).symm
  · intro x hx
    exact tailFundamentalGreenSolve_firstOrder (hp₀' x hx).ne' hW₀
      (hw x hx).1 (hu x hx).1 (hw x hx).2 (hu x hx).2 (hW x hx) hwψ huψ

end ContinuousFlexibility.Radial
