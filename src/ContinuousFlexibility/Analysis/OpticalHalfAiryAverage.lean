import ContinuousFlexibility.Analysis.N06AiryRadialGerm
import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization

/-!
# The actual Airy average on a complete optical half

Only the input jets on the physical interval are used in the integral
bounds. A smooth clamp in the value variable makes a positive square-root
representative without altering any germ on that interval. Its derivatives
away from those germs are never part of a quantitative estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

private theorem opticalHalf_scaled_mem {d x t : ℝ}
    (hx : x ∈ Icc (0 : ℝ) d) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * x ∈ Icc (0 : ℝ) d := by
  refine ⟨mul_nonneg ht.1 hx.1, ?_⟩
  have htx : t * x ≤ x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 hx.1
  exact htx.trans hx.2

/-- The normalized positive average preserves the actual interval's
value bounds; there is no hypothesis on values outside that interval. -/
theorem airyAverage_bounds_on_nonnegative_interval
    {c : ℝ → ℝ} (hc : Continuous c) {d x m M : ℝ}
    (hx : x ∈ Icc (0 : ℝ) d)
    (hb : ∀ y ∈ Icc (0 : ℝ) d, m ≤ c y ∧ c y ≤ M) :
    m ≤ n06AiryAverage c x ∧ n06AiryAverage c x ≤ M := by
  have hcI : IntervalIntegrable (fun t : ℝ => Real.sqrt t * c (t * x)) volume 0 1 :=
    (Real.continuous_sqrt.mul (hc.comp (continuous_id.mul_const x))).intervalIntegrable 0 1
  have hconst (v : ℝ) : IntervalIntegrable (fun t : ℝ => Real.sqrt t * v) volume 0 1 :=
    (Real.continuous_sqrt.mul_const v).intervalIntegrable 0 1
  have hmass (v : ℝ) :
      (3 / 2 : ℝ) * (∫ t in (0 : ℝ)..1, Real.sqrt t * v) = v := by
    rw [intervalIntegral.integral_mul_const, ← mul_assoc, n06_airy_weight_mass, one_mul]
  have hlo := intervalIntegral.integral_mono_on zero_le_one (hconst m) hcI
    (fun t ht => mul_le_mul_of_nonneg_left
      (hb (t * x) (opticalHalf_scaled_mem hx ht)).1 (Real.sqrt_nonneg t))
  have hhi := intervalIntegral.integral_mono_on zero_le_one hcI (hconst M)
    (fun t ht => mul_le_mul_of_nonneg_left
      (hb (t * x) (opticalHalf_scaled_mem hx ht)).2 (Real.sqrt_nonneg t))
  constructor
  · simpa only [hmass, n06AiryAverage] using
      mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 3 / 2)
  · simpa only [hmass, n06AiryAverage] using
      mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 3 / 2)

/-- Every genuine integral jet samples only the same closed half. The
factor two is independent of the interval length and derivative order. -/
theorem airyAverage_jet_bound_on_nonnegative_interval
    {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (n : ℕ) {d x M : ℝ}
    (hM : 0 ≤ M) (hx : x ∈ Icc (0 : ℝ) d)
    (hb : ∀ y ∈ Icc (0 : ℝ) d, |iteratedDeriv n c y| ≤ M) :
    |iteratedDeriv n (n06AiryAverage c) x| ≤ 2 * M := by
  rw [n06_iteratedDeriv_airyAverage hc n x, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hpoint (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      ‖Real.sqrt t * t ^ n * iteratedDeriv n c (t * x)‖ ≤ M := by
    have hs0 := Real.sqrt_nonneg t
    have hs1 : Real.sqrt t ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht.2
    have hp0 := pow_nonneg ht.1.le n
    have hp1 := pow_le_one₀ ht.1.le ht.2 (n := n)
    have hw : Real.sqrt t * t ^ n ≤ 1 := by
      simpa only [one_mul] using mul_le_mul hs1 hp1 hp0 zero_le_one
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg hp0]
    calc
      _ ≤ (Real.sqrt t * t ^ n) * M := mul_le_mul_of_nonneg_left
        (hb _ (opticalHalf_scaled_mem hx ⟨ht.1.le, ht.2⟩)) (mul_nonneg hs0 hp0)
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right hw hM
      _ = M := one_mul _
  have hi := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall hpoint)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 1)
  have hi' : |∫ t in (0 : ℝ)..1,
      Real.sqrt t * t ^ n * iteratedDeriv n c (t * x)| ≤ M := by
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const, sub_zero, one_smul] using hi
  exact (mul_le_mul_of_nonneg_left hi' (by norm_num : (0 : ℝ) ≤ 3 / 2)).trans
    (by nlinarith only [hM])

/-- A clamp of the values supplies a global positive representative of
the actual square root. Every germ whose input value lies in the displayed
range is preserved, including the two physical ends. -/
theorem exists_positive_sqrt_germ_extension
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {m M : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) :
    ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧
      (∀ x : ℝ, 0 < c x) ∧
      (∀ x : ℝ, Real.sqrt (m / 4) ≤ c x) ∧
      ∀ x : ℝ, m ≤ g x → g x ≤ M →
        c =ᶠ[𝓝 x] (fun y => Real.sqrt (g y)) := by
  have hab : m / 2 ≤ M + 1 := by linarith only [hm, hmM]
  have hδ : 0 < m / 4 := div_pos hm (by norm_num)
  let χ := circleFlowSmoothTimeClamp (m / 2) (M + 1) (m / 4) hab hδ
  let G : ℝ → ℝ := fun x => χ (g x)
  have hG : ContDiff ℝ ∞ G := (contDiff_circleFlowSmoothTimeClamp hab hδ).comp hg
  have hlower (x : ℝ) : m / 4 < G x := by
    have hx := (circleFlowSmoothTimeClamp_mem hab hδ (g x)).1
    change m / 2 - m / 4 < G x at hx
    linarith only [hx]
  have hpositive (x : ℝ) : 0 < G x := hδ.trans (hlower x)
  let c : ℝ → ℝ := fun x => Real.sqrt (G x)
  have hc : ContDiff ℝ ∞ c := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact hG.contDiffAt.sqrt (hpositive x).ne'
  refine ⟨c, hc, (fun x => Real.sqrt_pos.mpr (hpositive x)),
    (fun x => Real.sqrt_le_sqrt (hlower x).le), ?_⟩
  intro x hxlo hxhi
  have hx : g x ∈ Ioo (m / 2) (M + 1) := by
    constructor <;> linarith only [hm, hxlo, hxhi]
  filter_upwards [hg.continuous.continuousAt.preimage_mem_nhds
    (isOpen_Ioo.mem_nhds hx)] with y hy
  change Real.sqrt (χ (g y)) = Real.sqrt (g y)
  exact congrArg Real.sqrt (circleFlowSmoothTimeClamp_eq hab hδ ⟨hy.1.le, hy.2.le⟩)

/-- The averaged factor is the original optical integral after its exact
simple-zero factorization, not a different reference coordinate. -/
theorem opticalHalf_integral_eq_airyAverage
    {g c : ℝ → ℝ} {d x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) d)
    (heq : ∀ y ∈ Icc (0 : ℝ) d, c y = Real.sqrt (g y)) :
    (3 / 2 : ℝ) * (∫ y in (0 : ℝ)..x, Real.sqrt (y * g y)) =
      x ^ (3 / 2 : ℝ) * n06AiryAverage c x := by
  have hphysical : (∫ y in (0 : ℝ)..x, Real.sqrt (y * g y)) =
      ∫ y in (0 : ℝ)..x, Real.sqrt y * c y := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc (0 : ℝ) x := by simpa only [uIcc_of_le hx.1] using hy
    rw [heq y ⟨hy'.1, hy'.2.trans hx.2⟩, Real.sqrt_mul hy'.1]
  have hchange : x * (∫ t in (0 : ℝ)..1, Real.sqrt (t * x) * c (t * x)) =
      ∫ y in (0 : ℝ)..x, Real.sqrt y * c y := by
    simpa only [mul_zero, zero_add, mul_one, add_zero, smul_eq_mul, mul_comm] using
      intervalIntegral.smul_integral_comp_mul_add (fun y => Real.sqrt y * c y)
        (a := (0 : ℝ)) (b := 1) x 0
  have hscaled : (∫ t in (0 : ℝ)..1, Real.sqrt (t * x) * c (t * x)) =
      Real.sqrt x * (∫ t in (0 : ℝ)..1, Real.sqrt t * c (t * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    rw [Real.sqrt_mul ht'.1]
    ring
  have hpower : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hx.1 (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hphysical, ← hchange, hscaled, hpower]
  dsimp only [n06AiryAverage]
  ring

/-- The actual nonnegative Airy coordinate equals the smooth radial
formula on the whole half, including its physical root. -/
theorem opticalHalf_rootCoordinate_eq_airyRadialCoordinate
    {g c : ℝ → ℝ} {d x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) d)
    (heq : ∀ y ∈ Icc (0 : ℝ) d, c y = Real.sqrt (g y))
    (havg : 0 ≤ n06AiryAverage c x) :
    ((3 / 2 : ℝ) * (∫ y in (0 : ℝ)..x, Real.sqrt (y * g y))) ^ (2 / 3 : ℝ) =
      n06AiryRadialCoordinate c x := by
  rw [opticalHalf_integral_eq_airyAverage hx heq,
    Real.mul_rpow (Real.rpow_nonneg hx.1 _) havg, ← Real.rpow_mul hx.1]
  simp only [show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num,
    Real.rpow_one, n06AiryRadialCoordinate]

/-- One speed representative, chosen before any derivative order, gives
the actual integral coordinate on the entire closed half. Quantitative
jets use only the genuine square-root jets on that same physical half. -/
theorem exists_opticalHalfAiryAverage_of_factor_bounds
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {d m M : ℝ}
    (hd : 0 ≤ d) (hm : 0 < m)
    (hb : ∀ x ∈ Icc (0 : ℝ) d, m ≤ g x ∧ g x ≤ M) :
    ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧
      (∀ x : ℝ, 0 < c x) ∧
      (∀ x : ℝ, 0 < n06AiryAverage c x) ∧
      (∀ x ∈ Icc (0 : ℝ) d,
        c =ᶠ[𝓝 x] (fun y => Real.sqrt (g y)) ∧
        (Real.sqrt m ≤ n06AiryAverage c x ∧ n06AiryAverage c x ≤ Real.sqrt M) ∧
        ((3 / 2 : ℝ) * (∫ y in (0 : ℝ)..x, Real.sqrt (y * g y))) ^ (2 / 3 : ℝ) =
          n06AiryRadialCoordinate c x) ∧
      ∀ n : ℕ, ∀ B : ℝ, 0 ≤ B →
        (∀ y ∈ Icc (0 : ℝ) d,
          |iteratedDeriv n (fun t => Real.sqrt (g t)) y| ≤ B) →
        ∀ x ∈ Icc (0 : ℝ) d,
          |iteratedDeriv n (n06AiryAverage c) x| ≤ 2 * B := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) d := ⟨le_rfl, hd⟩
  obtain ⟨c, hc, hpos, hlower, hgerm⟩ :=
    exists_positive_sqrt_germ_extension hg hm ((hb 0 hzero).1.trans (hb 0 hzero).2)
  have hlocal (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      c =ᶠ[𝓝 x] (fun y => Real.sqrt (g y)) := hgerm x (hb x hx).1 (hb x hx).2
  have heq (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) : c x = Real.sqrt (g x) :=
    (hlocal x hx).self_of_nhds
  have hApos (x : ℝ) : 0 < n06AiryAverage c x :=
    (Real.sqrt_pos.mpr (show 0 < m / 4 from div_pos hm (by norm_num))).trans_le
      (n06_airyAverage_lower hc.continuous (Real.sqrt (m / 4)) hlower x)
  refine ⟨c, hc, hpos, hApos, ?_, ?_⟩
  · intro x hx
    refine ⟨hlocal x hx, ?_, opticalHalf_rootCoordinate_eq_airyRadialCoordinate hx heq (hApos x).le⟩
    apply airyAverage_bounds_on_nonnegative_interval hc.continuous hx
    intro y hy
    rw [heq y hy]
    exact ⟨Real.sqrt_le_sqrt (hb y hy).1, Real.sqrt_le_sqrt (hb y hy).2⟩
  · intro n B hB hj x hx
    apply airyAverage_jet_bound_on_nonnegative_interval hc n hB hx
    intro y hy
    rw [(hlocal y hy).iteratedDeriv_eq n]
    exact hj y hy

end ContinuousFlexibility.Analysis
