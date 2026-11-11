import ContinuousFlexibility.Radial.ModeWeakRegularity
import ContinuousFlexibility.Radial.ZeroModePrimitive

/-!
# Weak homogeneous zero modes on the whole open core

The compact-interval weak divergence theorem is applied to the actual
locally integrable field. Its representatives glue on the open interval.
Their fluxes are locally constant, hence the field is almost everywhere
an affine function of the genuine resistance primitive. No differentiability
of the original representative is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The genuine resistance coordinate based at an interior point. -/
def zeroModeResistance (c : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in c..x, 1 / w t

theorem zeroModeResistance_hasDerivAt {a b c : ℝ} {w : ℝ → ℝ}
    (hc : c ∈ Ioo a b) (hw : Continuous w)
    (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (zeroModeResistance c w) (1 / w x) x := by
  have hsub : uIcc c x ⊆ Ioo a b := by
    intro t ht
    rcases mem_uIcc.mp ht with ⟨hct, htx⟩ | ⟨hxt, htc⟩
    · exact ⟨hc.1.trans_le hct, htx.trans_lt hx.2⟩
    · exact ⟨hx.1.trans_le hxt, htc.trans_lt hc.2⟩
  have hi : IntervalIntegrable (fun t => 1 / w t) volume c x :=
    (continuousOn_const.div hw.continuousOn (fun t ht => hwn t (hsub ht))).intervalIntegrable
  exact intervalIntegral.integral_hasDerivAt_right hi
    (measurable_const.div hw.measurable).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_const.div hw.continuousAt (hwn x hx))

/-- Compact weak equations give one C1 representative on the full interval
whose actual flux has zero derivative at every interior point. -/
theorem zeroModeWeak_contDiffOn_representative
    {a b : ℝ} {u w : ℝ → ℝ}
    (hu : ∀ l h : ℝ, a < l → l < h → h < b →
      IntervalIntegrable u volume l h)
    (hw : ContDiff ℝ ∞ w) (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    (hweak : ∀ l h : ℝ, a < l → l < h → h < b →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ioo l h →
        (∫ x in l..h, u x * deriv (fun y => w y * deriv ψ y) x) = 0) :
    ∃ v : ℝ → ℝ,
      ContDiffOn ℝ 1 v (Ioo a b) ∧
      u =ᵐ[volume.restrict (Ioo a b)] v ∧
      ∀ x ∈ Ioo a b, HasDerivAt (fun y => w y * deriv v y) 0 x := by
  have hcompact (l h : ℝ) (hal : a < l) (hlh : l < h) (hhb : h < b) :
      ∃ v : ℝ → ℝ, ∃ C : ℝ, ContDiff ℝ 1 v ∧
        u =ᵐ[volume.restrict (Ioo l h)] v ∧
        ∀ x ∈ Icc l h, w x * deriv v x = C := by
    obtain ⟨v, C, hv, huv, hflux, _⟩ :=
      exists_contDiff_representative_of_weak_divergence hlh (hu l h hal hlh hhb)
        ((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).intervalIntegrable l h)
        hw (fun x hx => hwn x ⟨hal.trans_le hx.1, hx.2.trans_lt hhb⟩)
        (by simpa only [zero_mul, intervalIntegral.integral_zero] using hweak l h hal hlh hhb)
    exact ⟨v, C, hv, huv, by
      simpa only [intervalIntegral.integral_zero, add_zero] using hflux⟩
  have hlocal : ∀ x ∈ Ioo a b, ∃ V : Set ℝ,
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ioo a b ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 1 f ∧ u =ᵐ[volume.restrict V] f := by
    intro x hx
    let l := (a + x) / 2
    let h := (x + b) / 2
    have hal : a < l := by dsimp only [l]; linarith [hx.1]
    have hlx : l < x := by dsimp only [l]; linarith [hx.1]
    have hxh : x < h := by dsimp only [h]; linarith [hx.2]
    have hhb : h < b := by dsimp only [h]; linarith [hx.2]
    obtain ⟨v, C, hv, huv, _⟩ := hcompact l h hal (hlx.trans hxh) hhb
    exact ⟨Ioo l h, isOpen_Ioo, ⟨hlx, hxh⟩,
      fun y hy => ⟨hal.trans hy.1, hy.2.trans hhb⟩, v, hv, huv⟩
  obtain ⟨v, hv, huv⟩ := exists_contDiffOn_representative_of_locally hlocal
  refine ⟨v, hv, huv, ?_⟩
  intro x hx
  let l := (a + x) / 2
  let h := (x + b) / 2
  have hal : a < l := by dsimp only [l]; linarith [hx.1]
  have hlx : l < x := by dsimp only [l]; linarith [hx.1]
  have hxh : x < h := by dsimp only [h]; linarith [hx.2]
  have hhb : h < b := by dsimp only [h]; linarith [hx.2]
  have hsub : Ioo l h ⊆ Ioo a b :=
    fun y hy => ⟨hal.trans hy.1, hy.2.trans hhb⟩
  obtain ⟨r, C, hr, hur, hflux⟩ := hcompact l h hal (hlx.trans hxh) hhb
  have hvr : v =ᵐ[volume.restrict (Ioo l h)] r :=
    (ae_restrict_of_ae_restrict_of_subset hsub huv).symm.trans hur
  have hpoint : EqOn v r (Ioo l h) :=
    Measure.eqOn_open_of_ae_eq hvr isOpen_Ioo
      (hv.continuousOn.mono hsub) hr.continuous.continuousOn
  have heq : (fun y => w y * deriv v y) =ᶠ[𝓝 x] (fun _ => C) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo l h from ⟨hlx, hxh⟩)] with y hy
    have hd : deriv v y = deriv r y := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
      exact hpoint hz
    rw [hd]
    exact hflux y (mem_Icc_of_Ioo hy)
  exact (hasDerivAt_const x C).congr_of_eventuallyEq heq

/-- The homogeneous weak zero channel has exactly the two classical
degrees of freedom, even when the original field is only locally integrable. -/
theorem zeroModeWeak_ae_affine_resistance
    {a b : ℝ} (hab : a < b) {u w : ℝ → ℝ}
    (hu : ∀ l h : ℝ, a < l → l < h → h < b →
      IntervalIntegrable u volume l h)
    (hw : ContDiff ℝ ∞ w) (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    (hweak : ∀ l h : ℝ, a < l → l < h → h < b →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ioo l h →
        (∫ x in l..h, u x * deriv (fun y => w y * deriv ψ y) x) = 0) :
    ∃ c d : ℝ, u =ᵐ[volume.restrict (Ioo a b)]
      (fun x => c + d * zeroModeResistance ((a + b) / 2) w x) := by
  obtain ⟨v, hv, huv, hflux⟩ :=
    zeroModeWeak_contDiffOn_representative hu hw hwn hweak
  obtain ⟨d, hd⟩ := zeroMode_flux_const hflux
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hzero (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun y => v y - d * zeroModeResistance ((a + b) / 2) w y) 0 x := by
    have hdv : HasDerivAt v (deriv v x) x :=
      ((hv.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
    have hvalue : deriv v x = d * (1 / w x) := by
      rw [mul_one_div]
      exact (eq_div_iff (hwn x hx)).mpr (by simpa only [mul_comm] using hd x hx)
    have hz := hdv.sub ((zeroModeResistance_hasDerivAt hmid hw.continuous hwn hx).const_mul d)
    simpa only [hvalue, sub_self] using hz
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx => (hzero x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [(hzero x hx).deriv]; rfl)
  refine ⟨c, d, ?_⟩
  filter_upwards [huv, self_mem_ae_restrict measurableSet_Ioo] with x hx hxi
  have he := hc x hxi
  rw [hx]
  linarith only [he]

end ContinuousFlexibility.Radial
