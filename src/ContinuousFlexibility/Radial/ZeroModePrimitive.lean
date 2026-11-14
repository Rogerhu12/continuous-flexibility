module

public import ContinuousFlexibility.Radial.Gauge
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The zero mode by two primitives

Section 6, equation `eq:rad-eq-rm49` of the manuscript
(`06-global-reference-inverse.tex`, lines 798-812): for a source `f₀` with
`∫ f₀ = 0` the zero mode of the radial operator `(w u')'` is solved by
`p₀(r) = ∫_{r₋}^r f₀` and `u₀(r) = -∫_r^{r₊} p₀ / w`.

This file treats the case of a continuous source supported in `[a', b']`
inside the open interval `(a, b)`, with `w` continuous and positive on
`(a, b)`; the general weighted case is obtained later by density.  It also
proves uniqueness of the zero channel on `(a, b)`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set intervalIntegral Filter
open scoped Topology

/-- The flux `p₀(r) = ∫_a^r f`. -/
def zeroModeFlux (a : ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t in a..r, f t

/-- The height `u₀(r) = -∫_r^b p₀ / w`. -/
def zeroModeHeight (a b : ℝ) (w f : ℝ → ℝ) (r : ℝ) : ℝ :=
  -∫ t in r..b, zeroModeFlux a f t / w t

theorem zeroModeFlux_hasDerivAt {a : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (r : ℝ) :
    HasDerivAt (zeroModeFlux a f) (f r) r := by
  unfold zeroModeFlux
  exact (hf.integral_hasStrictDerivAt a r).hasDerivAt

theorem source_zero_le {a' b' : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) {t : ℝ} (ht : t ≤ a') : f t = 0 := by
  rcases ht.lt_or_eq with h | h
  · exact hsupp t (fun hh => absurd hh.1 (not_le.2 h))
  · subst h
    by_contra hne
    have h1 : ∀ᶠ x in 𝓝 t, f x ≠ 0 := hf.continuousAt.eventually_ne hne
    have h2 : ∀ᶠ x in 𝓝[<] t, f x ≠ 0 ∧ x ∈ Iio t :=
      (h1.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin)
    obtain ⟨x, hx1, hx2⟩ := h2.exists
    exact hx1 (hsupp x (fun hh => absurd hh.1 (not_le.2 hx2)))

theorem source_zero_ge {a' b' : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) {t : ℝ} (ht : b' ≤ t) : f t = 0 := by
  rcases ht.lt_or_eq with h | h
  · exact hsupp t (fun hh => absurd hh.2 (not_le.2 h))
  · subst h
    by_contra hne
    have h1 : ∀ᶠ x in 𝓝 b', f x ≠ 0 := hf.continuousAt.eventually_ne hne
    have h2 : ∀ᶠ x in 𝓝[>] b', f x ≠ 0 ∧ x ∈ Ioi b' :=
      (h1.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin)
    obtain ⟨x, hx1, hx2⟩ := h2.exists
    exact hx1 (hsupp x (fun hh => absurd hh.2 (not_le.2 hx2)))

theorem zeroModeFlux_eq_zero_left {a a' b' r : ℝ} {f : ℝ → ℝ} (haa : a < a')
    (hf : Continuous f) (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) (hr : r ≤ a') :
    zeroModeFlux a f r = 0 := by
  unfold zeroModeFlux
  have h : ∫ t in a..r, f t = ∫ t in a..r, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show f t = 0
    apply source_zero_le hf hsupp
    rcases Set.mem_uIcc.1 ht with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith
  rw [h]; simp

theorem zeroModeFlux_eq_zero_right {a b' b r : ℝ} {a' : ℝ} {f : ℝ → ℝ} (hbb : b' < b)
    (hf : Continuous f) (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0)
    (hmean : ∫ t in a..b, f t = 0) (hr : b' ≤ r) :
    zeroModeFlux a f r = 0 := by
  unfold zeroModeFlux
  have h : ∫ t in r..b, f t = ∫ t in r..b, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show f t = 0
    apply source_zero_ge hf hsupp
    rcases Set.mem_uIcc.1 ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have h0 : ∫ t in r..b, f t = 0 := by rw [h]; simp
  have hadd := integral_add_adjacent_intervals (hf.intervalIntegrable (μ := MeasureTheory.volume) a r)
    (hf.intervalIntegrable (μ := MeasureTheory.volume) r b)
  linarith

/-- Item 1: the flux vanishes to the left of `a'` and to the right of `b'`. -/
theorem zeroModeFlux_zero_outside {a a' b' b : ℝ} {f : ℝ → ℝ} (haa : a < a') (hbb : b' < b)
    (hf : Continuous f) (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0)
    (hmean : ∫ t in a..b, f t = 0) {r : ℝ} (hr : r ∉ Ioo a' b') :
    zeroModeFlux a f r = 0 := by
  by_cases h : r ≤ a'
  · exact zeroModeFlux_eq_zero_left haa hf hsupp h
  · exact zeroModeFlux_eq_zero_right hbb hf hsupp hmean
      (by by_contra h2; exact hr ⟨not_le.1 h, not_le.1 h2⟩)

theorem zeroModeQuot_zero_left {a a' b' : ℝ} {w f : ℝ → ℝ} (haa : a < a')
    (hf : Continuous f) (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) {t : ℝ} (ht : t ≤ a') :
    zeroModeFlux a f t / w t = 0 := by
  rw [zeroModeFlux_eq_zero_left haa hf hsupp ht]; simp

theorem zeroModeQuot_zero_right {a a' b' b : ℝ} {w f : ℝ → ℝ} (hbb : b' < b)
    (hf : Continuous f) (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0)
    (hmean : ∫ t in a..b, f t = 0) {t : ℝ} (ht : b' ≤ t) :
    zeroModeFlux a f t / w t = 0 := by
  rw [zeroModeFlux_eq_zero_right hbb hf hsupp hmean ht]; simp

theorem zeroModeQuot_continuous {a a' b' b : ℝ} {w f : ℝ → ℝ}
    (hwc : ContinuousOn w (Ioo a b)) (hw : ∀ r ∈ Ioo a b, 0 < w r)
    (haa : a < a') (hbb : b' < b) (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) (hmean : ∫ t in a..b, f t = 0) :
    Continuous (fun t => zeroModeFlux a f t / w t) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t ∈ Ioo a b
  · have hp : ContinuousAt (zeroModeFlux a f) t := (zeroModeFlux_hasDerivAt hf t).continuousAt
    exact hp.div (hwc.continuousAt (Ioo_mem_nhds ht.1 ht.2)) (hw t ht).ne'
  · by_cases hta : t ≤ a
    · have hev : (fun t => zeroModeFlux a f t / w t) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds (lt_of_le_of_lt hta haa)] with s hs
        exact zeroModeQuot_zero_left haa hf hsupp (le_of_lt hs)
      exact continuousAt_const.congr hev.symm
    · have hb : b ≤ t := by
        by_contra h
        exact ht ⟨not_le.1 hta, not_le.1 h⟩
      have hev : (fun t => zeroModeFlux a f t / w t) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (lt_of_lt_of_le hbb hb)] with s hs
        exact zeroModeQuot_zero_right hbb hf hsupp hmean (le_of_lt hs)
      exact continuousAt_const.congr hev.symm

theorem zeroModeHeight_eq {a a' b' b : ℝ} {w f : ℝ → ℝ}
    (hwc : ContinuousOn w (Ioo a b)) (hw : ∀ r ∈ Ioo a b, 0 < w r)
    (haa : a < a') (hbb : b' < b) (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) (hmean : ∫ t in a..b, f t = 0) (r : ℝ) :
    zeroModeHeight a b w f r =
      (∫ t in a..r, zeroModeFlux a f t / w t) - ∫ t in a..b, zeroModeFlux a f t / w t := by
  have hg := zeroModeQuot_continuous hwc hw haa hbb hf hsupp hmean
  unfold zeroModeHeight
  have := integral_interval_sub_left (hg.intervalIntegrable (μ := MeasureTheory.volume) a b) (hg.intervalIntegrable (μ := MeasureTheory.volume) a r)
  linarith

/-- Item 2 (valid in fact at every `r`, by the vanishing outside `(a', b')`). -/
theorem zeroModeHeight_hasDerivAt {a a' b' b : ℝ} {w f : ℝ → ℝ}
    (hwc : ContinuousOn w (Ioo a b)) (hw : ∀ r ∈ Ioo a b, 0 < w r)
    (haa : a < a') (hbb : b' < b) (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) (hmean : ∫ t in a..b, f t = 0)
    {r : ℝ} (_hr : r ∈ Ioo a b) :
    HasDerivAt (zeroModeHeight a b w f) (zeroModeFlux a f r / w r) r := by
  have hg := zeroModeQuot_continuous hwc hw haa hbb hf hsupp hmean
  have h1 := (hg.integral_hasStrictDerivAt a r).hasDerivAt
  have h2 := h1.sub_const (∫ t in a..b, zeroModeFlux a f t / w t)
  have h3 : zeroModeHeight a b w f = fun u =>
      (∫ t in a..u, zeroModeFlux a f t / w t) - ∫ t in a..b, zeroModeFlux a f t / w t :=
    funext (zeroModeHeight_eq hwc hw haa hbb hf hsupp hmean)
  rw [h3]
  exact h2

/-- Item 3: flux identity. -/
theorem zeroModeHeight_flux {a a' b' b : ℝ} {w f : ℝ → ℝ}
    (hwc : ContinuousOn w (Ioo a b)) (hw : ∀ r ∈ Ioo a b, 0 < w r)
    (haa : a < a') (hbb : b' < b) (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) (hmean : ∫ t in a..b, f t = 0)
    {r : ℝ} (hr : r ∈ Ioo a b) :
    w r * deriv (zeroModeHeight a b w f) r = zeroModeFlux a f r := by
  rw [(zeroModeHeight_hasDerivAt hwc hw haa hbb hf hsupp hmean hr).deriv]
  have hne : w r ≠ 0 := (hw r hr).ne'
  field_simp

/-- Item 3: the equation `(w u₀')' = f`. -/
theorem zeroModeHeight_flux_deriv {a a' b' b : ℝ} {w f : ℝ → ℝ}
    (hwc : ContinuousOn w (Ioo a b)) (hw : ∀ r ∈ Ioo a b, 0 < w r)
    (haa : a < a') (hbb : b' < b) (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) (hmean : ∫ t in a..b, f t = 0)
    {r : ℝ} (hr : r ∈ Ioo a b) :
    deriv (fun t => w t * deriv (zeroModeHeight a b w f) t) r = f r := by
  have hev : (fun t => w t * deriv (zeroModeHeight a b w f) t) =ᶠ[𝓝 r]
      zeroModeFlux a f := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    exact zeroModeHeight_flux hwc hw haa hbb hf hsupp hmean ht
  rw [hev.deriv_eq]
  exact (zeroModeFlux_hasDerivAt hf r).deriv

/-- Item 3: the zero-mode Jacobi equation. -/
theorem zeroModeHeight_radialJacobi {a a' b' b : ℝ} {w f : ℝ → ℝ}
    (hwc : ContinuousOn w (Ioo a b)) (hw : ∀ r ∈ Ioo a b, 0 < w r)
    (haa : a < a') (hbb : b' < b) (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) (hmean : ∫ t in a..b, f t = 0)
    {r : ℝ} (hr : r ∈ Ioo a b) :
    radialJacobi 0 w (zeroModeHeight a b w f) r = f r := by
  unfold radialJacobi
  rw [zeroModeHeight_flux_deriv hwc hw haa hbb hf hsupp hmean hr]
  simp

/-- Item 4: the right height is zero. -/
theorem zeroModeHeight_eq_zero_right {a a' b' b : ℝ} {w f : ℝ → ℝ}
    (hbb : b' < b) (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) (hmean : ∫ t in a..b, f t = 0)
    {r : ℝ} (hr : r ∈ Icc b' b) :
    zeroModeHeight a b w f r = 0 := by
  unfold zeroModeHeight
  have h : ∫ t in r..b, zeroModeFlux a f t / w t = ∫ t in r..b, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show zeroModeFlux a f t / w t = 0
    have hb : b' ≤ t := by
      rcases Set.mem_uIcc.1 ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hr.1, hr.2]
    exact zeroModeQuot_zero_right hbb hf hsupp hmean hb
  rw [h]; simp

/-- Item 4: the left height is constant on `(a, a']`. -/
theorem zeroModeHeight_const_left {a a' b' b : ℝ} {w f : ℝ → ℝ}
    (hwc : ContinuousOn w (Ioo a b)) (hw : ∀ r ∈ Ioo a b, 0 < w r)
    (haa : a < a') (hbb : b' < b) (hf : Continuous f)
    (hsupp : ∀ r, r ∉ Icc a' b' → f r = 0) (hmean : ∫ t in a..b, f t = 0)
    {r : ℝ} (hr : r ∈ Ioc a a') :
    zeroModeHeight a b w f r = zeroModeHeight a b w f a' := by
  have hg := zeroModeQuot_continuous hwc hw haa hbb hf hsupp hmean
  unfold zeroModeHeight
  have h1 := integral_add_adjacent_intervals (hg.intervalIntegrable (μ := MeasureTheory.volume) r a')
    (hg.intervalIntegrable (μ := MeasureTheory.volume) a' b)
  have h : ∫ t in r..a', zeroModeFlux a f t / w t = ∫ t in r..a', (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show zeroModeFlux a f t / w t = 0
    have hb : t ≤ a' := by
      rcases Set.mem_uIcc.1 ht with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith [hr.2]
    exact zeroModeQuot_zero_left haa hf hsupp hb
  have h2 : ∫ t in r..a', zeroModeFlux a f t / w t = 0 := by rw [h]; simp
  linarith

/-- Item 5: the flux of a solution of the homogeneous zero-mode equation is constant. -/
theorem zeroMode_flux_const {a b : ℝ} {w u : ℝ → ℝ}
    (hflux : ∀ r ∈ Ioo a b, HasDerivAt (fun t => w t * deriv u t) 0 r) :
    ∃ c, ∀ r ∈ Ioo a b, w r * deriv u r = c := by
  have hdiff : DifferentiableOn ℝ (fun t => w t * deriv u t) (Ioo a b) :=
    fun r hr => (hflux r hr).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff
    (fun r hr => by rw [(hflux r hr).deriv]; rfl)
  exact ⟨c, hc⟩

/-- Item 5: vanishing derivative at one point forces vanishing derivative on the interval. -/
theorem zeroMode_deriv_eq_zero {a b : ℝ} {w u : ℝ → ℝ} (hw : ∀ r ∈ Ioo a b, 0 < w r)
    (hflux : ∀ r ∈ Ioo a b, HasDerivAt (fun t => w t * deriv u t) 0 r)
    {r₁ : ℝ} (hr₁ : r₁ ∈ Ioo a b) (hd : deriv u r₁ = 0) :
    ∀ r ∈ Ioo a b, deriv u r = 0 := by
  obtain ⟨c, hc⟩ := zeroMode_flux_const hflux
  have hc0 : c = 0 := by rw [← hc r₁ hr₁, hd, mul_zero]
  intro r hr
  have h := hc r hr
  rw [hc0] at h
  exact (mul_eq_zero.1 h).resolve_left (hw r hr).ne'

/-- Item 5: uniqueness of the zero channel on `(a, b)`. -/
theorem zeroMode_eq_zero {a b : ℝ} {w u : ℝ → ℝ} (hw : ∀ r ∈ Ioo a b, 0 < w r)
    (hu : DifferentiableOn ℝ u (Ioo a b))
    (hflux : ∀ r ∈ Ioo a b, HasDerivAt (fun t => w t * deriv u t) 0 r)
    {r₁ : ℝ} (hr₁ : r₁ ∈ Ioo a b) (hd : deriv u r₁ = 0) (h0 : u r₁ = 0) :
    ∀ r ∈ Ioo a b, u r = 0 := by
  have hd' := zeroMode_deriv_eq_zero hw hflux hr₁ hd
  intro r hr
  have h := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hu
    (fun r hr => by rw [hd' r hr]; rfl) hr hr₁
  exact h.trans h0

end ContinuousFlexibility.Radial
