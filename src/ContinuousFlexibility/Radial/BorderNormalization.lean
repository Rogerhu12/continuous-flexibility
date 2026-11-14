module

public import ContinuousFlexibility.Radial.Gauge
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Border-column pairing and normalization

Section 6 of the manuscript (`eq:ct-positive-shape`, `eq:rad-eq-ct9`): for a nonnegative nonzero
bump `χ` supported where `φ'/φ < 0`, the border pairing
`a_* = ∫ φ · L'_{2,w}[wχ]φ dr = ∫ wχ (-φ'² + 8φφ'/r - 4φ²/r²) dr` is negative, and
`χ_* = χ / a_*` gives `∫ (L'_{2,w}[wχ_*]φ) φ dr = 1`.

The support hypothesis is `Function.support χ ⊆ Set.Icc α' β'` with `α < α'` and `β' < β`.
-/

@[expose] public section

open scoped ContDiff
open MeasureTheory

namespace ContinuousFlexibility.Radial

noncomputable section

private theorem smooth_deriv {f : ℝ → ℝ} (h : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp h).2

private theorem smooth_hasDerivAt {f : ℝ → ℝ} (h : ContDiff ℝ ∞ f) (x : ℝ) :
    HasDerivAt f (deriv f x) x :=
  (h.differentiable (by simp) x).hasDerivAt

private theorem chi_zero {χ : ℝ → ℝ} {α' β' r : ℝ}
    (hsupp : Function.support χ ⊆ Set.Icc α' β') (hr : r ∉ Set.Icc α' β') : χ r = 0 := by
  by_contra h
  exact hr (hsupp (Function.mem_support.mpr h))

private theorem hasDerivAt_borderPrimitive {φ v g : ℝ → ℝ} {x φ' v' g' : ℝ} (hx : x ≠ 0)
    (hφ : HasDerivAt φ φ' x) (hv : HasDerivAt v v' x) (hg : HasDerivAt g g' x)
    (hgx : g x = v x * φ') :
    HasDerivAt (fun r => φ r * g r - 4 * v r * (φ r * φ r) / r)
      (φ x * (g' - 4 * v' / x * φ x) -
        v x * (-φ' ^ 2 + 8 * φ x * φ' / x - 4 * φ x ^ 2 / x ^ 2)) x := by
  have h := (hφ.mul hg).sub (((hv.const_mul 4).mul (hφ.mul hφ)).div (hasDerivAt_id' x) hx)
  refine h.congr_deriv ?_
  rw [hgx]
  simp only [Pi.mul_apply]
  field_simp
  ring

private def bpA (w φ χ : ℝ → ℝ) (r : ℝ) : ℝ := φ r * radialJacobi 4 (fun t => w t * χ t) φ r

private def bpB (w φ χ : ℝ → ℝ) (r : ℝ) : ℝ :=
  w r * χ r * (-(deriv φ r) ^ 2 + 8 * φ r * deriv φ r / r - 4 * φ r ^ 2 / r ^ 2)

private theorem continuousOn_bp {w φ χ : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) {α β : ℝ} (hα : 0 < α) :
    ContinuousOn (bpA w φ χ) (Set.Icc α β) ∧ ContinuousOn (bpB w φ χ) (Set.Icc α β) := by
  have hv : ContDiff ℝ ∞ (fun t => w t * χ t) := hw.mul hχ
  have hg : ContDiff ℝ ∞ (fun t => (w t * χ t) * deriv φ t) := hv.mul (smooth_deriv hφ)
  have hφc : Continuous φ := hφ.continuous
  have hdφ : Continuous (deriv φ) := (smooth_deriv hφ).continuous
  have hdv : Continuous (deriv fun t => w t * χ t) := (smooth_deriv hv).continuous
  have hdg : Continuous (deriv fun t => (w t * χ t) * deriv φ t) := (smooth_deriv hg).continuous
  have h0 : ∀ x ∈ Set.Icc α β, x ≠ 0 := fun x hx => (hα.trans_le hx.1).ne'
  have c1 : ContinuousOn (fun r => 4 * deriv (fun t => w t * χ t) r / r) (Set.Icc α β) :=
    (continuousOn_const.mul hdv.continuousOn).div continuousOn_id h0
  have c2 : ContinuousOn (fun r => 8 * φ r * deriv φ r / r) (Set.Icc α β) :=
    ((continuousOn_const.mul hφc.continuousOn).mul hdφ.continuousOn).div continuousOn_id h0
  have c3 : ContinuousOn (fun r => 4 * φ r ^ 2 / r ^ 2) (Set.Icc α β) :=
    (continuousOn_const.mul (hφc.pow 2).continuousOn).div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (h0 x hx))
  constructor
  · exact hφc.continuousOn.mul (hdg.continuousOn.sub (c1.mul hφc.continuousOn))
  · exact ((hw.continuous.mul hχ.continuous).continuousOn).mul
      (((hdφ.pow 2).neg.continuousOn.add c2).sub c3)

/-- Integration by parts for the border pairing. -/
theorem border_pairing_eq {w φ χ : ℝ → ℝ} {α β α' β' : ℝ}
    (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    (hα : 0 < α) (hαα' : α < α') (hββ' : β' < β) (hαβ : α ≤ β)
    (hsupp : Function.support χ ⊆ Set.Icc α' β') :
    ∫ r in α..β, φ r * radialJacobi 4 (fun t => w t * χ t) φ r =
      ∫ r in α..β, w r * χ r *
        (-(deriv φ r) ^ 2 + 8 * φ r * deriv φ r / r - 4 * φ r ^ 2 / r ^ 2) := by
  have hv : ContDiff ℝ ∞ (fun t => w t * χ t) := hw.mul hχ
  have hg : ContDiff ℝ ∞ (fun t => (w t * χ t) * deriv φ t) := hv.mul (smooth_deriv hφ)
  obtain ⟨hAc, hBc⟩ := continuousOn_bp (β := β) hw hφ hχ hα
  have hAi : IntervalIntegrable (bpA w φ χ) volume α β := hAc.intervalIntegrable_of_Icc hαβ
  have hBi : IntervalIntegrable (bpB w φ χ) volume α β := hBc.intervalIntegrable_of_Icc hαβ
  have hderiv : ∀ x ∈ Set.uIcc α β,
      HasDerivAt (fun r => φ r * ((w r * χ r) * deriv φ r) - 4 * (w r * χ r) * (φ r * φ r) / r)
        (bpA w φ χ x - bpB w φ χ x) x := by
    intro x hx
    rw [Set.uIcc_of_le hαβ] at hx
    exact hasDerivAt_borderPrimitive (hα.trans_le hx.1).ne' (smooth_hasDerivAt hφ x)
      (smooth_hasDerivAt hv x) (smooth_hasDerivAt hg x) rfl
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hAi.sub hBi)
  rw [intervalIntegral.integral_sub hAi hBi] at hint
  have hχα : χ α = 0 := chi_zero hsupp (fun h => absurd h.1 (not_le.mpr hαα'))
  have hχβ : χ β = 0 := chi_zero hsupp (fun h => absurd h.2 (not_le.mpr hββ'))
  have h2 : (∫ x in α..β, bpA w φ χ x) - ∫ x in α..β, bpB w φ χ x = 0 := by
    rw [hint]
    simp [hχα, hχβ]
  exact sub_eq_zero.mp h2

private theorem bracket_neg {p d r : ℝ} (hr : 0 < r) (h : p * d < 0) :
    -d ^ 2 + 8 * p * d / r - 4 * p ^ 2 / r ^ 2 < 0 := by
  have h1 : 8 * p * d / r < 0 := div_neg_of_neg_of_pos (by linarith) hr
  have h2 : 0 ≤ 4 * p ^ 2 / r ^ 2 := by positivity
  linarith [sq_nonneg d]

/-- The border pairing is negative. -/
theorem border_pairing_neg {w φ χ : ℝ → ℝ} {α β α' β' : ℝ}
    (hws : ContDiff ℝ ∞ w) (hφs : ContDiff ℝ ∞ φ) (hχs : ContDiff ℝ ∞ χ)
    (hα : 0 < α) (hαα' : α < α') (hββ' : β' < β)
    (hsupp : Function.support χ ⊆ Set.Icc α' β')
    (hχ : ∀ r, 0 ≤ χ r) (hχ₀ : ∃ r, 0 < χ r)
    (hw : ∀ r ∈ Set.Ioo α β, 0 < w r)
    (hφ : ∀ r ∈ Set.Ioo α β, φ r * deriv φ r < 0) :
    ∫ r in α..β, φ r * radialJacobi 4 (fun t => w t * χ t) φ r < 0 := by
  obtain ⟨c, hc⟩ := hχ₀
  have hcs : c ∈ Set.Icc α' β' := hsupp (Function.mem_support.mpr hc.ne')
  have hαβ : α < β := by linarith [hcs.1, hcs.2]
  have hcI : c ∈ Set.Ioo α β := ⟨by linarith [hcs.1], by linarith [hcs.2]⟩
  rw [border_pairing_eq hws hφs hχs hα hαα' hββ' hαβ.le hsupp]
  have hχβ : χ β = 0 := chi_zero hsupp (fun h => absurd h.2 (not_le.mpr hββ'))
  obtain ⟨_, hBc⟩ := continuousOn_bp (β := β) hws hφs hχs hα
  have hpos : 0 < ∫ r in α..β, -bpB w φ χ r := by
    refine intervalIntegral.integral_pos hαβ hBc.neg ?_ ?_
    · intro x hx
      by_cases hxb : x = β
      · rw [hxb]
        simp [bpB, hχβ]
      · have hxI : x ∈ Set.Ioo α β := ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩
        have hbr := bracket_neg (hα.trans hxI.1) (hφ x hxI)
        have : bpB w φ χ x ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hw x hxI).le (hχ x)) hbr.le
        linarith
    · refine ⟨c, ⟨hcI.1.le, hcI.2.le⟩, ?_⟩
      have hbr := bracket_neg (hα.trans hcI.1) (hφ c hcI)
      have : bpB w φ χ c < 0 := mul_neg_of_pos_of_neg (mul_pos (hw c hcI) hc) hbr
      linarith
  rw [intervalIntegral.integral_neg] at hpos
  have : (∫ r in α..β, bpB w φ χ r) < 0 := by linarith
  exact this

/-- Scaling the bump scales the border column. -/
theorem radialJacobi_border_div (w χ φ : ℝ → ℝ) (c r : ℝ) :
    radialJacobi 4 (fun t => w t * (χ t / c)) φ r =
      radialJacobi 4 (fun t => w t * χ t) φ r / c := by
  have e1 : (fun t => w t * (χ t / c)) = fun t => (w t * χ t) / c := funext fun t => by ring
  have e2 : (fun t => w t * (χ t / c) * deriv φ t) =
      fun t => w t * χ t * deriv φ t / c := funext fun t => by ring
  simp only [radialJacobi]
  rw [e1, e2, deriv_div_const, deriv_div_const]
  ring

/-- The border pairing `a_*`. -/
def borderPairing (w φ χ : ℝ → ℝ) (α β : ℝ) : ℝ :=
  ∫ r in α..β, φ r * radialJacobi 4 (fun t => w t * χ t) φ r

/-- With `χ_* = χ / a_*`, the border column pairs to one against `φ`. -/
theorem border_normalized {w φ χ : ℝ → ℝ} {α β α' β' : ℝ}
    (hws : ContDiff ℝ ∞ w) (hφs : ContDiff ℝ ∞ φ) (hχs : ContDiff ℝ ∞ χ)
    (hα : 0 < α) (hαα' : α < α') (hββ' : β' < β)
    (hsupp : Function.support χ ⊆ Set.Icc α' β')
    (hχ : ∀ r, 0 ≤ χ r) (hχ₀ : ∃ r, 0 < χ r)
    (hw : ∀ r ∈ Set.Ioo α β, 0 < w r)
    (hφ : ∀ r ∈ Set.Ioo α β, φ r * deriv φ r < 0) :
    ∫ r in α..β,
      radialJacobi 4 (fun t => w t * (χ t / borderPairing w φ χ α β)) φ r * φ r = 1 := by
  have hne : borderPairing w φ χ α β ≠ 0 :=
    (border_pairing_neg hws hφs hχs hα hαα' hββ' hsupp hχ hχ₀ hw hφ).ne
  calc ∫ r in α..β, radialJacobi 4 (fun t => w t * (χ t / borderPairing w φ χ α β)) φ r * φ r
      = ∫ r in α..β, (φ r * radialJacobi 4 (fun t => w t * χ t) φ r) /
          borderPairing w φ χ α β := by
        refine intervalIntegral.integral_congr (fun r _ => ?_)
        rw [radialJacobi_border_div]
        ring
    _ = (∫ r in α..β, φ r * radialJacobi 4 (fun t => w t * χ t) φ r) /
          borderPairing w φ χ α β := intervalIntegral.integral_div _ _
    _ = 1 := div_self hne

/-- The border column vanishes outside the closed support interval. -/
theorem border_column_support {w φ χ : ℝ → ℝ} {α' β' r : ℝ}
    (hsupp : Function.support χ ⊆ Set.Icc α' β') (hr : r ∉ Set.Icc α' β') :
    radialJacobi 4 (fun t => w t * χ t) φ r = 0 := by
  have hn : ∀ᶠ t in nhds r, t ∉ Set.Icc α' β' := isClosed_Icc.isOpen_compl.mem_nhds hr
  have hev : ∀ᶠ t in nhds r, χ t = 0 := hn.mono (fun t ht => chi_zero hsupp ht)
  have hv : (fun t => w t * χ t) =ᶠ[nhds r] fun _ => (0 : ℝ) :=
    hev.mono (fun t ht => by simp [ht])
  have hg : (fun t => w t * χ t * deriv φ t) =ᶠ[nhds r] fun _ => (0 : ℝ) :=
    hev.mono (fun t ht => by simp [ht])
  simp only [radialJacobi]
  rw [hg.deriv_eq, hv.deriv_eq]
  simp

end

end ContinuousFlexibility.Radial
