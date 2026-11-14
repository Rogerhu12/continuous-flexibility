module

public import ContinuousFlexibility.Analysis.N01aOpticalCutoff

/-!
# Interior support of the quantitative optical control

The cutoff is applied to the actual optical radicand. Since that radicand
vanishes at both turning points, extension by zero is smooth on the whole
line and has compact support strictly inside the component.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n01aOpticalRadicand (w : ℝ → ℝ) (r : ℝ) : ℝ :=
  -deriv w r / (r * w r)

theorem contDiffAt_n01aOpticalRadicand {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    {r : ℝ} (hr : r ≠ 0) (hwr : w r ≠ 0) :
    ContDiffAt ℝ ∞ (n01aOpticalRadicand w) r :=
  (contDiff_infty_iff_deriv.mp hw).2.contDiffAt.neg.div
    (contDiffAt_id.mul hw.contDiffAt) (mul_ne_zero hr hwr)

theorem n01aOpticalRadicand_zero {w : ℝ → ℝ} {r : ℝ} (hr : deriv w r = 0) :
    n01aOpticalRadicand w r = 0 := by
  simp only [n01aOpticalRadicand, hr, neg_zero, zero_div]

theorem n01aOpticalRadicand_pos {w : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hwr : 0 < w r) (hderiv : deriv w r < 0) :
    0 < n01aOpticalRadicand w r :=
  div_pos (neg_pos.mpr hderiv) (mul_pos hr hwr)

def n01aOpticalRawControl (w : ℝ → ℝ) (l h δ r : ℝ) : ℝ :=
  if r ∈ Ioo l h then r * n01aOpticalCutoff (n01aOpticalRadicand w r / δ) else 0

theorem n01aOpticalRawControl_eq {w : ℝ → ℝ} {l h δ r : ℝ}
    (hr : r ∈ Ioo l h) :
    n01aOpticalRawControl w l h δ r =
      r * n01aOpticalCutoff (n01aOpticalRadicand w r / δ) := by
  simp only [n01aOpticalRawControl, if_pos hr]

theorem n01aOpticalRawControl_zero {w : ℝ → ℝ} {l h δ r : ℝ}
    (hr : r ∉ Ioo l h) : n01aOpticalRawControl w l h δ r = 0 := by
  simp only [n01aOpticalRawControl, if_neg hr]

theorem n01aOpticalRawControl_eventuallyEq {w : ℝ → ℝ} {l h δ r : ℝ}
    (hr : r ∈ Ioo l h) :
    n01aOpticalRawControl w l h δ =ᶠ[𝓝 r]
      (fun x => x * n01aOpticalCutoff (n01aOpticalRadicand w x / δ)) := by
  filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
  exact n01aOpticalRawControl_eq hx

theorem n01aOpticalRawControl_eventually_zero {w : ℝ → ℝ} {l h δ r : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ x ∈ Icc l h, 0 < w x)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0)
    (hr : r ∉ Ioo l h) :
    n01aOpticalRawControl w l h δ =ᶠ[𝓝 r] (fun _ => 0) := by
  by_cases hr' : r ∈ Icc l h
  · have hzero : n01aOpticalRadicand w r = 0 := by
      rcases eq_or_lt_of_le hr'.1 with hrl | hlr
      · rw [← hrl]
        exact n01aOpticalRadicand_zero hrootL
      · have hrh : r = h := le_antisymm hr'.2
          (le_of_not_gt fun hh => hr ⟨hlr, hh⟩)
        rw [hrh]
        exact n01aOpticalRadicand_zero hrootR
    have hq := (contDiffAt_n01aOpticalRadicand hw
      (hl.trans_le hr'.1).ne' (hpos r hr').ne').continuousAt
    have hsmall : ∀ᶠ x in 𝓝 r, n01aOpticalRadicand w x / δ < 1 :=
      (hq.div_const δ).eventually_lt continuousAt_const
        (by simpa only [hzero, zero_div] using (zero_lt_one : (0 : ℝ) < 1))
    filter_upwards [hsmall] with x hx
    by_cases hx' : x ∈ Ioo l h
    · rw [n01aOpticalRawControl_eq hx', n01aOpticalCutoff_zero hx.le, mul_zero]
    · exact n01aOpticalRawControl_zero hx'
  · filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hr'] with x hx
    exact n01aOpticalRawControl_zero fun hi => hx (Ioo_subset_Icc_self hi)

theorem contDiff_n01aOpticalRawControl {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ x ∈ Icc l h, 0 < w x)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) :
    ContDiff ℝ ∞ (n01aOpticalRawControl w l h δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r ∈ Ioo l h
  · have hq := contDiffAt_n01aOpticalRadicand hw
      (hl.trans hr.1).ne' (hpos r (Ioo_subset_Icc_self hr)).ne'
    have hc : ContDiffAt ℝ ∞
        (fun x => x * n01aOpticalCutoff (n01aOpticalRadicand w x / δ)) r :=
      contDiffAt_id.mul (contDiff_n01aOpticalCutoff.contDiffAt.comp r (hq.div_const δ))
    exact hc.congr_of_eventuallyEq (n01aOpticalRawControl_eventuallyEq hr)
  · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) r).congr_of_eventuallyEq
      (n01aOpticalRawControl_eventually_zero hl hδ hw hpos hrootL hrootR hr)

theorem tsupport_n01aOpticalRawControl_subset {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ x ∈ Icc l h, 0 < w x)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) :
    tsupport (n01aOpticalRawControl w l h δ) ⊆ Ioo l h := by
  intro r hr
  by_contra hnot
  exact (notMem_tsupport_iff_eventuallyEq.mpr
    (n01aOpticalRawControl_eventually_zero hl hδ hw hpos hrootL hrootR hnot)) hr

theorem hasCompactSupport_n01aOpticalRawControl {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ x ∈ Icc l h, 0 < w x)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) :
    HasCompactSupport (n01aOpticalRawControl w l h δ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_n01aOpticalRawControl_subset hl hδ hw hpos hrootL hrootR).trans
      Ioo_subset_Icc_self)

theorem iteratedDeriv_n01aOpticalRawControl_eq {w : ℝ → ℝ} {l h δ r : ℝ}
    (hr : r ∈ Ioo l h) (s : ℕ) :
    iteratedDeriv s (n01aOpticalRawControl w l h δ) r =
      iteratedDeriv s (fun x => x * n01aOpticalCutoff (n01aOpticalRadicand w x / δ)) r :=
  (n01aOpticalRawControl_eventuallyEq hr).iteratedDeriv_eq s

theorem iteratedDeriv_n01aOpticalRawControl_zero {w : ℝ → ℝ} {l h δ r : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ x ∈ Icc l h, 0 < w x)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0)
    (hr : r ∉ Ioo l h) (s : ℕ) :
    iteratedDeriv s (n01aOpticalRawControl w l h δ) r = 0 := by
  rw [(n01aOpticalRawControl_eventually_zero hl hδ hw hpos hrootL hrootR hr).iteratedDeriv_eq s,
    iteratedDeriv_fun_const_zero]

private theorem exists_inner_interval_of_compact {K : Set ℝ} {l h : ℝ}
    (hlh : l < h) (hK : IsCompact K) (hsub : K ⊆ Ioo l h) :
    ∃ a b : ℝ, l < a ∧ a < b ∧ b < h ∧ K ⊆ Ioo a b := by
  rcases K.eq_empty_or_nonempty with hzero | hne
  · refine ⟨(2 * l + h) / 3, (l + 2 * h) / 3, by linarith,
      by linarith, by linarith, ?_⟩
    simp only [hzero, empty_subset]
  · obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
    have hlp := (hsub hp).1
    have hqh := (hsub hq).2
    have hpq : p ≤ q := hmin hq
    refine ⟨(l + p) / 2, (q + h) / 2, by linarith, by linarith,
      by linarith, fun r hr => ?_⟩
    have hpr : p ≤ r := hmin hr
    have hrq : r ≤ q := hmax hr
    constructor <;> linarith

/-- The exact first variation needs only compact support in the open
component; an auxiliary pair of inner endpoints is constructed. -/
theorem hasDerivAt_opticalTravel_of_compactInteriorSupport
    {w χ : ℝ → ℝ} {l h : ℝ} (hl : 0 < l) (hlh : l < h)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hsupp : tsupport χ ⊆ Ioo l h) :
    HasDerivAt (fun t => opticalTravel (opticalLogPerturbation w χ t) l h)
      (∫ r in l..h, -deriv χ r / (2 * r * opticalSpeed w r)) 0 := by
  obtain ⟨a, b, hla, hab, hbh, hs⟩ := exists_inner_interval_of_compact hlh hc hsupp
  exact hasDerivAt_opticalTravel_logPerturbation hl hla hab hbh hw hχ hpos hneg hs

end ContinuousFlexibility.Statements
