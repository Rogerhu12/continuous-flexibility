import ContinuousFlexibility.Radial.ReferenceRadialSmoothExtension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A genuine smooth left switch for the zero mode

The output cutoff is prescribed only inside endpoint neighborhoods. A
global transition supplies constant exterior values, while its difference
from that cutoff is compactly supported relative to the open radial core.
All positive derivatives and the actual zero-mode forcing are compactly
supported strictly inside the core.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem reference_deriv_support_of_constant_sides {g : ℝ → ℝ} {l h : ℝ}
    (hl : ∀ r, r ≤ l → g r = 1) (hh : ∀ r, h ≤ r → g r = 0) :
    tsupport (deriv g) ⊆ Icc l h := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  change deriv g r ≠ 0 at hr
  constructor
  · by_contra hn
    have hrl : r < l := lt_of_not_ge hn
    have he : g =ᶠ[𝓝 r] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hrl] with t ht
      exact hl t ht.le
    apply hr
    rw [he.deriv_eq]
    exact deriv_const r 1
  · by_contra hn
    have hhr : h < r := lt_of_not_ge hn
    have he : g =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hhr] with t ht
      exact hh t ht.le
    apply hr
    rw [he.deriv_eq]
    exact deriv_const r 0

theorem exists_referenceLeftSwitch {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∃ l h : ℝ, D.a < l ∧ l < h ∧ h < D.b ∧
        (∀ r, r ≤ l → g r = 1) ∧ (∀ r, h ≤ r → g r = 0)) ∧
      ReferenceRapid D (fun r => D.chiLeft r - g r) ∧
      (∀ n : ℕ, ReferenceRapid D (iteratedDeriv (n + 1) g)) ∧
      (∀ n : ℕ, ReferenceRapid D (iteratedDeriv n (radialJacobi 0 D.w g))) := by
  have hab : D.a < D.b := hD.choose_spec.1.2.1
  let l : ℝ := (2 * D.a + D.b) / 3
  let h : ℝ := (D.a + 2 * D.b) / 3
  have hal : D.a < l := by dsimp only [l]; linarith
  have hlh : l < h := by dsimp only [l, h]; linarith
  have hhb : h < D.b := by dsimp only [h]; linarith
  let g : ℝ → ℝ := fun r => 1 - smoothTransition ((r - l) / (h - l))
  have hg : ContDiff ℝ ∞ g :=
    contDiff_const.sub (smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const (h - l)))
  have hleft (r : ℝ) (hr : r ≤ l) : g r = 1 := by
    change 1 - smoothTransition ((r - l) / (h - l)) = 1
    rw [smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) (sub_pos.mpr hlh).le), sub_zero]
  have hright (r : ℝ) (hr : h ≤ r) : g r = 0 := by
    change 1 - smoothTransition ((r - l) / (h - l)) = 0
    rw [smoothTransition.one_of_one_le
      ((le_div_iff₀ (sub_pos.mpr hlh)).mpr (by linarith)), sub_self]
  have hdg : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hs : tsupport (deriv g) ⊆ Icc l h :=
    reference_deriv_support_of_constant_sides hleft hright
  have hc : HasCompactSupport (deriv g) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport (deriv g)) hs
  have hcore : Icc l h ⊆ radialCore D :=
    fun r hr => ⟨hal.trans_le hr.1, hr.2.trans_lt hhb⟩
  have hjets (n : ℕ) : ReferenceRapid D (iteratedDeriv (n + 1) g) := by
    simpa only [iteratedDeriv_succ'] using
      referenceRapid_compact_jets hD hdg hc (hs.trans hcore) n
  have hdiff : ReferenceRapid D (fun r => D.chiLeft r - g r) := by
    obtain ⟨ε, hε, hχleft, hχright⟩ := hborder.2.2.2.2.2
    let δ : ℝ := min (ε / 2) ((D.b - D.a) / 6)
    have hδ : 0 < δ := lt_min (by positivity) (by linarith)
    have hδε : δ < ε := by
      have hm : δ ≤ ε / 2 := min_le_left _ _
      linarith
    have hδwidth : δ ≤ (D.b - D.a) / 6 := min_le_right _ _
    have hKL : D.a + δ ≤ l := by dsimp only [l]; linarith
    have hKR : h ≤ D.b - δ := by dsimp only [h]; linarith
    have hK : Icc (D.a + δ) (D.b - δ) ⊆ radialCore D := by
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hz (r : ℝ) (hr : r ∈ radialCore D)
        (hout : r ∉ Icc (D.a + δ) (D.b - δ)) : D.chiLeft r - g r = 0 := by
      by_cases hlr : r < D.a + δ
      · rw [hχleft r ⟨hr.1, by linarith⟩, hleft r (hlr.le.trans hKL), sub_self]
      · have hrr : D.b - δ < r := lt_of_not_ge
          (fun hh => hout ⟨le_of_not_gt hlr, hh⟩)
        rw [hχright r ⟨by linarith, hr.2⟩, hright r (hKR.trans hrr.le), sub_self]
    exact ⟨1, 0, zero_lt_one,
      referenceRadialWeighted_of_compact_core hD
        (hborder.2.2.2.2.1.continuous.sub hg.continuous) isCompact_Icc hK hz 1 0⟩
  have hforcing (n : ℕ) :
      ReferenceRapid D (iteratedDeriv n (radialJacobi 0 D.w g)) := by
    have hw : ContDiff ℝ ∞ D.w := hD.choose_spec.1.2.2.1.1
    have hflux : ContDiff ℝ ∞ (fun r => D.w r * deriv g r) := hw.mul hdg
    have hfluxC : HasCompactSupport (fun r => D.w r * deriv g r) :=
      hc.mul_left (f := D.w)
    have hfluxS : tsupport (fun r => D.w r * deriv g r) ⊆ radialCore D :=
      tsupport_mul_subset_right.trans (hs.trans hcore)
    have he : radialJacobi 0 D.w g = deriv (fun r => D.w r * deriv g r) := by
      funext r
      simp only [radialJacobi, zero_mul, zero_div, sub_zero]
    rw [he]
    exact referenceRapid_compact_jets hD (contDiff_infty_iff_deriv.mp hflux).2
      hfluxC.deriv (tsupport_deriv_subset.trans hfluxS) n
  exact ⟨g, hg, ⟨l, h, hal, hlh, hhb, hleft, hright⟩, hdiff, hjets, hforcing⟩

end ContinuousFlexibility.Radial
