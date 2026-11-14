module

public import ContinuousFlexibility.Radial.MorseMiddleJoin
public import ContinuousFlexibility.Radial.MorseChainLocalGluing

/-!
# Finite positive bridges and positions of two cone heads

The cone reference heights are fixed before their short joins are chosen.
Their lengths can then be made arbitrarily small while the two cones remain
strictly ordered in height. All constructions here concern the finite middle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

theorem exists_r07_positive_bridge {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x)
    (hfd : 0 < deriv f a) (hgd : 0 < deriv g b) (hgap : f a < g b) :
    ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ (∀ x, 0 < w x) ∧
      (w =ᶠ[𝓝 a] f) ∧ (w =ᶠ[𝓝 b] g) ∧ ∀ x ∈ Icc a b, 0 < deriv w x := by
  have hlf : ContDiff ℝ ∞ (fun x => log (f x)) := hf.log (fun x => (hfp x).ne')
  have hlg : ContDiff ℝ ∞ (fun x => log (g x)) := hg.log (fun x => (hgp x).ne')
  have hldf : 0 < deriv (fun x => log (f x)) a := by
    rw [((hf.differentiable (by simp) a).hasDerivAt.log (hfp a).ne').deriv]
    exact div_pos hfd (hfp a)
  have hldg : 0 < deriv (fun x => log (g x)) b := by
    rw [((hg.differentiable (by simp) b).hasDerivAt.log (hgp b).ne').deriv]
    exact div_pos hgd (hgp b)
  obtain ⟨h, m, hh, _, hsep, hm, _, hw, hp, hL, hR, hd, _⟩ :=
    exists_morseMiddleJoin_of_log_profiles (eta := 1) hab (by norm_num) hlf hlg hldf hldg
      (log_lt_log (hfp a) hgap)
  refine ⟨_, hw, hp, ?_, ?_, fun x hx => (hd x hx).2⟩
  · filter_upwards [hL] with x hx
    exact hx.trans (exp_log (hfp x))
  · filter_upwards [hR] with x hx
    exact hx.trans (exp_log (hgp x))

/-- Positive smooth pieces with positive slopes glue over adjacent closed
intervals when their full germs agree at the cut. -/
theorem r07_positive_glue {a c b : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (hfg : f =ᶠ[𝓝 c] g)
    (hfd : ∀ x ∈ Icc a c, 0 < deriv f x) (hgd : ∀ x ∈ Icc c b, 0 < deriv g x) :
    ContDiff ℝ ∞ (morseGlueCut c f g) ∧ (∀ x, 0 < morseGlueCut c f g x) ∧
      ∀ x ∈ Icc a b, 0 < deriv (morseGlueCut c f g) x := by
  refine ⟨contDiff_morseGlueCut hf hg hfg, ?_, ?_⟩
  · intro x
    unfold morseGlueCut
    split_ifs <;> first | exact hfp x | exact hgp x
  · intro x hx
    rcases le_total x c with h | h
    · rw [(morseGlueCut_eventually_left hfg h).deriv_eq]
      exact hfd x ⟨hx.1, h⟩
    · rw [(morseGlueCut_eventually_right hfg h).deriv_eq]
      exact hgd x ⟨h, hx.2⟩

/-- Four strictly ordered cuts, with arbitrarily short outer joins, keep
the prescribed left and right cone heights separated at the middle cuts. -/
theorem exists_r07_cone_positions {a b WL WR η : ℝ}
    (ha : 0 < a) (hab : a < b) (hWL : 0 < WL) (hW : WL < WR) (hη : 0 < η) :
    ∃ jL cL cR jR : ℝ,
      a < jL ∧ jL < cL ∧ cL < cR ∧ cR < jR ∧ jR < b ∧
      jL - a < η ∧ b - jR < η ∧ WL / jL * cL < WR / jR * cR := by
  have hb : 0 < b := ha.trans hab
  let L : ℝ → ℝ := fun t => WL * (a + 2 * t) / (a + t)
  let R : ℝ → ℝ := fun t => WR * (b - 2 * t) / (b - t)
  have hL : ContinuousAt L 0 :=
    ((continuous_const.mul (continuous_const.add (continuous_const.mul continuous_id))).continuousAt).div
      (continuous_const.add continuous_id).continuousAt (by simpa using ha.ne')
  have hR : ContinuousAt R 0 :=
    ((continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_id))).continuousAt).div
      (continuous_const.sub continuous_id).continuousAt (by simpa using hb.ne')
  have h0 : L 0 < R 0 := by simpa [L, R, ha.ne', hb.ne'] using hW
  obtain ⟨d, hd, hdgap⟩ := Metric.eventually_nhds_iff.mp (hL.eventually_lt hR h0)
  let e := min d (min η ((b - a) / 8)) / 2
  have he : 0 < e := div_pos (lt_min hd (lt_min hη (by positivity))) (by norm_num)
  have heD : e < d := by
    have h := min_le_left d (min η ((b - a) / 8))
    dsimp only [e]
    linarith only [h, hd]
  have heη : e < η := by
    have h := (min_le_right d (min η ((b - a) / 8))).trans (min_le_left _ _)
    dsimp only [e]
    linarith only [h, hη]
  have heGap : 8 * e < b - a := by
    have h := (min_le_right d (min η ((b - a) / 8))).trans (min_le_right _ _)
    dsimp only [e]
    linarith only [h, hab]
  have hg : L e < R e := hdgap (by simpa only [Real.dist_eq, sub_zero, abs_of_pos he] using heD)
  refine ⟨a + e, a + 2 * e, b - 2 * e, b - e,
    by linarith only [he], by linarith only [he], by linarith only [heGap, he],
    by linarith only [he], by linarith only [he], ?_, ?_, ?_⟩
  · linarith only [heη]
  · linarith only [heη]
  · dsimp only [L, R] at hg
    convert hg using 1 <;> ring

/-- A global positive smooth radius agrees with the physical radius near
the entire retained middle interval. -/
theorem exists_r07_smooth_radius_germ {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ R : ℝ → ℝ, ContDiff ℝ ∞ R ∧ (∀ x, 0 < R x) ∧
      ∀ x ∈ Icc a b, R =ᶠ[𝓝 x] id := by
  have hlog : ContDiffOn ℝ ∞ (fun x : ℝ => log x) (Ioo (a / 2) (b + 1)) :=
    contDiffOn_id.log (fun x hx => (lt_trans (by linarith only [ha] : 0 < a / 2) hx.1).ne')
  obtain ⟨F, hF, _, hFg⟩ := exists_contDiff_joinGerm_extension
    (by linarith only [ha] : a / 2 < a) hab (by linarith : b < b + 1) hlog
  refine ⟨fun x => exp (F x), hF.exp, fun x => exp_pos _, ?_⟩
  intro x hx
  have hx₀ : 0 < x := ha.trans_le hx.1
  filter_upwards [hFg x hx, Ioi_mem_nhds hx₀] with y hy hy₀
  exact (congrArg exp hy).trans (exp_log hy₀)

end ContinuousFlexibility.Radial
