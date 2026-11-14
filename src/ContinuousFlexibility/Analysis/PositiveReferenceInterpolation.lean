module

public import ContinuousFlexibility.Analysis.PositiveReferenceCoordinate
public import ContinuousFlexibility.Analysis.PositiveReferenceHeight

/-!
# A genuine positive reference interpolation from local endpoint data

The cutoff radius, lower slope bound, upper slope bound, and middle
normalizer are all constructed from the actual endpoint fields. The
result includes the actual global coordinate inverse and the logarithmic
height, with both endpoint germs and avoidance of a closed forbidden set.
No endpoint mass bound or proposed diffeomorphism is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem continuousAt_positive_value_bounds
    {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousAt f c) (hp : 0 < f c) :
    ∀ᶠ x in 𝓝 c, f c / 2 ≤ f x ∧ |f x| ≤ f c + 1 := by
  have hnear : ∀ᶠ x in 𝓝 c, f c / 2 < f x ∧ f x < f c + 1 :=
    hf.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hnear] with x hx
  refine ⟨hx.1.le, ?_⟩
  rw [abs_of_pos (by linarith [hx.1] : 0 < f x)]
  exact hx.2.le

/-- Local smooth endpoint coordinates with positive actual slopes, and
local positive endpoint heights, determine an actual global interpolation.
The right endpoint coordinate is normalized to have value one. -/
theorem exists_positiveReferenceInterpolation
    {F : Set ℝ} (hF : IsClosed F) {l r ε ρL ρR : ℝ}
    (hl : l ∉ F) (hr : r ∉ F) (hlr : l < r)
    (hε : 0 < ε) (hρL : 0 < ρL) (hρR : 0 < ρR)
    {yL yR hL hR : ℝ → ℝ}
    (hyL : ∀ x ∈ Metric.ball l ρL, ContDiffAt ℝ ∞ yL x)
    (hyR : ∀ x ∈ Metric.ball r ρR, ContDiffAt ℝ ∞ yR x)
    (hhL : ∀ x ∈ Metric.ball l ρL, ContDiffAt ℝ ∞ hL x)
    (hhR : ∀ x ∈ Metric.ball r ρR, ContDiffAt ℝ ∞ hR x)
    (hvL : yL l = 0) (hvR : yR r = 1)
    (hdL : 0 < deriv yL l) (hdR : 0 < deriv yR r)
    (hpL : 0 < hL l) (hpR : 0 < hR r) :
    ∃ δ : ℝ, 0 < δ ∧ δ < min ρL ρR ∧ δ < ε ∧ 2 * δ < r - l ∧
      Disjoint (Metric.ball l δ) F ∧ Disjoint (Metric.ball r δ) F ∧
      (let Y : ℝ → ℝ := positiveReferenceCoordinate l r δ (deriv yL) (deriv yR);
       let H : ℝ → ℝ := positiveReferenceHeight l r δ hL hR;
       ContDiff ℝ ∞ Y ∧ (∀ x : ℝ, 0 < deriv Y x) ∧
       (∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, B ≤ deriv Y x) ∧
       Function.Bijective Y ∧ ContDiff ℝ ∞ (Function.invFun Y) ∧
       Y '' Ioo l r = Ioo 0 1 ∧
       ContDiff ℝ ∞ H ∧ (∀ x : ℝ, 0 < H x) ∧ (∀ x ∈ F, H x = 1) ∧
       ∀ side : Bool,
         Y =ᶠ[𝓝 (if side then r else l)] (if side then yR else yL) ∧
         H =ᶠ[𝓝 (if side then r else l)] (if side then hR else hL)) := by
  have hdyL : ContDiffAt ℝ ∞ (deriv yL) l :=
    (hyL l (Metric.mem_ball_self hρL)).derivWithin (by simp)
  have hdyR : ContDiffAt ℝ ∞ (deriv yR) r :=
    (hyR r (Metric.mem_ball_self hρR)).derivWithin (by simp)
  have hheightL : ∀ᶠ x in 𝓝 l, 0 < hL x :=
    (hhL l (Metric.mem_ball_self hρL)).continuousAt.eventually (Ioi_mem_nhds hpL)
  have hheightR : ∀ᶠ x in 𝓝 r, 0 < hR x :=
    (hhR r (Metric.mem_ball_self hρR)).continuousAt.eventually (Ioi_mem_nhds hpR)
  obtain ⟨κL, hκL, hlocalL⟩ := Metric.mem_nhds_iff.mp
    ((continuousAt_positive_value_bounds hdyL.continuousAt hdL).and hheightL)
  obtain ⟨κR, hκR, hlocalR⟩ := Metric.mem_nhds_iff.mp
    ((continuousAt_positive_value_bounds hdyR.continuousAt hdR).and hheightR)
  let A : ℝ := min (deriv yL l / 2) (deriv yR r / 2)
  let M : ℝ := max (deriv yL l + 1) (deriv yR r + 1)
  have hA : 0 < A := lt_min (half_pos hdL) (half_pos hdR)
  have hM : 0 < M :=
    (by linarith : 0 < deriv yL l + 1).trans_le (le_max_left _ _)
  have hsmallRadius :
      0 < min ρL (min ρR (min κL (min κR (min ε (1 / (4 * M)))))) :=
    lt_min hρL (lt_min hρR (lt_min hκL (lt_min hκR
      (lt_min hε (div_pos (by norm_num) (by positivity))))))
  obtain ⟨δ, hδ, hδsmall, hgap, havoidL, havoidR⟩ :=
    exists_positiveEndpoint_collars_avoiding hF hl hr hlr hsmallRadius
  rcases lt_min_iff.mp hδsmall with ⟨hδρL, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hδρR, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hδκL, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hδκR, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hδε, hδM⟩
  have hyδL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ yL x :=
    fun x hx => hyL x (Metric.ball_subset_ball hδρL.le hx)
  have hyδR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ yR x :=
    fun x hx => hyR x (Metric.ball_subset_ball hδρR.le hx)
  have hdδL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ (deriv yL) x :=
    fun x hx => (hyδL x hx).derivWithin (by simp)
  have hdδR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ (deriv yR) x :=
    fun x hx => (hyδR x hx).derivWithin (by simp)
  have hAL : ∀ x ∈ Metric.ball l δ, A ≤ deriv yL x := by
    intro x hx
    exact (min_le_left _ _).trans
      (hlocalL (Metric.ball_subset_ball hδκL.le hx)).1.1
  have hAR : ∀ x ∈ Metric.ball r δ, A ≤ deriv yR x := by
    intro x hx
    exact (min_le_right _ _).trans
      (hlocalR (Metric.ball_subset_ball hδκR.le hx)).1.1
  have hbL : ∀ x ∈ Metric.ball l δ, |deriv yL x| ≤ M := by
    intro x hx
    exact (hlocalL (Metric.ball_subset_ball hδκL.le hx)).1.2.trans
      (le_max_left _ _)
  have hbR : ∀ x ∈ Metric.ball r δ, |deriv yR x| ≤ M := by
    intro x hx
    exact (hlocalR (Metric.ball_subset_ball hδκR.le hx)).1.2.trans
      (le_max_right _ _)
  have hmassSmall : positiveReferenceEndMass l r δ (deriv yL) (deriv yR) < 1 := by
    apply (positiveReferenceEndMass_le hδ hM.le hdδL hdδR hbL hbR).trans_lt
    have hδM' := (lt_div_iff₀ (by positivity : 0 < 4 * M)).mp hδM
    nlinarith
  let Y : ℝ → ℝ := positiveReferenceCoordinate l r δ (deriv yL) (deriv yR)
  have hY := contDiff_positiveReferenceCoordinate hδ hdδL hdδR
  let B : ℝ := min A (positiveReferenceScale l r δ (deriv yL) (deriv yR))
  have hB : 0 < B := lt_min hA (positiveReferenceScale_pos hδ hgap hmassSmall)
  have hlower (x : ℝ) : B ≤ deriv Y x := by
    change B ≤ deriv (positiveReferenceCoordinate l r δ (deriv yL) (deriv yR)) x
    rw [(hasDerivAt_positiveReferenceCoordinate hδ hdδL hdδR x).deriv]
    exact positiveReferenceSlope_lower hδ hgap.le hAL hAR x
  have hpositive (x : ℝ) : 0 < deriv Y x := hB.trans_le (hlower x)
  have hbij := positiveReferenceCoordinate_bijective_smoothInverse
    hδ hgap hdδL hdδR hA hAL hAR hmassSmall
  have hmono : StrictMono Y := strictMono_of_deriv_pos hpositive
  have hleft : Y l = 0 := positiveReferenceCoordinate_left l r δ (deriv yL) (deriv yR)
  have hright : Y r = 1 := positiveReferenceCoordinate_right hδ hgap hdδL hdδR
  have himage : Y '' Ioo l r = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · simpa only [hleft] using hmono hx.1
      · simpa only [hright] using hmono hx.2
    · intro hy
      obtain ⟨x, hx⟩ := (show Function.Surjective Y from hbij.1.2) y
      refine ⟨x, ⟨?_, ?_⟩, hx⟩
      · by_contra hnot
        have h := hmono.monotone (le_of_not_gt hnot)
        rw [hleft, hx] at h
        exact (not_le_of_gt hy.1) h
      · by_contra hnot
        have h := hmono.monotone (le_of_not_gt hnot)
        rw [hright, hx] at h
        exact (not_le_of_gt hy.2) h
  have hhδL : ∀ x ∈ Metric.ball l δ, ContDiffAt ℝ ∞ hL x :=
    fun x hx => hhL x (Metric.ball_subset_ball hδρL.le hx)
  have hhδR : ∀ x ∈ Metric.ball r δ, ContDiffAt ℝ ∞ hR x :=
    fun x hx => hhR x (Metric.ball_subset_ball hδρR.le hx)
  have hpδL : ∀ x ∈ Metric.ball l δ, 0 < hL x :=
    fun _ hx => (hlocalL (Metric.ball_subset_ball hδκL.le hx)).2
  have hpδR : ∀ x ∈ Metric.ball r δ, 0 < hR x :=
    fun _ hx => (hlocalR (Metric.ball_subset_ball hδκR.le hx)).2
  refine ⟨δ, hδ, lt_min hδρL hδρR, hδε, hgap, havoidL, havoidR,
    hY, hpositive, ⟨B, hB, hlower⟩, hbij.1, hbij.2, himage,
    contDiff_positiveReferenceHeight hδ hhδL hhδR hpδL hpδR,
    positiveReferenceHeight_pos l r δ hL hR, ?_, ?_⟩
  · intro x hx
    exact positiveReferenceHeight_eq_one_on_forbidden hδ havoidL havoidR hx
  · intro side
    exact ⟨positiveReferenceCoordinate_endpoint_germ hδ hgap hyδL hyδR hvL hvR side,
      positiveReferenceHeight_endpoint_germ hδ hgap hpδL hpδR side⟩

end ContinuousFlexibility.Analysis
