module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowTimeChange
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Localization of a circle speed to its original time neighborhood

A smooth time clamp equals the identity on the supplied closed interval and
takes every real time into the given open strip. Composing the original
speed with this clamp gives a globally smooth periodic speed without
changing any angular slice or angular derivative on the original interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped ContDiff Topology

private def circleFlowTimeClampBump (a b ε : ℝ) (hab : a ≤ b) (hε : 0 < ε) :
    ContDiffBump ((a + b) / 2) where
  rIn := (b - a) / 2 + ε / 3
  rOut := (b - a) / 2 + 2 * ε / 3
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- A globally smooth time clamp, with the identity retained on the closed
interval. The positive margin also covers the degenerate case `a = b`. -/
def circleFlowSmoothTimeClamp (a b ε : ℝ) (hab : a ≤ b) (hε : 0 < ε)
    (t : ℝ) : ℝ :=
  (a + b) / 2 + circleFlowTimeClampBump a b ε hab hε t * (t - (a + b) / 2)

theorem contDiff_circleFlowSmoothTimeClamp {a b ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) :
    ContDiff ℝ ∞ (circleFlowSmoothTimeClamp a b ε hab hε) :=
  contDiff_const.add ((circleFlowTimeClampBump a b ε hab hε).contDiff.mul
    (contDiff_id.sub contDiff_const))

theorem circleFlowSmoothTimeClamp_eq {a b ε t : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) (ht : t ∈ Icc a b) :
    circleFlowSmoothTimeClamp a b ε hab hε t = t := by
  let χ := circleFlowTimeClampBump a b ε hab hε
  have hball : t ∈ Metric.closedBall ((a + b) / 2) χ.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    apply abs_le.mpr
    change -((b - a) / 2 + ε / 3) ≤ t - (a + b) / 2 ∧
      t - (a + b) / 2 ≤ (b - a) / 2 + ε / 3
    constructor <;> linarith [ht.1, ht.2]
  have hone : χ t = 1 := χ.one_of_mem_closedBall hball
  change (a + b) / 2 + χ t * (t - (a + b) / 2) = t
  rw [hone]
  ring

theorem circleFlowSmoothTimeClamp_eqOn {a b ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) :
    EqOn (circleFlowSmoothTimeClamp a b ε hab hε) id (Icc a b) :=
  fun _ ht => circleFlowSmoothTimeClamp_eq hab hε ht

theorem circleFlowSmoothTimeClamp_mem {a b ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) (t : ℝ) :
    circleFlowSmoothTimeClamp a b ε hab hε t ∈ Ioo (a - ε) (b + ε) := by
  let c : ℝ := (a + b) / 2
  let χ := circleFlowTimeClampBump a b ε hab hε
  change a - ε < c + χ t * (t - c) ∧ c + χ t * (t - c) < b + ε
  by_cases hz : χ t = 0
  · rw [hz, zero_mul, add_zero]
    dsimp only [c]
    constructor <;> linarith
  · have hball : t ∈ Metric.ball c χ.rOut := by
      rw [← χ.support_eq]
      exact hz
    have hd : |t - c| < χ.rOut := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hball
    have hmul : |χ t * (t - c)| ≤ |t - c| := by
      rw [abs_mul, abs_of_nonneg χ.nonneg]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg (t - c))
    obtain ⟨hlo, hhi⟩ := abs_lt.mp (hmul.trans_lt hd)
    change -((b - a) / 2 + 2 * ε / 3) < χ t * (t - c) at hlo
    change χ t * (t - c) < (b - a) / 2 + 2 * ε / 3 at hhi
    dsimp only [c] at hlo hhi ⊢
    constructor <;> linarith

/-- The original angular slice is smooth at every time in the given open
time domain. This requires no extension of the speed. -/
theorem contDiff_circleFlowLocal_slice {G : PolarPoint → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G (U ×ˢ (univ : Set ℝ)))
    {t : ℝ} (ht : t ∈ U) :
    ContDiff ℝ ∞ (fun θ : ℝ => G (t, θ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hg : ContDiffAt ℝ ∞ G (t, θ) :=
    hG.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ht, mem_univ θ⟩)
  exact hg.comp θ (contDiffAt_const.prodMk contDiffAt_id)

/-- The globally defined speed obtained solely by changing the time
argument outside the original closed interval. -/
def circleFlowLocalizedSpeed {a b ε : ℝ} (G : PolarPoint → ℝ)
    (hab : a ≤ b) (hε : 0 < ε) (p : PolarPoint) : ℝ :=
  G (circleFlowSmoothTimeClamp a b ε hab hε p.1, p.2)

theorem contDiff_circleFlowLocalizedSpeed {G : PolarPoint → ℝ} {a b ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε)
    (hG : ContDiffOn ℝ ∞ G (Ioo (a - ε) (b + ε) ×ˢ (univ : Set ℝ))) :
    ContDiff ℝ ∞ (circleFlowLocalizedSpeed G hab hε) := by
  have hm : ContDiff ℝ ∞ (fun p : PolarPoint =>
      (circleFlowSmoothTimeClamp a b ε hab hε p.1, p.2)) :=
    ((contDiff_circleFlowSmoothTimeClamp hab hε).comp contDiff_fst).prodMk contDiff_snd
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hg : ContDiffAt ℝ ∞ G
      (circleFlowSmoothTimeClamp a b ε hab hε p.1, p.2) :=
    hG.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨circleFlowSmoothTimeClamp_mem hab hε p.1, mem_univ p.2⟩)
  have he : circleFlowLocalizedSpeed G hab hε =
      G ∘ (fun q : PolarPoint =>
        (circleFlowSmoothTimeClamp a b ε hab hε q.1, q.2)) := rfl
  rw [he]
  exact hg.comp p hm.contDiffAt

theorem circleFlowLocalizedSpeed_periodic {G : PolarPoint → ℝ} {a b ε P : ℝ}
    (hab : a ≤ b) (hε : 0 < ε)
    (hperiod : ∀ t ∈ Ioo (a - ε) (b + ε),
      Periodic (fun θ => G (t, θ)) P) :
    ∀ t : ℝ, Periodic (fun θ => circleFlowLocalizedSpeed G hab hε (t, θ)) P := by
  intro t
  exact hperiod _ (circleFlowSmoothTimeClamp_mem hab hε t)

theorem circleFlowLocalizedSpeed_eq {G : PolarPoint → ℝ} {a b ε t : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) (ht : t ∈ Icc a b) (θ : ℝ) :
    circleFlowLocalizedSpeed G hab hε (t, θ) = G (t, θ) := by
  change G (circleFlowSmoothTimeClamp a b ε hab hε t, θ) = G (t, θ)
  rw [circleFlowSmoothTimeClamp_eq hab hε ht]

theorem circleFlowLocalizedSpeed_eqOn {G : PolarPoint → ℝ} {a b ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) :
    EqOn (circleFlowLocalizedSpeed G hab hε) G (Icc a b ×ˢ (univ : Set ℝ)) := by
  rintro ⟨t, θ⟩ ⟨ht, _⟩
  exact circleFlowLocalizedSpeed_eq hab hε ht θ

theorem circleFlowLocalizedSpeed_slice_eq {G : PolarPoint → ℝ} {a b ε t : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) (ht : t ∈ Icc a b) :
    (fun θ : ℝ => circleFlowLocalizedSpeed G hab hε (t, θ)) =
      (fun θ : ℝ => G (t, θ)) :=
  funext (circleFlowLocalizedSpeed_eq hab hε ht)

theorem circleFlowLocalizedSpeed_iteratedDeriv {G : PolarPoint → ℝ} {a b ε t : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) (ht : t ∈ Icc a b) (n : ℕ) (θ : ℝ) :
    iteratedDeriv n (fun η => circleFlowLocalizedSpeed G hab hε (t, η)) θ =
      iteratedDeriv n (fun η => G (t, η)) θ := by
  rw [circleFlowLocalizedSpeed_slice_eq hab hε ht]

end ContinuousFlexibility.Analysis
