import ContinuousFlexibility.Analysis.N01OpticalCorrectionCutoffs
import ContinuousFlexibility.Analysis.ReturnCorrectionErrorSmoothness
import Mathlib.Order.Filter.Finite

/-!
# Patching with the actual optical cutoff family

Disjoint negative components have at most one left endpoint and at most
one right endpoint at a fixed radius. Isolation of a reference root
therefore gives one neighborhood on which every cutoff derivative
vanishes, even when the transition collars have different relative
widths. This supplies the global smooth patch for the quantitative
optical cutoff family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem componentFamily_eventually_zero_at_isolated_root
    (l h : ℕ → ℝ) (f : ℝ → ℝ) (r₀ : ℝ) (g : ℕ → ℝ → ℝ)
    (hlh : ∀ m, l m < h m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (l m) (h m)) (Ioo (l n) (h n)))
    (hroot : ∀ m, f (l m) = 0 ∧ f (h m) = 0)
    (hneg : ∀ m r, r ∈ Ioo (l m) (h m) → f r < 0)
    (hr₀ : f r₀ = 0) (hiso : ∀ᶠ r in 𝓝 r₀, f r = 0 → r = r₀)
    (hsupp : ∀ m, Function.support (g m) ⊆ Ioo (l m) (h m))
    (hleft : ∀ m, g m =ᶠ[𝓝 (l m)] fun _ => 0)
    (hright : ∀ m, g m =ᶠ[𝓝 (h m)] fun _ => 0) :
    ∀ᶠ r in 𝓝 r₀, ∀ m, g m r = 0 := by
  have hlf : Set.Finite {m | l m = r₀} := by
    apply Set.Subsingleton.finite
    intro m hm n hn
    change l m = r₀ at hm
    change l n = r₀ at hn
    by_contra hmn
    let r := (r₀ + min (h m) (h n)) / 2
    have hmin : r₀ < min (h m) (h n) :=
      lt_min (by simpa only [hm] using hlh m) (by simpa only [hn] using hlh n)
    have hrm : r ∈ Ioo (l m) (h m) := by
      rw [hm]
      dsimp only [r]
      constructor <;> linarith [min_le_left (h m) (h n)]
    have hrn : r ∈ Ioo (l n) (h n) := by
      rw [hn]
      dsimp only [r]
      constructor <;> linarith [min_le_right (h m) (h n)]
    exact Set.disjoint_left.mp (hdisj m n hmn) hrm hrn
  have hhf : Set.Finite {m | h m = r₀} := by
    apply Set.Subsingleton.finite
    intro m hm n hn
    change h m = r₀ at hm
    change h n = r₀ at hn
    by_contra hmn
    let r := (max (l m) (l n) + r₀) / 2
    have hmax : max (l m) (l n) < r₀ :=
      max_lt (by simpa only [hm] using hlh m) (by simpa only [hn] using hlh n)
    have hrm : r ∈ Ioo (l m) (h m) := by
      rw [hm]
      dsimp only [r]
      constructor <;> linarith [le_max_left (l m) (l n)]
    have hrn : r ∈ Ioo (l n) (h n) := by
      rw [hn]
      dsimp only [r]
      constructor <;> linarith [le_max_right (l m) (l n)]
    exact Set.disjoint_left.mp (hdisj m n hmn) hrm hrn
  have he : ∀ᶠ r in 𝓝 r₀, ∀ m ∈ {m | l m = r₀} ∪ {m | h m = r₀}, g m r = 0 := by
    apply ((hlf.union hhf).eventually_all).mpr
    intro m hm
    rcases hm with hm | hm
    · change l m = r₀ at hm
      simpa only [hm] using (hleft m).eventually
    · change h m = r₀ at hm
      simpa only [hm] using (hright m).eventually
  obtain ⟨δ, hδ, hisoδ⟩ := Metric.mem_nhds_iff.mp hiso
  filter_upwards [he, Metric.ball_mem_nhds r₀ hδ] with r her hr
  have hrabs : |r - r₀| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
  obtain ⟨hrlo, hrhi⟩ := abs_lt.mp hrabs
  intro m
  by_contra hgm
  have hm : r ∈ Ioo (l m) (h m) := hsupp m hgm
  have hside : r₀ ≤ l m ∨ h m ≤ r₀ := by
    by_cases hl : r₀ ≤ l m
    · exact Or.inl hl
    · right
      by_contra hh
      have hn := hneg m r₀ ⟨lt_of_not_ge hl, lt_of_not_ge hh⟩
      linarith
  rcases hside with hl | hh
  · have hlball : l m ∈ Metric.ball r₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hm.1]
    have heq := hisoδ hlball (hroot m).1
    exact hgm (her m (Or.inl heq))
  · have hhball : h m ∈ Metric.ball r₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hm.2]
    have heq := hisoδ hhball (hroot m).2
    exact hgm (her m (Or.inr heq))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.cutoffs_deriv_eventually_zero_of_nonnegative
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (χ : ℕ → ℝ → ℝ)
    (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) (hw' : 0 ≤ deriv D.w r) :
    ∀ᶠ s in 𝓝 r, ∀ m, deriv (χ m) s = 0 := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  obtain ⟨bounds, hbounds⟩ := hN01.1.1
  rcases hw'.eq_or_lt with hzero | hpos
  · have hroot : deriv D.w r = 0 := hzero.symm
    have hsimple : deriv (deriv D.w) r ≠ 0 := hbounds.1.2.2.2.2.2.2 r hr hroot
    have hne : ∀ᶠ s in 𝓝[≠] r, deriv D.w s ≠ 0 :=
      (differentiableAt_of_deriv_ne_zero hsimple).hasDerivAt.eventually_ne hsimple
    have hiso : ∀ᶠ s in 𝓝 r, deriv D.w s = 0 → s = r := by
      filter_upwards [eventually_nhdsWithin_iff.mp hne] with s hs
      intro hs0
      by_contra hsr
      exact hs hsr hs0
    apply componentFamily_eventually_zero_at_isolated_root
      C.left C.right (deriv D.w) r (fun m => deriv (χ m))
      (fun m => (hC.1 m).2.1) hC.2.2.1
      (fun m => ⟨(hC.2.1 m).1, (hC.2.1 m).2.1⟩) hC.2.2.2.1 hroot hiso hsupp
    · intro m
      simpa only [deriv_const'] using (hend m).1.deriv
    · intro m
      simpa only [deriv_const'] using (hend m).2.deriv
  · have hw : ContDiff ℝ ∞ D.w := hbounds.1.2.2.1.1
    have hc : ContinuousAt (deriv D.w) r := (hw.continuous_deriv (by simp)).continuousAt
    filter_upwards [hc.preimage_mem_nhds (Ioi_mem_nhds hpos)] with s hs
    intro m
    by_contra hne
    exact (not_lt_of_ge hs.le) (hC.2.2.2.1 m s (hsupp m hne))

theorem N01Properties.returnCorrectionCoefficientError_contDiffAt_of_cutoffs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    (hdisc : ∀ m p, p.1 ∈ tsupport (deriv (χ m)) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (fun q => returnCorrectionCoefficientError D S C R χ z q ρ) p := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  by_cases hex : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m)
  · obtain ⟨m, hm⟩ := hex
    have heq := returnCorrectionCoefficientError_eventually_local (D := D)
      hC.2.2.1 R χ z m p hm
    by_cases hactive : p.1 ∈ tsupport (deriv (χ m))
    · have hl := hN01.returnCorrectionLocalCoefficientError_contDiffAt
        hS hT R hz hsector χ m (hχ m) (hχrange m) ρ p hm (hdisc m p hactive)
      apply hl.congr_of_eventuallyEq
      filter_upwards [heq] with q hq
      exact congrArg (fun L : CircleSpace S →ₗ[ℝ] ℝ × ℝ => L ρ) hq
    · have hz : deriv (χ m) =ᶠ[𝓝 p.1] fun _ => 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hactive
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [heq, continuous_fst.continuousAt.preimage_mem_nhds hz] with q hq hqz
      rw [hq, returnCorrectionLocalCoefficientError_eq_zero_of_deriv_zero
        D S C R χ z m q hqz, LinearMap.zero_apply]
  · have hn : 0 ≤ deriv D.w p.1 := by
      by_contra h
      exact hex (hC.2.2.2.2.1 p.1 hp.1 (lt_of_not_ge h))
    have hzero := returnCorrectionCoefficientError_eventually_zero D S C R χ z p
      (hN01.cutoffs_deriv_eventually_zero_of_nonnegative χ hsupp hend hp.1 hn)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hzero] with q hq
    rw [hq, LinearMap.zero_apply]

end ContinuousFlexibility.Statements

