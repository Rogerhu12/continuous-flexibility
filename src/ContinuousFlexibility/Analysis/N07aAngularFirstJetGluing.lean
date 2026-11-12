import ContinuousFlexibility.Analysis.N07aAngularBoundaryQuotient
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Local gluing of one physical first jet

Only a common first jet at the interface point is needed for
differentiability there. Once differentiability is known throughout the
open region, the two smooth closed-side representatives also prove
continuity of the actual derivative. No second normal matching is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n07a_hasFDerivAt_if_interface {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u v : PolarPoint → F} {A : PolarPoint →L[ℝ] F}
    {p : PolarPoint} {c : ℝ} (hp : p.1 = c)
    (hu : HasFDerivAt u A p) (hv : HasFDerivAt v A p) (hvalue : u p = v p) :
    HasFDerivAt (fun q : PolarPoint => if q.1 ≤ c then u q else v q) A p := by
  let S : Set PolarPoint := {q | q.1 ≤ c}
  have hpc : p.1 ≤ c := hp.le
  have hl : HasFDerivWithinAt (fun q : PolarPoint => if q.1 ≤ c then u q else v q) A S p :=
    hu.hasFDerivWithinAt.congr (fun q hq => if_pos hq) (if_pos hpc)
  have hr : HasFDerivWithinAt (fun q : PolarPoint => if q.1 ≤ c then u q else v q) A Sᶜ p :=
    hv.hasFDerivWithinAt.congr (fun q hq => if_neg hq) ((if_pos hpc).trans hvalue)
  simpa only [union_compl_self, hasFDerivWithinAt_univ] using hl.union hr

theorem n07a_fderiv_eventually_eq_on_set {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f g : PolarPoint → F} {s : Set PolarPoint} {p : PolarPoint}
    (hs : UniqueDiffOn ℝ s)
    (hf : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q)
    (hg : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ g q)
    (he : ∀ᶠ q in 𝓝 p, q ∈ s → f q = g q) :
    ∀ᶠ q in 𝓝 p, q ∈ s → fderiv ℝ f q = fderiv ℝ g q := by
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp he
  filter_upwards [hVo.mem_nhds hpV, hf, hg] with q hq hf hg hqs
  have heq : f =ᶠ[𝓝[s] q] g := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hVo.mem_nhds hq)] with x hx hxV
    exact hV hxV hx
  exact (hs q hqs).eq hf.hasFDerivAt.hasFDerivWithinAt
    (hg.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq heq (hV hq hqs))

theorem n07a_two_closed_branches_hasFDerivAt
    {f u v : PolarPoint → ℝ} {p : PolarPoint} {c : ℝ} (hp : p.1 = c)
    (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p)
    (hd : fderiv ℝ u p = fderiv ℝ v p)
    (hl : ∀ᶠ q in 𝓝 p, q.1 ≤ c → f q = u q)
    (hr : ∀ᶠ q in 𝓝 p, c ≤ q.1 → f q = v q) :
    HasFDerivAt f (fderiv ℝ u p) p := by
  have hvalue : u p = v p := (hl.self_of_nhds hp.le).symm.trans (hr.self_of_nhds hp.ge)
  have h := n07a_hasFDerivAt_if_interface hp hu.hasFDerivAt
    (hv.hasFDerivAt.congr_fderiv hd.symm) hvalue
  apply h.congr_of_eventuallyEq
  filter_upwards [hl, hr] with q hqL hqR
  split_ifs with hqc
  · exact hqL hqc
  · exact hqR (lt_of_not_ge hqc).le

theorem n07a_two_closed_branches_fderiv_continuousAt
    {f u v : PolarPoint → ℝ} {p : PolarPoint} {c : ℝ} (hp : p.1 = c)
    (hf : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q)
    (hu : ContDiffAt ℝ ∞ u p) (hv : ContDiffAt ℝ ∞ v p)
    (hl : ∀ᶠ q in 𝓝 p, q.1 ≤ c → f q = u q)
    (hr : ∀ᶠ q in 𝓝 p, c ≤ q.1 → f q = v q) :
    ContinuousAt (fderiv ℝ f) p := by
  have hu1 : ContDiffAt ℝ 1 u p := hu.of_le (by simp)
  have hv1 : ContDiffAt ℝ 1 v p := hv.of_le (by simp)
  have hud : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ u q :=
    (hu1.eventually (by simp)).mono fun _ hq => hq.differentiableAt (by simp)
  have hvd : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ v q :=
    (hv1.eventually (by simp)).mono fun _ hq => hq.differentiableAt (by simp)
  have hld := n07a_fderiv_eventually_eq_on_set
    ((uniqueDiffOn_Iic c).prod uniqueDiffOn_univ) hf hud
    (hl.mono fun q hq hqs => hq hqs.1)
  have hrd := n07a_fderiv_eventually_eq_on_set
    ((uniqueDiffOn_Ici c).prod uniqueDiffOn_univ) hf hvd
    (hr.mono fun q hq hqs => hq hqs.1)
  have heL : fderiv ℝ f p = fderiv ℝ u p := hld.self_of_nhds ⟨hp.le, mem_univ _⟩
  have heR : fderiv ℝ f p = fderiv ℝ v p := hrd.self_of_nhds ⟨hp.ge, mem_univ _⟩
  have hut : Tendsto (fderiv ℝ u) (𝓝 p) (𝓝 (fderiv ℝ f p)) := by
    rw [heL]
    exact (hu.fderiv_right (show (0 : ℕ∞ω) + 1 ≤ ∞ by simp)).continuousAt.tendsto
  have hvt : Tendsto (fderiv ℝ v) (𝓝 p) (𝓝 (fderiv ℝ f p)) := by
    rw [heR]
    exact (hv.fderiv_right (show (0 : ℕ∞ω) + 1 ≤ ∞ by simp)).continuousAt.tendsto
  have hlim := hut.if' (p := fun q : PolarPoint => q.1 ≤ c) hvt
  apply hlim.congr'
  filter_upwards [hld, hrd] with q hqL hqR
  split_ifs with hqc
  · exact (hqL ⟨hqc, mem_univ _⟩).symm
  · exact (hqR ⟨(lt_of_not_ge hqc).le, mem_univ _⟩).symm

end ContinuousFlexibility.Analysis
