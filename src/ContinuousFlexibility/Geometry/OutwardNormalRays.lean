module

public import ContinuousFlexibility.Contracts.GraphBoundaryNormals
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.ClusterPt

/-!
# Actual outward rays and local inside-region identification

Equality of regions in a genuine neighborhood also identifies their closures
locally, so it transports the same Euclidean inward and outward normal rays.
The two opposite directions cannot both point outward from the same region.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem closure_eventuallyEq_of_eventuallyEq {Ω U : Set E3} {p : E3}
    (h : Ω =ᶠ[𝓝 p] U) : closure Ω =ᶠ[𝓝 p] closure U := by
  apply Filter.eventuallyEqSet_iff.mpr
  filter_upwards [(Filter.EventuallyEqSet.mem_iff h).eventually_nhds] with x hx
  have he : 𝓝[Ω] x = 𝓝[U] x :=
    nhdsWithin_eq_iff_eventuallyEqSet.mpr (Filter.Eventually.set_eq hx)
  simp only [mem_closure_iff_nhdsWithin_neBot, he]

/-- The same actual normal rays are outward after a local identification of
the actual inside region. No differential transport by a homeomorphism is assumed. -/
theorem PointsOutwardFrom.congr_germ {Ω U : Set E3} {p n : E3}
    (h : PointsOutwardFrom Ω p n) (he : Ω =ᶠ[𝓝 p] U) :
    PointsOutwardFrom U p n := by
  obtain ⟨ε, hε, hrays⟩ := h
  have hec := closure_eventuallyEq_of_eventuallyEq he
  have hc : Continuous (fun s : ℝ => p + s • n) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun s : ℝ => p + s • n) (𝓝 0) (𝓝 p) := by
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  have hnear := ht.eventually
    ((Filter.EventuallyEqSet.mem_iff he).and (Filter.EventuallyEqSet.mem_iff hec))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min ε δ, lt_min hε hδ, fun s hs => ?_⟩
  have hsε : s ∈ Ioo (0 : ℝ) ε := ⟨hs.1, hs.2.trans_le (min_le_left ε δ)⟩
  have hsδ : s < δ := hs.2.trans_le (min_le_right ε δ)
  have hp := hb (y := s) (by simpa [Real.dist_eq, abs_of_pos hs.1] using hsδ)
  have hm := hb (y := -s) (by simpa [Real.dist_eq, abs_neg, abs_of_pos hs.1] using hsδ)
  have hminus : (p - s • n ∈ Ω ↔ p - s • n ∈ U) := by
    simpa only [neg_smul, sub_eq_add_neg] using hm.1
  exact ⟨hminus.mp (hrays s hsε).1,
    fun hx => (hrays s hsε).2 (hp.2.mpr hx)⟩

/-- A direction and its negative cannot both satisfy the real inside/outside
ray condition at one boundary point of the same region. -/
theorem PointsOutwardFrom.not_neg {Ω : Set E3} {p n : E3}
    (h : PointsOutwardFrom Ω p n) : ¬ PointsOutwardFrom Ω p (-n) := by
  obtain ⟨ε, hε, hrays⟩ := h
  rintro ⟨δ, hδ, hneg⟩
  let s : ℝ := min ε δ / 2
  have hspos : 0 < s := half_pos (lt_min hε hδ)
  have hsmall : s < min ε δ := half_lt_self (lt_min hε hδ)
  have hsε : s ∈ Ioo (0 : ℝ) ε := ⟨hspos, hsmall.trans_le (min_le_left ε δ)⟩
  have hsδ : s ∈ Ioo (0 : ℝ) δ := ⟨hspos, hsmall.trans_le (min_le_right ε δ)⟩
  apply (hneg s hsδ).2
  have hin : p - s • n ∈ closure Ω := subset_closure (hrays s hsε).1
  simpa only [smul_neg, sub_eq_add_neg] using hin

theorem PointsOutwardFrom.eq_of_eq_or_eq_neg {Ω : Set E3} {p n m : E3}
    (hn : PointsOutwardFrom Ω p n) (hm : PointsOutwardFrom Ω p m)
    (he : m = n ∨ m = -n) : m = n := by
  rcases he with he | he
  · exact he
  · exact False.elim (hn.not_neg (he ▸ hm))

/-- A continuous actual defining function, with positive derivative along
the actual normal ray, identifies an outward normal for a locally equal region. -/
theorem PointsOutwardFrom.of_defining_function {Ω : Set E3} {p n : E3}
    {J : E3 → ℝ} (hJ : Continuous J) (hΩ : Ω =ᶠ[𝓝 p] {v : E3 | J v < 0})
    (hzero : J p = 0) {c : ℝ}
    (hd : HasDerivAt (fun s : ℝ => J (p + s • n)) c 0) (hc : 0 < c) :
    PointsOutwardFrom Ω p n := by
  obtain ⟨ε, hε, hsigns⟩ := positive_derivative_two_sided_sign hd
    (by simpa only [zero_smul, add_zero] using hzero) hc
  have hclosure : closure {v : E3 | J v < 0} ⊆ {v : E3 | J v ≤ 0} := by
    apply closure_minimal
    · intro v hv
      change J v < 0 at hv
      change J v ≤ 0
      exact hv.le
    · exact isClosed_le hJ continuous_const
  have hout : PointsOutwardFrom {v : E3 | J v < 0} p n := by
    refine ⟨ε, hε, fun s hs => ?_⟩
    constructor
    · change J (p - s • n) < 0
      simpa only [neg_smul, sub_eq_add_neg] using (hsigns s hs).2
    · intro hx
      exact not_le_of_gt (hsigns s hs).1 (hclosure hx)
  exact hout.congr_germ hΩ.symm

end ContinuousFlexibility
