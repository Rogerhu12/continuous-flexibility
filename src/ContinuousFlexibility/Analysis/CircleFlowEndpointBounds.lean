import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Angular derivative bounds at radial endpoints

The ordinary circle flow is continuous in its radial variable up to the two
ends of a cell.  Its quantitative jet estimates are stated only in the open
cell.  Uniform bounds on the first angular derivative pass to the endpoints
without assuming that the derivative is jointly continuous there: first pass
the corresponding increment bounds to the radial limit, then take the angular
difference quotient.  One argument treats both radial endpoints.
-/

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

/-- Uniform angular derivative bounds in an open parameter interval give the
same increment bounds on its closure, assuming pointwise parameter continuity. -/
theorem circleFlow_increment_bounds_on_Icc
    {F : ℝ → ℝ → ℝ} {l r A B : ℝ} (hlr : l < r)
    (hcont : ∀ θ, ContinuousOn (fun t => F t θ) (Icc l r))
    (hdiff : ∀ t ∈ Ioo l r, Differentiable ℝ (F t))
    (hbound : ∀ t ∈ Ioo l r, ∀ θ, A ≤ deriv (F t) θ ∧ deriv (F t) θ ≤ B)
    {t : ℝ} (ht : t ∈ Icc l r) {x y : ℝ} (hxy : x ≤ y) :
    A * (y - x) ≤ F t y - F t x ∧ F t y - F t x ≤ B * (y - x) := by
  have hclosure : t ∈ closure (Ioo l r) := by
    rw [closure_Ioo hlr.ne]
    exact ht
  have : NeBot (𝓝[Ioo l r] t) := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hlim : Tendsto (fun s => F s y - F s x) (𝓝[Ioo l r] t)
      (𝓝 (F t y - F t x)) :=
    ((hcont y t ht).sub (hcont x t ht)).mono Ioo_subset_Icc_self
  have hb : ∀ᶠ s in 𝓝[Ioo l r] t,
      A * (y - x) ≤ F s y - F s x ∧ F s y - F s x ≤ B * (y - x) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ⟨mul_sub_le_image_sub_of_le_deriv (hdiff s hs)
        (fun θ => (hbound s hs θ).1) hxy,
      image_sub_le_mul_sub_of_deriv_le (hdiff s hs)
        (fun θ => (hbound s hs θ).2) hxy⟩
  exact ⟨ge_of_tendsto hlim (hb.mono fun _ h => h.1),
    le_of_tendsto hlim (hb.mono fun _ h => h.2)⟩

/-- The derivative bounds themselves pass to the closed radial interval when
the endpoint angular derivatives exist.  Joint continuity of those derivatives
is not needed. -/
theorem circleFlow_deriv_bounds_on_Icc
    {F : ℝ → ℝ → ℝ} {l r A B : ℝ} (hlr : l < r)
    (hcont : ∀ θ, ContinuousOn (fun t => F t θ) (Icc l r))
    (hdiff : ∀ t ∈ Icc l r, Differentiable ℝ (F t))
    (hbound : ∀ t ∈ Ioo l r, ∀ θ, A ≤ deriv (F t) θ ∧ deriv (F t) θ ≤ B)
    {t : ℝ} (ht : t ∈ Icc l r) (θ : ℝ) :
    A ≤ deriv (F t) θ ∧ deriv (F t) θ ≤ B := by
  have hlim : Tendsto (slope (F t) θ) (𝓝[>] θ) (𝓝 (deriv (F t) θ)) :=
    (hdiff t ht θ).hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE θ)
  have hb : ∀ᶠ u in 𝓝[>] θ, A ≤ slope (F t) θ u ∧ slope (F t) θ u ≤ B := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hinc := circleFlow_increment_bounds_on_Icc hlr hcont
      (fun s hs => hdiff s (Ioo_subset_Icc_self hs)) hbound ht hu.le
    rw [slope_def_field]
    exact ⟨(le_div_iff₀ (sub_pos.mpr hu)).2 hinc.1,
      (div_le_iff₀ (sub_pos.mpr hu)).2 hinc.2⟩
  exact ⟨ge_of_tendsto hlim (hb.mono fun _ h => h.1),
    le_of_tendsto hlim (hb.mono fun _ h => h.2)⟩

end ContinuousFlexibility.Analysis
