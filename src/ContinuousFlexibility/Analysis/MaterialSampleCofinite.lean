module

public import ContinuousFlexibility.Analysis.StateKappaBounds
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Material samples escape every compact interior interval

The cell partition is locally finite on compact subsets of the open radial
interval. Thus the sample points approach the two endpoints jointly along
the cofinite filter, without choosing one of the endpoints. A bounded change
of cell index preserves the cofinite filter. These qualitative facts suffice
for endpoint closure of locally finite control sums.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology

/-- The actual cell samples eventually leave each closed interior collar. -/
theorem materialSample_endpointDistance_tendsto_zero
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    Tendsto (fun m => endpointDistance D (T.sample m)) cofinite (𝓝 0) := by
  obtain ⟨C, hbounds⟩ := hRef
  have hsample : ∀ m, T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hbounds.2.1
  have hsampleCell : ∀ m, T.sample m ∈ D.cells m := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
    exact hs
  have hlocal : ∀ K : Set ℝ, IsCompact K → K ⊆ radialCore D →
      {m | (D.cells m ∩ K).Nonempty}.Finite := hbounds.2.2.2.2.2.1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K : Set ℝ := Icc (D.a + ε) (D.b - ε)
  have hK : K ⊆ radialCore D := by
    intro r hr
    exact ⟨by linarith only [hr.1, hε], by linarith only [hr.2, hε]⟩
  have hfinite := hlocal K isCompact_Icc hK
  filter_upwards [hfinite.eventually_cofinite_notMem] with m hm
  have hpos : 0 ≤ endpointDistance D (T.sample m) :=
    le_min (sub_nonneg.mpr (hsample m).1.le) (sub_nonneg.mpr (hsample m).2.le)
  have hlt : endpointDistance D (T.sample m) < ε := by
    by_contra hnot
    have hle := le_min_iff.mp (le_of_not_gt hnot)
    apply hm
    refine ⟨T.sample m, hsampleCell m, ?_⟩
    exact ⟨by linarith only [hle.1], by linarith only [hle.2]⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hpos] using hlt

/-- A common inward limit at the two endpoints is also the limit along
the material samples, even when successive samples alternate endpoints. -/
theorem materialSample_tendsto_zero_of_endpoint_limits
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) {f : ℝ → ℝ}
    (ha : Tendsto f (𝓝[>] D.a) (𝓝 0))
    (hb : Tendsto f (𝓝[<] D.b) (𝓝 0)) :
    Tendsto (fun m => f (T.sample m)) cofinite (𝓝 0) := by
  have hsample : ∀ m, T.sample m ∈ Ioo D.a D.b := by
    obtain ⟨_, hbounds⟩ := hRef
    exact materialSample_mem_radialCore hT hbounds.2.1
  have hdist := materialSample_endpointDistance_tendsto_zero hT hRef
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hleft := (Metric.tendsto_nhds.mp ha) ε hε
  have hright := (Metric.tendsto_nhds.mp hb) ε hε
  obtain ⟨u, hu, hleft'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hleft
  obtain ⟨l, hl, hright'⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hright
  have hδ : 0 < min (u - D.a) (D.b - l) :=
    lt_min (sub_pos.mpr hu) (sub_pos.mpr hl)
  filter_upwards [hdist.eventually (Iio_mem_nhds hδ)] with m hm
  rcases min_lt_iff.mp hm with hm | hm
  · exact hleft' ⟨(hsample m).1,
      by linarith only [hm, min_le_left (u - D.a) (D.b - l)]⟩
  · exact hright' ⟨by linarith only [hm, min_le_right (u - D.a) (D.b - l)],
      (hsample m).2⟩

/-- A bounded change of the physical cell index has finite fibres. -/
theorem controlCell_tendsto_cofinite {D : ReferenceData}
    (hRef : IsAccumulatingProfile D) (cell : ℕ → ℕ) {B : ℝ}
    (hindex : ∀ m, |(D.cellIndex (cell m) : ℝ) - D.cellIndex m| ≤ B) :
    Tendsto cell cofinite cofinite := by
  obtain ⟨_, hbounds⟩ := hRef
  have hfinite : ∀ N : ℕ, {m | D.cellIndex m ≤ N}.Finite := hbounds.2.2.2.2.1
  apply Tendsto.cofinite_of_finite_preimage_singleton
  intro j
  obtain ⟨N, hN⟩ := exists_nat_ge ((D.cellIndex j : ℝ) + B)
  apply (hfinite N).subset
  intro m hm
  have hm' : cell m = j := hm
  have hshift := (abs_le.mp (hindex m)).1
  rw [hm'] at hshift
  have hle : (D.cellIndex m : ℝ) ≤ N := by linarith only [hshift, hN]
  exact_mod_cast hle

end ContinuousFlexibility.Statements
