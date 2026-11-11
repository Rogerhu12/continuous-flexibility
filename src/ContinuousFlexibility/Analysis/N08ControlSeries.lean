import ContinuousFlexibility.Analysis.N08ControlLabelDecay

/-!
# Actual locally finite control series with arbitrary scalar coefficients

The coefficients need no summability assumption. Local finiteness of the
given smooth controls identifies the series with a finite sum near each
interior point; disjointness then bounds each jet by its sole active term.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}

def n08ControlSeries (C : NonlinearGeometryData S) (a : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑' m, a m * C.control m r

def n08ActiveControls (hC : controlGeometryConditions D S C) (r : ℝ) : Finset ℕ :=
  (n08_controlActive_subsingleton hC r).finite.toFinset

theorem n08_mem_activeControls (hC : controlGeometryConditions D S C) (r : ℝ) (m : ℕ) :
    m ∈ n08ActiveControls hC r ↔ C.control m r ≠ 0 :=
  Set.Finite.mem_toFinset _

theorem n08ControlSeries_eq_sum (hC : controlGeometryConditions D S C)
    (a : ℕ → ℝ) (r : ℝ) :
    n08ControlSeries C a r = ∑ m ∈ n08ActiveControls hC r, a m * C.control m r := by
  classical
  apply tsum_eq_sum
  intro m hm
  have hz : C.control m r = 0 :=
    not_not.mp (mt (n08_mem_activeControls hC r m).mpr hm)
  rw [hz, mul_zero]

theorem n08ControlSeries_contDiffOn (hC : controlGeometryConditions D S C)
    (a : ℕ → ℝ) : ContDiffOn ℝ ∞ (n08ControlSeries C a) (Ioo D.a D.b) := by
  classical
  obtain ⟨_, _, _, _, _, hcontrol, hfinite, _⟩ := hC
  intro r hr
  obtain ⟨t, ht, htf⟩ := hfinite ⟨r, hr⟩
  let indices := htf.toFinset
  have hn : (Subtype.val : Ioo D.a D.b → ℝ) '' t ∈ 𝓝 r :=
    isOpen_Ioo.isOpenMap_subtype_val.image_mem_nhds ht
  have heq : n08ControlSeries C a =ᶠ[𝓝 r]
      (fun y => ∑ m ∈ indices, a m * C.control m y) := by
    filter_upwards [hn] with y hy
    obtain ⟨z, hzt, rfl⟩ := hy
    apply tsum_eq_sum
    intro m hm
    have hz : C.control m z = 0 := by
      by_contra hne
      exact hm (htf.mem_toFinset.mpr ⟨z, hne, hzt⟩)
    rw [hz, mul_zero]
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ m ∈ indices, a m * C.control m y) r :=
    ContDiffAt.sum fun m _ => contDiffAt_const.mul (hcontrol m).1.contDiffAt
  exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt

theorem n08ControlSeries_zero_off_core (hC : controlGeometryConditions D S C)
    (a : ℕ → ℝ) {r : ℝ} (hr : r ∉ Ioo D.a D.b) : n08ControlSeries C a r = 0 := by
  obtain ⟨hI, _, _, _, _, hcontrol, _⟩ := hC
  have hz (m : ℕ) : C.control m r = 0 := by
    by_contra hne
    have hm := (hcontrol m).2.2 hne
    exact hr ⟨(hI m).1.trans hm.1, hm.2.trans (hI m).2.2⟩
  simp only [n08ControlSeries, hz, mul_zero, tsum_zero]

theorem n08ControlSeries_jet_bound (hC : controlGeometryConditions D S C)
    (a : ℕ → ℝ) (n : ℕ) {r W : ℝ} (hr : r ∈ Ioo D.a D.b) (hW : 0 ≤ W)
    (hterm : ∀ m, r ∈ Ioo (C.left m) (C.right m) →
      |a m * iteratedDeriv n (C.control m) r| ≤ W) :
    |iteratedDeriv n (n08ControlSeries C a) r| ≤ W := by
  classical
  obtain ⟨_, _, hdisjoint, _, _, hcontrol, hfinite, _⟩ := hC
  obtain ⟨t, ht, htf⟩ := hfinite ⟨r, hr⟩
  let indices := htf.toFinset
  have hn : (Subtype.val : Ioo D.a D.b → ℝ) '' t ∈ 𝓝 r :=
    isOpen_Ioo.isOpenMap_subtype_val.image_mem_nhds ht
  have heq : n08ControlSeries C a =ᶠ[𝓝 r]
      (fun y => ∑ m ∈ indices, a m * C.control m y) := by
    filter_upwards [hn] with y hy
    obtain ⟨z, hzt, rfl⟩ := hy
    apply tsum_eq_sum
    intro m hm
    have hz : C.control m z = 0 := by
      by_contra hne
      exact hm (htf.mem_toFinset.mpr ⟨z, hne, hzt⟩)
    rw [hz, mul_zero]
  have hd (m : ℕ) : ContDiffAt ℝ n (fun y => a m * C.control m y) r :=
    (contDiffAt_const.mul (hcontrol m).1.contDiffAt).of_le (by simp)
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_fun_sum (fun m _ => hd m)]
  simp_rw [iteratedDeriv_const_mul_field]
  by_cases h : ∃ m ∈ indices, r ∈ Ioo (C.left m) (C.right m)
  · obtain ⟨m, hm, hmr⟩ := h
    rw [Finset.sum_eq_single_of_mem m hm]
    · exact hterm m hmr
    · intro i _ hi
      have hnot : r ∉ Ioo (C.left i) (C.right i) := fun hir =>
        Set.disjoint_left.mp (hdisjoint i m hi) hir hmr
      rw [n08_iteratedDeriv_zero_off_open_interval (hcontrol i).1 (hcontrol i).2.2 n hnot,
        mul_zero]
  · have hz : ∑ i ∈ indices, a i * iteratedDeriv n (C.control i) r = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hnot : r ∉ Ioo (C.left i) (C.right i) := fun hir => h ⟨i, hi, hir⟩
      rw [n08_iteratedDeriv_zero_off_open_interval (hcontrol i).1 (hcontrol i).2.2 n hnot,
        mul_zero]
    rwa [hz, abs_zero]

end ContinuousFlexibility.Statements
