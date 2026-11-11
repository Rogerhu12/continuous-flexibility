import ContinuousFlexibility.Analysis.StateProfileRegularity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Passing control estimates through the actual profile sum

The controls are smooth and supported in disjoint open negative components.
Every derivative vanishes on the complement of its own component, including
both turning points. The derivatives of the actual locally finite sum
therefore obey the same uniform estimate as the individual active term.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

/-- Every jet vanishes outside the open support interval, including its endpoints. -/
theorem iteratedDeriv_zero_off_open_interval {a b r : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : Function.support f ⊆ Ioo a b)
    (n : ℕ) (hr : r ∉ Ioo a b) : iteratedDeriv n f r = 0 := by
  have hc : IsClosed {x : ℝ | iteratedDeriv n f x = 0} :=
    isClosed_eq (hf.continuous_iteratedDeriv n (by simp)) continuous_const
  by_cases ha : r ≤ a
  · have hzero : Iio a ⊆ {x : ℝ | iteratedDeriv n f x = 0} := by
      intro x hx
      have heq : f =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        change f y = 0
        by_contra h
        exact (not_lt_of_ge (hs h).1.le) hy
      change iteratedDeriv n f x = 0
      simpa only [iteratedDeriv_const_zero] using heq.iteratedDeriv_eq n
    apply closure_minimal hzero hc
    rwa [closure_Iio]
  · have hb : b ≤ r := le_of_not_gt fun hb => hr ⟨lt_of_not_ge ha, hb⟩
    have hzero : Ioi b ⊆ {x : ℝ | iteratedDeriv n f x = 0} := by
      intro x hx
      have heq : f =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        change f y = 0
        by_contra h
        exact (not_lt_of_ge (hs h).2.le) hy
      change iteratedDeriv n f x = 0
      simpa only [iteratedDeriv_const_zero] using heq.iteratedDeriv_eq n
    apply closure_minimal hzero hc
    rwa [closure_Ioi]

/-- An absolute bound valid on each individual component controls the
derivative of the actual sum at every point of the core. -/
theorem abs_iteratedDeriv_stateControlSum_le {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hC : controlGeometryConditions D S C) (x : AnnularState S)
    (n : ℕ) {r W : ℝ} (hr : r ∈ Ioo D.a D.b) (hW : 0 ≤ W)
    (hterm : ∀ m, r ∈ Ioo (C.left m) (C.right m) →
      |stateKappa S x m * iteratedDeriv n (C.control m) r| ≤ W) :
    |iteratedDeriv n (stateControlSum C x) r| ≤ W := by
  classical
  obtain ⟨_, _, hdisjoint, _, _, hcontrol, hfinite, _⟩ := hC
  have hs : IsOpen (Ioo D.a D.b) := isOpen_Ioo
  obtain ⟨t, ht, htf⟩ := hfinite ⟨r, hr⟩
  let indices := htf.toFinset
  have hn : (Subtype.val : Ioo D.a D.b → ℝ) '' t ∈ 𝓝 r :=
    hs.isOpenMap_subtype_val.image_mem_nhds ht
  have heq : stateControlSum C x =ᶠ[𝓝 r]
      (fun y => ∑ m ∈ indices, stateKappa S x m * C.control m y) := by
    filter_upwards [hn] with y hy
    obtain ⟨z, hzt, rfl⟩ := hy
    unfold stateControlSum
    apply tsum_eq_sum
    intro m hm
    have hz : C.control m z = 0 := by
      by_contra hne
      exact hm (htf.mem_toFinset.mpr ⟨z, hne, hzt⟩)
    rw [hz, mul_zero]
  have hd (m : ℕ) : ContDiffAt ℝ n (fun y => stateKappa S x m * C.control m y) r :=
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
      rw [iteratedDeriv_zero_off_open_interval (hcontrol i).1 (hcontrol i).2.2 n hnot,
        mul_zero]
  · have hz : ∑ i ∈ indices, stateKappa S x i * iteratedDeriv n (C.control i) r = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hnot : r ∉ Ioo (C.left i) (C.right i) := fun hir => h ⟨i, hi, hir⟩
      rw [iteratedDeriv_zero_off_open_interval (hcontrol i).1 (hcontrol i).2.2 n hnot,
        mul_zero]
    rwa [hz, abs_zero]

/-- The quantitative control estimates at one actual state imply the
smoothness of that state's controlled profile through both ends. -/
theorem contDiff_stateProfile_of_control_jet_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hT : IsMaterialData D T) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hC : controlGeometryConditions D S C) (x : AnnularState S)
    {γ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ n : ℕ, ∃ K A : ℝ, 0 ≤ K ∧ ∀ m r,
      r ∈ Ioo D.a D.b → r ∈ Ioo (C.left m) (C.right m) →
      |stateKappa S x m * iteratedDeriv n (C.control m) r| ≤ K * T.H r ^ γ * T.M r ^ A) :
    ContDiff ℝ ∞ (stateProfile D S C x) := by
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, hdecay, _⟩ := hdata
  have hlimit (n : ℕ) {l : Filter ℝ}
      (hcore : ∀ᶠ r in l, r ∈ Ioo D.a D.b)
      (hend : ∀ A : ℝ, Tendsto (fun r => T.H r ^ γ * T.M r ^ A) l (𝓝 0)) :
      Tendsto (iteratedDeriv n (stateControlSum C x)) l (𝓝 0) := by
    obtain ⟨K, A, hK, hterm⟩ := hbound n
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (g := fun r => K * (T.H r ^ γ * T.M r ^ A))
    · filter_upwards [hcore] with r hr
      rw [← mul_assoc]
      have hp := hpos r hr
      exact abs_iteratedDeriv_stateControlSum_le hC x n hr
        (mul_nonneg (mul_nonneg hK (Real.rpow_pos_of_pos hp.2.1 _).le)
          (Real.rpow_pos_of_pos (zero_lt_one.trans_le hp.2.2.2) _).le)
        (fun m hm => hterm m r hr hm)
    · simpa only [mul_zero] using (hend A).const_mul K
  apply contDiff_stateProfile_of_flat_control_sum hD hχ hC x
  · intro n
    have hcore : ∀ᶠ r in 𝓝[>] D.a, r ∈ Ioo D.a D.b := by
      filter_upwards [eventually_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hD.2.1)] with r ha hb
      exact ⟨ha, hb⟩
    exact hlimit n hcore (fun A => (hdecay A γ hγ).choose_spec.2.2.1)
  · intro n
    have hcore : ∀ᶠ r in 𝓝[<] D.b, r ∈ Ioo D.a D.b := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hD.2.1),
        eventually_mem_nhdsWithin] with r ha hb
      exact ⟨ha, hb⟩
    exact hlimit n hcore (fun A => (hdecay A γ hγ).choose_spec.2.2.2)

end ContinuousFlexibility.Statements
