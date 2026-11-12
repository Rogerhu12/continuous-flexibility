import ContinuousFlexibility.Analysis.N01aComponentCountingDensity

/-!
# Host indices of components before a right-endpoint good point

Every intersection point with `[p,r]` has a fixed left-endpoint margin and
the same right-endpoint margin as `r`. The physical cell-distance estimate
therefore bounds every possible host index, independently of how hosts are
chosen for individual components.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem exists_n01a_cell_index_bound_before_right_band {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) {p : ℝ} (hp : p ∈ radialCore D) :
    ∃ H : ℝ, 0 < H ∧ ∀ N r y : ℝ, 0 ≤ N → p ≤ y → y ≤ r →
      r ≤ D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2) →
      ∀ m : ℕ, y ∈ D.cells m → (D.cellIndex m : ℝ) ≤ H * (1 + N) := by
  have hC : 0 < C 0 := hD.2.2.1 0
  let k : ℝ := min (p - D.a) (1 / 2 : ℝ)
  have hk : 0 < k := lt_min (sub_pos.mpr hp.1) (by norm_num)
  have hkLeft : k ≤ p - D.a := min_le_left _ _
  have hkHalf : k ≤ (1 / 2 : ℝ) := min_le_right _ _
  let L : ℝ := Real.log (C 0) - Real.log k
  let H : ℝ := 2 + |L|
  have hH : 0 < H := by dsimp [H]; positivity
  have hHone : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg L]
  have hLH : L ≤ H ^ 2 := by
    have hLH' : L ≤ H := by dsimp [H]; linarith [le_abs_self L]
    exact hLH'.trans (le_self_pow₀ hHone (by norm_num))
  refine ⟨H, hH, fun N r y hN hpy hyr hr m hym => ?_⟩
  have hexp : Real.exp (-N ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg N))
  have hleft : k * Real.exp (-N ^ 2) ≤ y - D.a := by
    calc
      k * Real.exp (-N ^ 2) ≤ k * 1 := mul_le_mul_of_nonneg_left hexp hk.le
      _ = k := mul_one k
      _ ≤ p - D.a := hkLeft
      _ ≤ y - D.a := sub_le_sub_right hpy _
  have hright : k * Real.exp (-N ^ 2) ≤ D.b - y := by
    have hhalf := mul_le_mul_of_nonneg_right hkHalf (Real.exp_pos (-N ^ 2)).le
    linarith only [hhalf, hyr, hr]
  have hdist : min (y - D.a) (D.b - y) ≤ C 0 * Real.exp (-(D.cellIndex m : ℝ) ^ 2) :=
    (hD.2.2.2.2.2.2.1 m y hym).2
  have hcompare := (le_min hleft hright).trans hdist
  have hlog := Real.log_le_log (mul_pos hk (Real.exp_pos _)) hcompare
  rw [Real.log_mul hk.ne' (Real.exp_pos _).ne', Real.log_mul hC.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp] at hlog
  have hsquare : (D.cellIndex m : ℝ) ^ 2 ≤ N ^ 2 + L := by
    dsimp only [L]
    linarith only [hlog]
  have hsum : (D.cellIndex m : ℝ) ^ 2 ≤ (N + H) ^ 2 := by
    nlinarith only [hsquare, hLH, mul_nonneg hN hH.le]
  have hindex : (D.cellIndex m : ℝ) ≤ N + H :=
    (sq_le_sq₀ (Nat.cast_nonneg _) (add_nonneg hN hH.le)).mp hsum
  have hscale : N + H ≤ H * (1 + N) := by
    have hh := mul_le_mul_of_nonneg_right hHone hN
    nlinarith only [hh]
  exact hindex.trans hscale

/-- The bound applies to every host of every component meeting the interval. -/
theorem exists_n01a_component_host_index_bound {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) {p : ℝ} (hp : p ∈ radialCore D) :
    ∃ H : ℝ, 0 < H ∧ ∀ N r : ℝ, 0 ≤ N →
      r ≤ D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2) →
      ∀ hr : r ∈ radialCore D, ∀ J ∈ n01aNegativeComponentsMeeting hD.1 hp hr,
        ∀ m : ℕ, J.interval ⊆ D.cells m → (D.cellIndex m : ℝ) ≤ H * (1 + N) := by
  obtain ⟨H, hH, hbound⟩ := exists_n01a_cell_index_bound_before_right_band hD hp
  refine ⟨H, hH, fun N r hN hrBand hr J hJS m hhost => ?_⟩
  obtain ⟨y, hyJ, hyp, hyr⟩ := (mem_n01aNegativeComponentsMeeting hD.1 hp hr J).mp hJS
  exact hbound N r y hN hyp hyr hrBand m (hhost hyJ)

/-- A supplied family of actual good points gives linearly many distinct
components with linearly bounded chosen host indices. -/
theorem exists_n01a_component_density_witnesses {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) (hR : RadialReturnMargins D)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hJ : ∀ r ∈ radialCore D, Radial.radialJacobi 4 D.w u r = 0)
    {p : ℝ} (hp : p ∈ radialCore D) (henergy : 0 < n01aJacobiEnergy u p)
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    (host : N01aNegativeComponent D → ℕ)
    (hhost : ∀ J, J.interval ⊆ D.cells (host J))
    {N₀ : ℝ}
    (hgood : ∀ N : ℝ, N₀ ≤ N → ∃ r : ℝ, r ∈ radialCore D ∧ p ≤ r ∧
      r ≤ D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2) ∧
      n01aJacobiEnergy u r ≤ A * Real.exp (-c * N ^ 3)) :
    ∃ d H : ℝ, 0 < d ∧ 0 < H ∧ ∀ N : ℝ, max N₀ 1 ≤ N →
      ∃ S : Finset (N01aNegativeComponent D),
        d * N - 1 ≤ (S.card : ℝ) ∧
        ∀ J ∈ S, (D.cellIndex (host J) : ℝ) ≤ H * (1 + N) := by
  obtain ⟨H, hH, hHostBound⟩ := exists_n01a_component_host_index_bound hD hp
  obtain ⟨d, hd, hcount⟩ := exists_n01a_component_count_slope hD hR hu hJ hp henergy hA hc hH.le
  refine ⟨d, H, hd, hH, fun N hN => ?_⟩
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨r, hr, hpr, hband, hdecay⟩ := hgood N hN₀
  let S : Finset (N01aNegativeComponent D) := n01aNegativeComponentsMeeting hD.1 hp hr
  have hb : ∀ J ∈ S, (D.cellIndex (host J) : ℝ) ≤ H * (1 + N) :=
    fun J hJS => hHostBound N r (zero_le_one.trans hN1) hband hr J hJS (host J) (hhost J)
  refine ⟨S, ?_, hb⟩
  exact hcount N r hN1 hr hpr hdecay (fun J hJS => ⟨host J, hhost J, hb J hJS⟩)

end ContinuousFlexibility.Statements
