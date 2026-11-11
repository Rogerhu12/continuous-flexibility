import ContinuousFlexibility.Analysis.N01aComponentCountingTransfer

/-!
# Linear density forced by cubic Jacobi-energy decay

At points approaching the right endpoint, the signed logarithmic endpoint
term has a fixed upper bound. Each component with host index at most a
linear function of the depth has quadratic logarithmic cost. A genuine
pointwise cubic energy-decay estimate therefore forces a linear number of
distinct negative components before that point.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

theorem exists_n01a_profile_log_upper {D : ReferenceData} (hD : RadialProfileGeometry D) :
    ∃ U : ℝ, ∀ r ∈ radialCore D, Real.log (D.w r) ≤ U := by
  have hw : Continuous D.w := hD.2.2.1.1.continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).exists_bound_of_continuousOn
    hw.continuousOn
  let W : ℝ := |M| + 1
  refine ⟨Real.log W, fun r hr => ?_⟩
  have hbound : D.w r ≤ W := by
    have hh : |D.w r| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM r ⟨hr.1.le, hr.2.le⟩
    exact (le_abs_self _).trans (hh.trans (by dsimp [W]; linarith [le_abs_self M]))
  exact Real.log_le_log (hD.2.2.2.2.1 r hr) hbound

theorem exists_n01a_component_drop_constant {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 0 ≤ N → ∀ (J : N01aNegativeComponent D) (m : ℕ),
      J.interval ⊆ D.cells m → (D.cellIndex m : ℝ) ≤ N →
      Real.log (D.w J.left) - Real.log (D.w J.right) ≤ K * (1 + N ^ 2) := by
  obtain ⟨K, hK, hk⟩ := n01a_negativeComponent_variation_uniform_bound hD
  obtain ⟨C, hprofile⟩ := hD
  refine ⟨K, hK, fun N hN J m hcell hm => ?_⟩
  have hsq : (D.cellIndex m : ℝ) ^ 2 ≤ N ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hN).mpr hm
  rw [← J.integral_abs_logDerivative hprofile.1]
  exact (hk J m hcell).trans (mul_le_mul_of_nonneg_left (add_le_add_left hsq 1) hK.le)

/-- The count uses the actual finite set of components meeting `[p,r]`.
The energy estimate and the host-index estimate are intermediate inputs;
all constants in the conclusion are uniform in the depth and good point. -/
theorem exists_n01a_component_count_slope {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) (hR : RadialReturnMargins D)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hJ : ∀ r ∈ radialCore D, Radial.radialJacobi 4 D.w u r = 0)
    {p : ℝ} (hp : p ∈ radialCore D) (henergy : 0 < n01aJacobiEnergy u p)
    {A c H : ℝ} (hA : 0 < A) (hc : 0 < c) (hH : 0 ≤ H) :
    ∃ d : ℝ, 0 < d ∧ ∀ N r : ℝ, 1 ≤ N →
      ∀ hr : r ∈ radialCore D, p ≤ r →
      n01aJacobiEnergy u r ≤ A * Real.exp (-c * N ^ 3) →
      (∀ J ∈ n01aNegativeComponentsMeeting hD.1 hp hr,
        ∃ m : ℕ, J.interval ⊆ D.cells m ∧ (D.cellIndex m : ℝ) ≤ H * (1 + N)) →
      d * N - 1 ≤ ((n01aNegativeComponentsMeeting hD.1 hp hr).card : ℝ) := by
  classical
  obtain ⟨K, hK, hdrop⟩ := exists_n01a_component_drop_constant (show IsAccumulatingProfile D from ⟨C, hD⟩)
  obtain ⟨U, hU⟩ := exists_n01a_profile_log_upper hD.1
  let κ : ℝ := 4 / D.a + 2
  have hκ : 0 < κ := by
    have hα : 0 < D.a := hD.1.1
    dsimp [κ]
    positivity
  let F : ℝ := 2 * κ * K * (1 + 2 * H ^ 2)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let B₀ : ℝ := (D.b - D.a) + κ * (U - Real.log (D.w p)) +
    Real.log A - Real.log (n01aJacobiEnergy u p)
  let B : ℝ := 1 + |B₀| + F
  have hB : 0 < B := by dsimp [B]; positivity
  have hB₀ : B₀ ≤ B := by dsimp [B]; linarith [le_abs_self B₀]
  have hFB : F ≤ B := by dsimp [B]; linarith [abs_nonneg B₀]
  refine ⟨c / (2 * B), div_pos hc (mul_pos (by norm_num) hB), ?_⟩
  intro N r hN hr hpr hdecay hhosts
  let S : Finset (N01aNegativeComponent D) := n01aNegativeComponentsMeeting hD.1 hp hr
  have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hcover : ∀ x ∈ Ioo p r, deriv D.w x < 0 → ∃ J ∈ S, x ∈ J.interval := by
    intro x hx hneg
    obtain ⟨l, h, hcomp, hxcomp⟩ := hR.1 x ⟨hp.1.trans hx.1, hx.2.trans hr.2⟩ hneg
    let J : N01aNegativeComponent D := ⟨(l, h), hcomp⟩
    refine ⟨J, (mem_n01aNegativeComponentsMeeting hD.1 hp hr J).mpr ?_, hxcomp⟩
    exact ⟨x, hxcomp, Ioo_subset_Icc_self hx⟩
  have hcap : 0 ≤ H * (1 + N) := mul_nonneg hH (by linarith)
  have hpoly : 1 + (H * (1 + N)) ^ 2 ≤ (1 + 2 * H ^ 2) * (1 + N ^ 2) := by
    nlinarith only [sq_nonneg N, mul_nonneg (sq_nonneg H) (sq_nonneg (N - 1))]
  let M : ℝ := K * (1 + 2 * H ^ 2) * (1 + N ^ 2)
  have hdropN : ∀ J ∈ S, Real.log (D.w J.left) - Real.log (D.w J.right) ≤ M := by
    intro J hJS
    obtain ⟨m, hm, hindex⟩ := hhosts J hJS
    have hb := (hdrop (H * (1 + N)) hcap J m hm hindex).trans
      (mul_le_mul_of_nonneg_left hpoly hK.le)
    simpa only [M, mul_assoc] using hb
  have hlog : Real.log (D.w r) - Real.log (D.w p) ≤ U - Real.log (D.w p) :=
    sub_le_sub_right (hU r hr) _
  have hforced := n01a_component_energy_decay_bound hD.1 hu hp hr hpr
    (fun x hx => hJ x ⟨hp.1.trans_le hx.1, hx.2.trans_lt hr.2⟩)
    S hcover hA henergy hdecay hlog hdropN
  have hlength : r - p ≤ D.b - D.a := by linarith [hp.1, hr.2]
  have hcost :
      (r - p) + (4 / D.a + 2) * (U - Real.log (D.w p) + 2 * (S.card : ℝ) * M) +
          Real.log A - Real.log (n01aJacobiEnergy u p) ≤
        B₀ + F * (1 + N ^ 2) * (S.card : ℝ) := by
    calc
      _ ≤ (D.b - D.a) + (4 / D.a + 2) *
          (U - Real.log (D.w p) + 2 * (S.card : ℝ) * M) +
            Real.log A - Real.log (n01aJacobiEnergy u p) := by linarith only [hlength]
      _ = _ := by dsimp [B₀, F, M, κ]; ring
  have hone : 1 ≤ 1 + N ^ 2 := by nlinarith [sq_nonneg N]
  have hbase : B₀ ≤ B * (1 + N ^ 2) :=
    hB₀.trans (le_mul_of_one_le_right hB.le hone)
  have hterm : F * (1 + N ^ 2) * (S.card : ℝ) ≤ B * (1 + N ^ 2) * (S.card : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hFB (zero_le_one.trans hone)) hcard
  have hquadratic : c * N ^ 3 ≤ B * (1 + N ^ 2) * ((S.card : ℝ) + 1) := by
    calc
      _ ≤ B₀ + F * (1 + N ^ 2) * (S.card : ℝ) := hforced.trans hcost
      _ ≤ B * (1 + N ^ 2) + B * (1 + N ^ 2) * (S.card : ℝ) := add_le_add hbase hterm
      _ = _ := by ring
  exact n01a_linear_count_of_cubic_bound hc hB hN hcard hquadratic

end ContinuousFlexibility.Statements
