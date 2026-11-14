module

public import ContinuousFlexibility.Analysis.N01aReferenceGoodPointScales
public import ContinuousFlexibility.Analysis.N01aReferencePartitionSquares

/-!
# Weighted density on a compact right band

Only finitely many physical cells meet the band.  The partition square
bound and finite integral sums therefore suffice to convert a summable
weighted density into a quantitative band integral.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators

def n01aLocalizedDensity (D : ReferenceData) (e : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∫ r in D.a..D.b, D.localizer m r ^ 2 * e r

def n01aWeightedDensity (D : ReferenceData) (γ M : ℝ) (e : ℝ → ℝ) (m : ℕ) : ℝ :=
  Real.exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
    n01aLocalizedDensity D e m

theorem n01aLocalizedDensity_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    {e : ℝ → ℝ} (he : ∀ r, 0 ≤ e r) (m : ℕ) :
    0 ≤ n01aLocalizedDensity D e m :=
  intervalIntegral.integral_nonneg_of_forall hab
    (fun r => mul_nonneg (sq_nonneg _) (he r))

theorem n01aWeightedDensity_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    {e : ℝ → ℝ} (he : ∀ r, 0 ≤ e r) (γ M : ℝ) (m : ℕ) :
    0 ≤ n01aWeightedDensity D γ M e m :=
  mul_nonneg (Real.exp_pos _).le (n01aLocalizedDensity_nonneg hab he m)

/-- A finite cover of a compact band converts a pointwise lower bound for
its cell weights into an upper bound for the actual density integral. -/
theorem n01a_partition_finite_band_integral_bound {D : ReferenceData}
    (hD : RadialPartition D) (hab : D.a ≤ D.b) {l u : ℝ} (hlu : l ≤ u)
    (hcore : Icc l u ⊆ radialCore D) {e : ℝ → ℝ} (he : Continuous e)
    (he0 : ∀ r, 0 ≤ e r) (B : ℕ)
    (hB : ∀ r ∈ radialCore D, 1 ≤ (B : ℝ) * ∑' m, D.localizer m r ^ 2)
    (S : Finset ℕ) (hS : ∀ m, (D.cells m ∩ Icc l u).Nonempty → m ∈ S)
    (W : ℕ → ℝ) (hW : ∀ m, 0 ≤ W m)
    (hs : Summable (fun m => W m * n01aLocalizedDensity D e m))
    (L : ℝ) (hL : 0 ≤ L) (hw : ∀ m ∈ S, 1 ≤ L * W m) :
    (∫ r in l..u, e r) ≤ (B : ℝ) * L *
      ∑' m, W m * n01aLocalizedDensity D e m := by
  classical
  have hloc (m : ℕ) : Continuous (fun r => D.localizer m r ^ 2 * e r) :=
    ((hD.1 m).continuous.pow 2).mul he
  have hsumInt : IntervalIntegrable
      (fun r => ∑ m ∈ S, D.localizer m r ^ 2 * e r) volume l u := by
    simpa only [Finset.sum_fn] using
      (IntervalIntegrable.sum S (f := fun m r => D.localizer m r ^ 2 * e r)
        (fun m _ => (hloc m).intervalIntegrable l u))
  have hpoint (r : ℝ) (hr : r ∈ Icc l u) :
      e r ≤ (B : ℝ) * ∑ m ∈ S, D.localizer m r ^ 2 * e r := by
    have hzero (m : ℕ) (hm : m ∉ S) : D.localizer m r = 0 := by
      by_contra hne
      exact hm (hS m ⟨r, hD.2.2.1 m hne, hr⟩)
    have hsum : (∑' m, D.localizer m r ^ 2) = ∑ m ∈ S, D.localizer m r ^ 2 := by
      apply tsum_eq_sum
      intro m hm
      rw [hzero m hm, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    have hb := hB r (hcore hr)
    rw [hsum] at hb
    simpa only [one_mul, mul_assoc, Finset.sum_mul] using
      mul_le_mul_of_nonneg_right hb (he0 r)
  have hi := intervalIntegral.integral_mono_on hlu (he.intervalIntegrable _ _)
    (hsumInt.const_mul (B : ℝ)) hpoint
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun m _ => (hloc m).intervalIntegrable _ _)] at hi
  have hal : D.a ≤ l := (hcore ⟨le_rfl, hlu⟩).1.le
  have hub : u ≤ D.b := (hcore ⟨hlu, le_rfl⟩).2.le
  have hband (m : ℕ) : (∫ r in l..u, D.localizer m r ^ 2 * e r) ≤
      n01aLocalizedDensity D e m :=
    intervalIntegral.integral_mono_interval hal hlu hub
      (Eventually.of_forall fun r => mul_nonneg (sq_nonneg _) (he0 r))
      ((hloc m).intervalIntegrable _ _)
  have hweight (m : ℕ) (hm : m ∈ S) : n01aLocalizedDensity D e m ≤
      L * (W m * n01aLocalizedDensity D e m) := by
    have h := mul_le_mul_of_nonneg_right (hw m hm)
      (n01aLocalizedDensity_nonneg hab he0 m)
    simpa only [one_mul, mul_assoc] using h
  calc
    (∫ r in l..u, e r) ≤ (B : ℝ) *
        ∑ m ∈ S, ∫ r in l..u, D.localizer m r ^ 2 * e r := hi
    _ ≤ (B : ℝ) * ∑ m ∈ S, L * (W m * n01aLocalizedDensity D e m) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm =>
        (hband m).trans (hweight m hm)) (Nat.cast_nonneg B)
    _ = (B : ℝ) * L * ∑ m ∈ S, W m * n01aLocalizedDensity D e m := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (B : ℝ) * L * ∑' m, W m * n01aLocalizedDensity D e m :=
      mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum S (fun m _ =>
          mul_nonneg (hW m) (n01aLocalizedDensity_nonneg hab he0 m)))
        (mul_nonneg (Nat.cast_nonneg B) hL)

theorem n01a_weighted_density_right_band_integral {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) {e : ℝ → ℝ} (he : Continuous e)
    (he0 : ∀ r, 0 ≤ e r) {γ M : ℝ} (hγ : 0 < γ)
    (hs : Summable (n01aWeightedDensity D γ M e)) {p : ℝ}
    (hp : p ∈ radialCore D) :
    ∃ A N₀ : ℝ, 0 < A ∧ 0 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (∫ r in (D.b - Real.exp (-N ^ 2))..
        (D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2)), e r) ≤
        A * Real.exp (-(γ / 12) * N ^ 3) := by
  classical
  obtain ⟨B, hB⟩ := radialPartition_square_bound hD.2.1
  have hB' (r : ℝ) (hr : r ∈ radialCore D) :
      1 ≤ (B : ℝ) * ∑' m, D.localizer m r ^ 2 := by
    simpa only [one_pow, mul_one] using hB r hr 1
  obtain ⟨K, hK, hw⟩ := n01a_output_weight_on_deep_cells hγ M
  let T : ℝ := ∑' m, n01aWeightedDensity D γ M e m
  have hT : 0 ≤ T := tsum_nonneg (n01aWeightedDensity_nonneg hD.1.2.1.le he0 γ M)
  let A : ℝ := 1 + (B : ℝ) * K * T
  let N₀ : ℝ := 2 + |Real.log (D.b - p)| + 4 * (|Real.log (C 0)| + 2)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hN₀ : 0 < N₀ := by dsimp only [N₀]; positivity
  refine ⟨A, N₀, hA, hN₀, fun N hN => ?_⟩
  have hNpos : 0 ≤ N := (hN₀.trans_le hN).le
  have hgeo : 1 + |Real.log (D.b - p)| ≤ N := by
    dsimp only [N₀] at hN
    linarith [abs_nonneg (Real.log (C 0))]
  have hidx : 4 * (|Real.log (C 0)| + 2) ≤ N := by
    dsimp only [N₀] at hN
    linarith [abs_nonneg (Real.log (D.b - p))]
  let l : ℝ := D.b - Real.exp (-N ^ 2)
  let u : ℝ := D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2)
  have hlu : l ≤ u := by dsimp only [l, u]; linarith [Real.exp_pos (-N ^ 2)]
  have hcore : Icc l u ⊆ radialCore D :=
    fun _ hr => (n01a_right_band_mem_core hp hgeo hr).1
  have hfinite := hD.2.2.2.2.2.1 (Icc l u) isCompact_Icc hcore
  let S : Finset ℕ := hfinite.toFinset
  let W : ℕ → ℝ := fun m =>
    Real.exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))
  let L : ℝ := K * Real.exp (-(γ / 12) * N ^ 3)
  have hS (m : ℕ) (hm : (D.cells m ∩ Icc l u).Nonempty) : m ∈ S :=
    hfinite.mem_toFinset.mpr hm
  have hweight (m : ℕ) (hm : m ∈ S) : 1 ≤ L * W m := by
    obtain ⟨r, hrm, hr⟩ := hfinite.mem_toFinset.mp hm
    exact hw N (D.cellIndex m) hNpos
      (n01a_cell_index_ge_half_depth hD hidx hrm hr.1)
  change Summable (fun m => W m * n01aLocalizedDensity D e m) at hs
  have hi := n01a_partition_finite_band_integral_bound hD.2.1 hD.1.2.1.le
    hlu hcore he he0 B hB' S hS W (fun _ => (Real.exp_pos _).le) hs L
    (mul_nonneg hK.le (Real.exp_pos _).le) hweight
  change (∫ r in l..u, e r) ≤ A * Real.exp (-(γ / 12) * N ^ 3)
  calc
    (∫ r in l..u, e r) ≤ (B : ℝ) * L * T := hi
    _ = ((B : ℝ) * K * T) * Real.exp (-(γ / 12) * N ^ 3) := by
      dsimp only [L]
      ring
    _ ≤ A * Real.exp (-(γ / 12) * N ^ 3) :=
      mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith) (Real.exp_pos _).le

end ContinuousFlexibility.Statements
