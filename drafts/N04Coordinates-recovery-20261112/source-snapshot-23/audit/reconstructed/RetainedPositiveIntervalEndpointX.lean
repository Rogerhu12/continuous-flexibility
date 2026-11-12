import ContinuousFlexibility.Analysis.RetainedPositiveComponentClassification
import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapEndpointX
import ContinuousFlexibility.Analysis.PositiveComponentMaterialCell
import Mathlib.Topology.Order.Compact

/-!
# Uniform endpoint coordinates on the actual whole positive intervals

The same retained tail gaps have their true closed-interval oscillation.
The remaining components form a finite set and have genuine interior
endpoints, so compactness supplies one bound for their entire intervals.
The actual midpoint and its original host sample are then compared using
the material index estimate; no whole-component cell is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem retainedReference_positive_closed_interval_X_oscillation
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {E : PhysicalSpacesData} {C : NonlinearGeometryData E}
    (hC : controlGeometryConditions Γ.reference E C)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (r s : ℝ), r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) →
        s ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) →
        |endpointX 1 (Statements.endpointDistance Γ.reference r) -
          endpointX 1 (Statements.endpointDistance Γ.reference s)| ≤ L := by
  classical
  let I := N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w)
  let X : ℝ → ℝ := fun r => endpointX 1 (Statements.endpointDistance Γ.reference r)
  have hd : Continuous (Statements.endpointDistance Γ.reference) :=
    (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)
  have hp (r : ℝ) (hr : r ∈ Ioo Γ.reference.a Γ.reference.b) :
      0 < Statements.endpointDistance Γ.reference r :=
    lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hX : ContinuousOn X (Ioo Γ.reference.a Γ.reference.b) :=
    ((continuousOn_const.div hd.continuousOn
      (fun r hr => (hp r hr).ne')).log
        (fun r hr => (div_pos zero_lt_one (hp r hr)).ne')).sqrt
  have hcompact (i : I) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
        |X r - X (n04PositiveMidpoint i)| ≤ B := by
    have hl := (retainedReference_positive_endpoints_interior
      P hS hband hq hΓ hw hcoordinates i false).1.1
    have hr := (retainedReference_positive_endpoints_interior
      P hS hband hq hΓ hw hcoordinates i true).1.2
    have hsub : Icc (n04PositiveLeft i) (n04PositiveRight i) ⊆
        Ioo Γ.reference.a Γ.reference.b :=
      fun r hr' => ⟨hl.trans_le hr'.1, hr'.2.trans_lt hr⟩
    have hf : ContinuousOn (fun r => |X r - X (n04PositiveMidpoint i)|)
        (Icc (n04PositiveLeft i) (n04PositiveRight i)) :=
      ((hX.mono hsub).sub continuousOn_const).abs
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf
    exact ⟨max B 0, le_max_right _ _, fun r hr' =>
      (hB ⟨r, hr', rfl⟩).trans (le_max_left _ _)⟩
  choose A hA hbound using hcompact
  let U : Set I := {i | ¬ ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
    n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
    n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n}
  have hfinite : U.Finite :=
    (retainedReference_positive_gap_exceptions_finite
      P hS hband hq hΓ hw hcoordinates hC).1
  obtain ⟨B, hB⟩ := (hfinite.image A).bddAbove
  obtain ⟨L, hL, htail⟩ :=
    retainedReference_positive_gap_endpointX_oscillation P hS hband hcoordinates hT
  refine ⟨max L (2 * max B 0), hL.trans (le_max_left _ _), ?_⟩
  intro i r s hr hs
  by_cases hi : i ∈ U
  · have hAi : A i ≤ max B 0 := (hB ⟨i, hi, rfl⟩).trans (le_max_left _ _)
    have hrb := (hbound i r hr).trans hAi
    have hsb : |X (n04PositiveMidpoint i) - X s| ≤ max B 0 := by
      simpa only [abs_sub_comm] using (hbound i s hs).trans hAi
    calc
      _ ≤ |X r - X (n04PositiveMidpoint i)| +
          |X (n04PositiveMidpoint i) - X s| := abs_sub_le _ _ _
      _ ≤ max B 0 + max B 0 := add_le_add hrb hsb
      _ = 2 * max B 0 := by ring
      _ ≤ max L (2 * max B 0) := le_max_right _ _
  · have hg : ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
        n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
        n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n := by
      simpa only [U, mem_setOf_eq, not_not] using hi
    obtain ⟨side, n, hn, hl, hu⟩ := hg
    have hR : 0 < P.sideRadius side := P.sideRadius_pos side
    have hscaled (x : ℝ) (hx : x ∈ Icc (n04PositiveLeft i) (n04PositiveRight i)) :
        x / P.sideRadius side ∈ Icc (n06MorsePositiveLeft S.chain side n)
          (n06MorsePositiveRight S.chain side n) := by
      rw [hl, hu] at hx
      exact ⟨(le_div_iff₀ hR).mpr (by simpa only [mul_comm] using hx.1),
        (div_le_iff₀ hR).mpr (by simpa only [mul_comm] using hx.2)⟩
    have hscale (x : ℝ) : P.sideRadius side * (x / P.sideRadius side) = x := by
      field_simp [hR.ne'] <;> ring
    have h := htail side n hn (r / P.sideRadius side) (s / P.sideRadius side)
      (hscaled r hr) (hscaled s hs)
    rw [hscale r, hscale s] at h
    exact h.trans (le_max_left _ _)

/-- The stored host need contain only the actual midpoint. Both the
point and sample remain the given ones, with one constant before all labels. -/
theorem retainedReference_positive_midpoint_sample_X_bound
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {E : PhysicalSpacesData} {C : NonlinearGeometryData E}
    (hC : controlGeometryConditions Γ.reference E C)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
        ∀ r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
          |endpointX 1 (Statements.endpointDistance Γ.reference r) -
            endpointX 1 (Statements.endpointDistance Γ.reference (T.sample j))| ≤ L := by
  obtain ⟨L, hL, hwhole⟩ := retainedReference_positive_closed_interval_X_oscillation
    P hS hband hq hΓ hw hcoordinates hC hT
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, hcompare⟩ := hdata
  obtain ⟨B, A, hB, _, hindex⟩ := hcompare
  have hf : Continuous (deriv Γ.reference.w) :=
    hΓ.2.1.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  refine ⟨L + 2 * B, by positivity, ?_⟩
  intro i j hhost r hr
  have hwidth := (n04PositiveComponent_bounds hf i).2.1
  have hmid : n04PositiveMidpoint i ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) := by
    change n04PositiveLeft i ≤ (n04PositiveLeft i + n04PositiveRight i) / 2 ∧
      (n04PositiveLeft i + n04PositiveRight i) / 2 ≤ n04PositiveRight i
    constructor <;> linarith only [hwidth]
  have hwhole' := abs_le.mp (hwhole i r (n04PositiveMidpoint i) hr hmid)
  have hm := abs_le.mp (hindex j (n04PositiveMidpoint i) hhost).1
  have hs := abs_le.mp (hindex j (T.sample j) (hsample j)).1
  exact abs_le.mpr ⟨by linarith only [hwhole'.1, hm.1, hs.2],
    by linarith only [hwhole'.2, hm.2, hs.1]⟩

end ContinuousFlexibility.Radial
