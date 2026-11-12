import ContinuousFlexibility.Analysis.PositiveComponentSimpleProfileLower
import ContinuousFlexibility.Analysis.RetainedPositiveGapProfileLower
import ContinuousFlexibility.Analysis.RetainedPositiveComponentClassification
import ContinuousFlexibility.Analysis.RetainedPositiveComponentInteriorEndpoints
import ContinuousFlexibility.Analysis.PositiveComponentMaterialCell
import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels

/-!
# One sampled physical lower bound for every retained positive component

The actual tail components use the quantitative Morse gap estimate.
Only the proved finite central exception set uses the qualitative
simple-root coefficient. A fixed scaled E0 floor absorbs that finite
constant. The original reference, component, midpoint cell and sample
are retained throughout, without requiring one cell for the whole gap.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem retainedReference_positive_component_profile_material_lower
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {E : PhysicalSpacesData} {C : NonlinearGeometryData E}
    (hC : controlGeometryConditions Γ.reference E C)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
        ∀ r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
          (B * T.E0 (T.sample j) ^ A)⁻¹ *
              min (r - n04PositiveLeft i) (n04PositiveRight i - r) ≤
            deriv Γ.reference.w r / r := by
  classical
  let I := N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w)
  let U : Set I := {i | ¬ ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
    n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
    n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n}
  have hD : RadialProfileGeometry Γ.reference := hΓ.2.1.choose_spec.1
  have hsingle (i : I) : ∃ k : ℝ, 0 < k ∧
      ∀ r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
        k * min (r - n04PositiveLeft i) (n04PositiveRight i - r) ≤
          deriv Γ.reference.w r / r :=
    n04PositiveComponent_simple_profile_min_lower hD i
      (retainedReference_positive_endpoints_interior P hS hband hq hΓ hw hcoordinates i)
  choose k hk hlower using hsingle
  have hU : U.Finite :=
    (retainedReference_positive_gap_exceptions_finite
      P hS hband hq hΓ hw hcoordinates hC).1
  obtain ⟨F, hF⟩ := (hU.image (fun i => (k i)⁻¹)).bddAbove
  let F0 : ℝ := max 1 F
  have hF0 : 0 < F0 := zero_lt_one.trans_le (le_max_left _ _)
  have hfinite (i : I) (hi : i ∈ U) : (k i)⁻¹ ≤ F0 :=
    (hF ⟨i, hi, rfl⟩).trans (le_max_right _ _)
  obtain ⟨Bt, A, hBt, hA, htail⟩ :=
    retainedReference_positive_gap_profile_material_lower P hS hband hΓ hw hcoordinates hT
  obtain ⟨K0, hK0, hfloor⟩ := material_E0_uniform_scaled_lower hT hΓ.2.1
  have hK0pos : 0 < K0 := zero_lt_one.trans_le hK0
  have hfiniteCost : 0 ≤ F0 * K0 ^ A :=
    mul_nonneg hF0.le (Real.rpow_nonneg hK0pos.le _)
  let B : ℝ := Bt + F0 * K0 ^ A
  have hB : 0 < B := add_pos_of_pos_of_nonneg hBt hfiniteCost
  have hBtB : Bt ≤ B := le_add_of_nonneg_right hfiniteCost
  refine ⟨B, A, hB, hA, ?_⟩
  intro i j hmid r hr
  have hjcore := materialSample_mem_interval hΓ.2.1 hT j
  have hEj : 0 < T.E0 (T.sample j) := (hT.2.1 _ hjcore).2.2.1
  have hpower : 1 ≤ K0 ^ A * T.E0 (T.sample j) ^ A := by
    rw [← Real.mul_rpow hK0pos.le hEj.le]
    exact Real.one_le_rpow (hfloor _ hjcore) hA
  have hF0bound : F0 ≤ B * T.E0 (T.sample j) ^ A := by
    calc
      F0 ≤ F0 * (K0 ^ A * T.E0 (T.sample j) ^ A) :=
        (mul_one _).symm.trans_le (mul_le_mul_of_nonneg_left hpower hF0.le)
      _ = (F0 * K0 ^ A) * T.E0 (T.sample j) ^ A := by ring
      _ ≤ B * T.E0 (T.sample j) ^ A :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hBt.le)
          (Real.rpow_nonneg hEj.le _)
  have hmin : 0 ≤ min (r - n04PositiveLeft i) (n04PositiveRight i - r) :=
    le_min (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  by_cases hi : i ∈ U
  · have hcost : (k i)⁻¹ ≤ B * T.E0 (T.sample j) ^ A :=
      (hfinite i hi).trans hF0bound
    have hcoefficient : (B * T.E0 (T.sample j) ^ A)⁻¹ ≤ k i := by
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (hk i)) hcost
    exact (mul_le_mul_of_nonneg_right hcoefficient hmin).trans (hlower i r hr)
  · have hg : ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
        n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
        n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n := by
      simpa only [U, mem_setOf_eq, not_not] using hi
    obtain ⟨side, n, hn, hl, hu⟩ := hg
    have hm : n04PositiveMidpoint i = P.sideRadius side *
        ((n06MorsePositiveLeft S.chain side n + n06MorsePositiveRight S.chain side n) / 2) := by
      change (n04PositiveLeft i + n04PositiveRight i) / 2 = _
      rw [hl, hu]
      ring
    have hmid' : P.sideRadius side *
        ((n06MorsePositiveLeft S.chain side n + n06MorsePositiveRight S.chain side n) / 2)
          ∈ Γ.reference.cells j := by rw [← hm]; exact hmid
    have hr' : r ∈ Icc (P.sideRadius side * n06MorsePositiveLeft S.chain side n)
        (P.sideRadius side * n06MorsePositiveRight S.chain side n) := by
      simpa only [← hl, ← hu] using hr
    have hbound : (Bt * T.E0 (T.sample j) ^ A)⁻¹ *
        min (r - n04PositiveLeft i) (n04PositiveRight i - r) ≤
          deriv Γ.reference.w r / r := by
      simpa only [← hl, ← hu] using htail side n hn j hmid' r hr'
    have hcost : Bt * T.E0 (T.sample j) ^ A ≤ B * T.E0 (T.sample j) ^ A :=
      mul_le_mul_of_nonneg_right hBtB (Real.rpow_nonneg hEj.le _)
    have hcoefficient : (B * T.E0 (T.sample j) ^ A)⁻¹ ≤
        (Bt * T.E0 (T.sample j) ^ A)⁻¹ :=
      inv_anti₀ (mul_pos hBt (Real.rpow_pos_of_pos hEj _)) hcost
    exact (mul_le_mul_of_nonneg_right hcoefficient hmin).trans hbound

end ContinuousFlexibility.Radial
