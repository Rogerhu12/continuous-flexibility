module

public import ContinuousFlexibility.Analysis.RetainedPositiveComponentClassification
public import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapMaterialWidth
public import ContinuousFlexibility.Analysis.PositiveComponentMaterialCell
public import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels

/-!
# Width costs of every actual retained positive component

The true tail gap estimate is evaluated at the physical midpoint cell.
The finitely many central components have a uniform reciprocal-width
constant. The actual scaled E0 floor absorbs that constant and the fixed
annulus span without assuming that the original E0 is at least one.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem retainedReference_positive_component_material_width
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
        (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ B * T.E0 (T.sample j) ^ A ∧
          n04PositiveRight i - n04PositiveLeft i ≤ B * T.E0 (T.sample j) ^ A := by
  classical
  let I := N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w)
  let U : Set I := {i | ¬ ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
    n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
    n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n}
  obtain ⟨_, F, hF, hfinite⟩ := retainedReference_positive_gap_exceptions_finite
    P hS hband hq hΓ hw hcoordinates hC
  obtain ⟨B, A, hB, hA, hwidth⟩ := retainedReference_positive_gap_inverse_width_bound
    P hS hband hΓ hcoordinates hT
  obtain ⟨K0, hK0, hfloor⟩ := material_E0_uniform_scaled_lower hT hΓ.2.1
  let V := max (Γ.reference.b - Γ.reference.a) 0
  have hV : 0 ≤ V := le_max_right _ _
  have hFV : 0 ≤ F + V := add_nonneg hF.le hV
  have hK0pos : 0 < K0 := zero_lt_one.trans_le hK0
  have hcost : 0 ≤ (F + V) * K0 ^ A :=
    mul_nonneg hFV (Real.rpow_nonneg hK0pos.le _)
  let M := B + (F + V) * K0 ^ A
  have hM : 0 < M := add_pos_of_pos_of_nonneg hB hcost
  have hBM : B ≤ M := le_add_of_nonneg_right hcost
  refine ⟨M, A, hM, hA, ?_⟩
  intro i j hmid
  have hjcore := materialSample_mem_interval hΓ.2.1 hT j
  have hEj : 0 < T.E0 (T.sample j) := (hT.2.1 _ hjcore).2.2.1
  have hpower : 1 ≤ K0 ^ A * T.E0 (T.sample j) ^ A := by
    rw [← Real.mul_rpow hK0pos.le hEj.le]
    exact Real.one_le_rpow (hfloor _ hjcore) hA
  have hconst {x : ℝ} (hx : x ≤ F + V) : x ≤ M * T.E0 (T.sample j) ^ A := by
    calc
      x ≤ F + V := hx
      _ ≤ (F + V) * (K0 ^ A * T.E0 (T.sample j) ^ A) :=
        (mul_one _).symm.trans_le (mul_le_mul_of_nonneg_left hpower hFV)
      _ = ((F + V) * K0 ^ A) * T.E0 (T.sample j) ^ A := by ring
      _ ≤ M * T.E0 (T.sample j) ^ A :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB.le)
          (Real.rpow_nonneg hEj.le _)
  have hf : Continuous (deriv Γ.reference.w) :=
    hΓ.2.1.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  have hib := n04PositiveComponent_bounds hf i
  have hspan0 : n04PositiveRight i - n04PositiveLeft i ≤
      Γ.reference.b - Γ.reference.a := by linarith only [hib.1, hib.2.2]
  have hspan : n04PositiveRight i - n04PositiveLeft i ≤ V :=
    hspan0.trans (le_max_left _ _)
  refine ⟨?_, hconst (hspan.trans (le_add_of_nonneg_left hF.le))⟩
  by_cases hi : i ∈ U
  · exact hconst ((hfinite i hi).trans (le_add_of_nonneg_right hV))
  · have hg : ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
        n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
        n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n := by
      by_contra hne
      exact hi hne
    obtain ⟨side, n, hn, hl, hr⟩ := hg
    have hm : n04PositiveMidpoint i = P.sideRadius side *
        ((n06MorsePositiveLeft S.chain side n + n06MorsePositiveRight S.chain side n) / 2) := by
      change (n04PositiveLeft i + n04PositiveRight i) / 2 = _
      rw [hl, hr]
      ring
    have hmid' : P.sideRadius side *
        ((n06MorsePositiveLeft S.chain side n + n06MorsePositiveRight S.chain side n) / 2)
          ∈ Γ.reference.cells j := by rw [← hm]; exact hmid
    have h := hwidth side n hn j hmid'
    rw [← hl, ← hr] at h
    exact h.trans (mul_le_mul_of_nonneg_right hBM (Real.rpow_nonneg hEj.le _))

end ContinuousFlexibility.Radial
