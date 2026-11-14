module

public import ContinuousFlexibility.Analysis.N04RealizationMaterialTransfer
public import ContinuousFlexibility.Analysis.MaterialSampleRadialPolynomial
public import ContinuousFlexibility.Analysis.ActualRadialCellComparison
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Exact physical height weights for the correction strips

The retained host cell contains each negative component. Its index is
uniformly close to the control label by N01. Consequently the original
circle sample height and any fixed containing-cell radial loss transfer
to the actual physical point with the same positive height exponent.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

/-- A material cell sample and every point of that cell have uniformly
close endpoint coordinates. Full positive height powers are preserved. -/
theorem n04PulledFields_cellSample_physicalCost
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    {γ R : ℝ} (hγ : 0 < γ) (hR : 0 ≤ R) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ j r, r ∈ D.cells j →
      T.H (T.sample j) ^ γ * T.E0 (T.sample j) ^ R ≤
        K * T.H r ^ γ * T.E0 r ^ A := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _, hcompare⟩ := hdata
  obtain ⟨C, P, hC, _, hindex⟩ := hcompare
  obtain ⟨K, A, hK, hA, hb⟩ := n04Realization_material_H_E0_rpow_oneSided
    hT hD hγ hR (show 0 ≤ 2 * C by positivity)
  refine ⟨K, A, hK, hA, fun j r hr => ?_⟩
  have hsample := (hindex j (T.sample j) (hsamp j)).1
  have hpoint := (hindex j r hr).1
  have hshift : endpointX 1 (endpointDistance D r) ≤
      endpointX 1 (endpointDistance D (T.sample j)) + 2 * C := by
    linarith only [(abs_le.mp hsample).1, (abs_le.mp hpoint).2]
  exact hb (T.sample j) r (materialSample_mem_interval hD hT j)
    (hD.choose_spec.2.1.2.2.2.1 j hr) hshift

local instance n04PulledFieldsStripPhysicalCostStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- The optical control sample is converted to the physical point using
the original host-cell fact. The containing cell used by the cutoff may
be any cell containing that point. -/
theorem N01Properties.n04PulledFields_controlSample_physicalCost
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ m j r,
      r ∈ Ioo (C.left m) (C.right m) → r ∈ D.cells j →
      T.H (T.sample m) ^ γ * radialE (D.cellIndex j) ^ Q ≤
        K * T.H r ^ γ * T.E0 r ^ A := by
  obtain ⟨B, hB, hlabel⟩ := hN.2.2.2.2.1
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _, hcompare⟩ := hdata
  obtain ⟨C₀, P₀, hC₀, _, hindex⟩ := hcompare
  let L : ℝ := 2 * C₀ + B
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  obtain ⟨Kr, Ar, hKr, hAr, hradial⟩ := radialE_rpow_of_nat_sub_bound hQ hL
  obtain ⟨Ks, As, hKs, hAs, hsample⟩ := materialSample_radialE_power_bound hT hN.1.1 hAr
  obtain ⟨Kt, At, hKt, hAt, htransfer⟩ :=
    n04Realization_material_H_E0_rpow_oneSided hT hN.1.1 hγ hAs hL
  refine ⟨Kr * Ks * Kt, At, mul_pos (mul_pos hKr hKs) hKt, hAt,
    fun m j r hr hj => ?_⟩
  have hcontrol := hlabel m
  have hhostIndex := (hindex (C.cell m) r (hhost m hr)).1
  have hjIndex := (hindex j r hj).1
  have hsIndex := (hindex m (T.sample m) (hsamp m)).1
  have hindexShift : |(D.cellIndex j : ℝ) - D.cellIndex m| ≤ L := by
    apply abs_le.mpr
    dsimp only [L]
    constructor <;> linarith only [(abs_le.mp hhostIndex).1,
      (abs_le.mp hhostIndex).2, (abs_le.mp hjIndex).1,
      (abs_le.mp hjIndex).2, (abs_le.mp hcontrol).1, (abs_le.mp hcontrol).2]
  have hpointShift : endpointX 1 (endpointDistance D r) ≤
      endpointX 1 (endpointDistance D (T.sample m)) + L := by
    dsimp only [L]
    linarith only [(abs_le.mp hhostIndex).2, (abs_le.mp hsIndex).1,
      (abs_le.mp hcontrol).2]
  have hcore : r ∈ Ioo D.a D.b :=
    hN.1.1.choose_spec.2.1.2.2.2.1 (C.cell m) (hhost m hr)
  have hsampleCore := materialSample_mem_interval hN.1.1 hT m
  have hheight : 0 ≤ T.H (T.sample m) ^ γ :=
    Real.rpow_nonneg (hT.2.1 _ hsampleCore).2.1.le _
  have hcost : radialE (D.cellIndex j) ^ Q ≤
      (Kr * Ks) * T.E0 (T.sample m) ^ As :=
    (hradial _ _ hindexShift).trans
      ((mul_le_mul_of_nonneg_left (hsample m) hKr.le).trans_eq (by ring))
  have hfull := htransfer (T.sample m) r hsampleCore hcore hpointShift
  calc
    _ ≤ T.H (T.sample m) ^ γ * ((Kr * Ks) * T.E0 (T.sample m) ^ As) :=
      mul_le_mul_of_nonneg_left hcost hheight
    _ = (Kr * Ks) * (T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ As) := by ring
    _ ≤ (Kr * Ks) * (Kt * T.H r ^ γ * T.E0 r ^ At) :=
      mul_le_mul_of_nonneg_left hfull (mul_nonneg hKr.le hKs.le)
    _ = _ := by ring

end ContinuousFlexibility.Statements
