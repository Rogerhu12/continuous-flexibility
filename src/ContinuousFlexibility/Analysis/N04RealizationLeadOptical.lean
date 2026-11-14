import ContinuousFlexibility.Analysis.N04RealizationLeadAssembly
import ContinuousFlexibility.Analysis.N05RetainedOpticalLowerAdapter
import ContinuousFlexibility.Analysis.MaterialSampleRadialPolynomial

/-!
# The optical obligation

The retained reference has the optical lower bound on every actual carrier,
with a power of the radial scale of the host cell. The material sample weight
dominates a fixed power of that scale, so one constant `κ` gives the lower
bound with a material cost.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem n04Realization_opticalObligation : N04RealizationOpticalObligation := by
  intro W
  have hlow : N05ActualCarrierOpticalLower W.D W.C :=
    n05_actualCarrierOpticalLower_of_retained_coordinates W.P W.metadata.selected
      W.metadata.first_two one_pos W.hw W.hphi W.radial W.construction W.coordinates
      W.through03.1.1.2.2.2.1
  obtain ⟨B, A, hB, hA, hl⟩ := hlow
  obtain ⟨K, P, hK, hP, hE⟩ := materialSample_radialE_power_bound W.hT W.radial.1 hA
  let κ : ℝ := max (B * K) (max P 1)
  have hκ1 : 1 ≤ κ := (le_max_right P 1).trans (le_max_right _ _)
  have hκ : 0 < κ := zero_lt_one.trans_le hκ1
  refine ⟨κ, hκ, fun m x hx => ?_⟩
  have hloc := hl m (W.C.cell m) (W.host m) x (Ioo_subset_Icc_self hx)
  have hfloor : 1 ≤ W.T.E0 (W.T.sample (W.C.cell m)) := W.floor _
  have hE0 : 0 < W.T.E0 (W.T.sample (W.C.cell m)) := zero_lt_one.trans_le hfloor
  have hrad : 0 < radialE (W.D.cellIndex (W.C.cell m)) ^ A :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hcost : B * radialE (W.D.cellIndex (W.C.cell m)) ^ A ≤
      κ * W.T.E0 (W.T.sample (W.C.cell m)) ^ κ := by
    calc B * radialE (W.D.cellIndex (W.C.cell m)) ^ A
        ≤ B * (K * W.T.E0 (W.T.sample (W.C.cell m)) ^ P) :=
          mul_le_mul_of_nonneg_left (hE (W.C.cell m)) hB.le
      _ = (B * K) * W.T.E0 (W.T.sample (W.C.cell m)) ^ P := by ring
      _ ≤ κ * W.T.E0 (W.T.sample (W.C.cell m)) ^ κ :=
          mul_le_mul (le_max_left _ _)
            (Real.rpow_le_rpow_of_exponent_le hfloor
              ((le_max_left P 1).trans (le_max_right _ _)))
            (Real.rpow_nonneg hE0.le _) hκ.le
  have hinv : κ⁻¹ * W.T.E0 (W.T.sample (W.C.cell m)) ^ (-κ) ≤
      (B * radialE (W.D.cellIndex (W.C.cell m)) ^ A)⁻¹ := by
    rw [Real.rpow_neg hE0.le, ← mul_inv]
    exact inv_anti₀ (mul_pos hB hrad) hcost
  have hmin : 0 ≤ min (x - W.C.left m) (W.C.right m - x) :=
    le_min (sub_nonneg.mpr hx.1.le) (sub_nonneg.mpr hx.2.le)
  exact (mul_le_mul_of_nonneg_right hinv hmin).trans hloc

end ContinuousFlexibility.Analysis
