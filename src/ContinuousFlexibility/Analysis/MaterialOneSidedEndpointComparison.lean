import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels

/-!
# Actual sample costs in one endpoint-coordinate direction

The second point may be farther from the ambient boundary than the first.
A one-sided coordinate bound controls the height ratio in the useful
direction and every fixed coefficient power at the second point. The
same actual material data are retained; no common cell is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem material_oneSided_endpoint_comparison
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) :
    ∃ KH AH KE AE : ℝ, 0 < KH ∧ 0 ≤ AH ∧ 0 < KE ∧ 0 ≤ AE ∧
      ∀ r s : ℝ, r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
        endpointX 1 (endpointDistance D s) ≤
          endpointX 1 (endpointDistance D r) + L →
        T.H r / T.H s ≤ KH * T.E0 r ^ AH ∧
          T.E0 s ^ R ≤ KE * T.E0 r ^ AE := by
  obtain ⟨d0, L0, CH, CE, CM, _, hL0, hCH, hCE, _, hmodels⟩ :=
    material_global_endpoint_models hT hRef
  let X : ℝ → ℝ := fun r => endpointX d0 (endpointDistance D r)
  have hCHpos : 0 < CH := zero_lt_one.trans_le hCH
  have hCEpos : 0 < CE := zero_lt_one.trans_le hCE
  have hshift : 0 ≤ 2 * L0 + L := by positivity
  obtain ⟨AH, hAH, hheight⟩ := materialH_neg_rpow_oneSided_shift
    (β := 1) (by norm_num) hshift
  obtain ⟨C, AE, hC, hAE, hcoefficient⟩ :=
    materialE0_rpow_oneSided_shift hR hshift
  refine ⟨CH * CH * CE ^ AH, AH, CE ^ R * C * CE ^ AE, AE,
    mul_pos (mul_pos hCHpos hCHpos) (Real.rpow_pos_of_pos hCEpos _), hAH,
    mul_pos (mul_pos (Real.rpow_pos_of_pos hCEpos _) hC)
      (Real.rpow_pos_of_pos hCEpos _), hAE, ?_⟩
  intro r s hr hs hrs
  obtain ⟨hxr, hdr, hHr, hHr', hEr, hEr', hMr, hMr'⟩ := hmodels r hr
  obtain ⟨hxs, hds, hHs, hHs', hEs, hEs', hMs, hMs'⟩ := hmodels s hs
  have hdist : X s ≤ X r + (2 * L0 + L) := by
    have hu := (abs_le.mp hds).2
    have hl := (abs_le.mp hdr).1
    change X s - endpointX 1 (endpointDistance D s) ≤ L0 at hu
    change -L0 ≤ X r - endpointX 1 (endpointDistance D r) at hl
    linarith only [hu, hl, hrs]
  have hErpos : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
  have hEspos : 0 < T.E0 s := (hT.2.1 s hs).2.2.1
  have hHspos : 0 < T.H s := (hT.2.1 s hs).2.1
  have hpower (P : ℝ) (hP : 0 ≤ P) :
      materialE0 (X r) ^ P ≤ CE ^ P * T.E0 r ^ P := by
    have hp := Real.rpow_le_rpow (materialE0_pos (X r)).le hEr' hP
    simpa only [Real.mul_rpow hCEpos.le hErpos.le] using hp
  constructor
  · have hi : (materialH (X s))⁻¹ ≤
        (materialH (X r))⁻¹ * materialE0 (X r) ^ AH := by
      simpa only [Real.rpow_neg_one] using hheight (X s) (X r) hxs hxr hdist
    have hratio : materialH (X r) / materialH (X s) ≤ materialE0 (X r) ^ AH := by
      calc
        _ = materialH (X r) * (materialH (X s))⁻¹ := div_eq_mul_inv _ _
        _ ≤ materialH (X r) *
            ((materialH (X r))⁻¹ * materialE0 (X r) ^ AH) :=
          mul_le_mul_of_nonneg_left hi (materialH_pos (X r)).le
        _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ (materialH_pos (X r)).ne', one_mul]
    have hmodel : materialH (X r) ≤ materialH (X s) * materialE0 (X r) ^ AH :=
      ((div_le_iff₀ (materialH_pos (X s))).mp hratio).trans_eq (mul_comm _ _)
    have hpoint : T.H r ≤ (CH * CH * CE ^ AH) * T.H s * T.E0 r ^ AH := by
      calc
        _ ≤ CH * materialH (X r) := hHr
        _ ≤ CH * (materialH (X s) * materialE0 (X r) ^ AH) :=
          mul_le_mul_of_nonneg_left hmodel hCHpos.le
        _ ≤ CH * ((CH * T.H s) * materialE0 (X r) ^ AH) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hHs' (Real.rpow_nonneg (materialE0_pos (X r)).le _))
            hCHpos.le
        _ ≤ CH * ((CH * T.H s) * (CE ^ AH * T.E0 r ^ AH)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hpower AH hAH) (mul_nonneg hCHpos.le hHspos.le))
            hCHpos.le
        _ = _ := by ring
    exact (div_le_iff₀ hHspos).mpr (hpoint.trans_eq (by ring))
  · have hfirst : T.E0 s ^ R ≤ CE ^ R * materialE0 (X s) ^ R := by
      have hEs' : T.E0 s ≤ CE * materialE0 (X s) := hEs
      have hp := Real.rpow_le_rpow hEspos.le hEs' hR
      simpa only [Real.mul_rpow hCEpos.le (materialE0_pos (X s)).le] using hp
    calc
      _ ≤ CE ^ R * materialE0 (X s) ^ R := hfirst
      _ ≤ CE ^ R * (C * materialE0 (X r) ^ AE) :=
        mul_le_mul_of_nonneg_left (hcoefficient (X s) (X r) hxs hxr hdist)
          (Real.rpow_nonneg hCEpos.le _)
      _ ≤ CE ^ R * (C * (CE ^ AE * T.E0 r ^ AE)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpower AE hAE) hC.le)
          (Real.rpow_nonneg hCEpos.le _)
      _ = _ := by ring

end ContinuousFlexibility.Statements
