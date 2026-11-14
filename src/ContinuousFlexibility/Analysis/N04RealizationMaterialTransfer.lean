module

public import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels
public import ContinuousFlexibility.Analysis.N04RealizationMaterialOneSided

/-!
# Exact height decay for actual material weights

The global endpoint models compare the actual weights at both physical
points with one common model coordinate. A one-sided comparison of the
fixed endpoint coordinates then retains the same positive height exponent.
The points need not belong to the same material cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- A one-sided endpoint-coordinate comparison transfers the full actual
height exponent. The constants precede both evaluation points. -/
theorem n04Realization_material_H_E0_rpow_oneSided
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {γ R L : ℝ} (hγ : 0 < γ) (hR : 0 ≤ R) (hL : 0 ≤ L) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      endpointX 1 (endpointDistance D s) ≤ endpointX 1 (endpointDistance D r) + L →
      T.H r ^ γ * T.E0 r ^ R ≤ B * T.H s ^ γ * T.E0 s ^ A := by
  obtain ⟨d0, L₀, KH, KE, KM, _, hL₀, hKH, hKE, _, hmodel⟩ :=
    material_global_endpoint_models hT hRef
  let X : ℝ → ℝ := fun r => endpointX d0 (endpointDistance D r)
  have hKH0 : 0 < KH := zero_lt_one.trans_le hKH
  have hKE0 : 0 < KE := zero_lt_one.trans_le hKE
  obtain ⟨K, A, hK, hA, hshift⟩ := n04Realization_materialH_E0_rpow_oneSided hγ hR
    (show 0 ≤ 2 * L₀ + L by positivity)
  let KF : ℝ := KH ^ γ * KE ^ R
  let KG : ℝ := KH ^ γ * KE ^ A
  have hKF : 0 < KF :=
    mul_pos (Real.rpow_pos_of_pos hKH0 _) (Real.rpow_pos_of_pos hKE0 _)
  have hKG : 0 < KG :=
    mul_pos (Real.rpow_pos_of_pos hKH0 _) (Real.rpow_pos_of_pos hKE0 _)
  refine ⟨KF * K * KG, A, mul_pos (mul_pos hKF hK) hKG, hA, ?_⟩
  intro r s hr hs hrs
  obtain ⟨hxr, hdr, hHr, hHr', hEr, hEr', _⟩ := hmodel r hr
  obtain ⟨hxs, hds, hHs, hHs', hEs, hEs', _⟩ := hmodel s hs
  have hHrpos : 0 < T.H r := (hT.2.1 r hr).2.1
  have hHspos : 0 < T.H s := (hT.2.1 s hs).2.1
  have hErpos : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
  have hEspos : 0 < T.E0 s := (hT.2.1 s hs).2.2.1
  have hdist : X s ≤ X r + (2 * L₀ + L) := by
    change |X r - endpointX 1 (endpointDistance D r)| ≤ L₀ at hdr
    change |X s - endpointX 1 (endpointDistance D s)| ≤ L₀ at hds
    linarith only [(abs_le.mp hdr).1, (abs_le.mp hds).2, hrs]
  have hHrγ := Real.rpow_le_rpow hHrpos.le hHr hγ.le
  rw [Real.mul_rpow hKH0.le (materialH_pos (X r)).le] at hHrγ
  have hErR := Real.rpow_le_rpow hErpos.le hEr hR
  rw [Real.mul_rpow hKE0.le (materialE0_pos (X r)).le] at hErR
  have hHsγ := Real.rpow_le_rpow (materialH_pos (X s)).le hHs' hγ.le
  rw [Real.mul_rpow hKH0.le hHspos.le] at hHsγ
  have hEsA := Real.rpow_le_rpow (materialE0_pos (X s)).le hEs' hA
  rw [Real.mul_rpow hKE0.le hEspos.le] at hEsA
  have hfirst : T.H r ^ γ * T.E0 r ^ R ≤
      KF * (materialH (X r) ^ γ * materialE0 (X r) ^ R) := by
    have h := mul_le_mul hHrγ hErR (Real.rpow_nonneg hErpos.le R)
      (mul_nonneg (Real.rpow_nonneg hKH0.le γ)
        (Real.rpow_nonneg (materialH_pos (X r)).le γ))
    exact h.trans_eq (by dsimp only [KF]; ring)
  have hlast : materialH (X s) ^ γ * materialE0 (X s) ^ A ≤
      KG * (T.H s ^ γ * T.E0 s ^ A) := by
    have h := mul_le_mul hHsγ hEsA (Real.rpow_nonneg (materialE0_pos (X s)).le A)
      (mul_nonneg (Real.rpow_nonneg hKH0.le γ) (Real.rpow_nonneg hHspos.le γ))
    exact h.trans_eq (by dsimp only [KG]; ring)
  calc
    _ ≤ KF * (materialH (X r) ^ γ * materialE0 (X r) ^ R) := hfirst
    _ ≤ KF * (K * (materialH (X s) ^ γ * materialE0 (X s) ^ A)) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [mul_assoc] using hshift (X r) (X s) hxr hxs hdist) hKF.le
    _ ≤ KF * (K * (KG * (T.H s ^ γ * T.E0 s ^ A))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hK.le) hKF.le
    _ = _ := by ring

end ContinuousFlexibility.Statements
