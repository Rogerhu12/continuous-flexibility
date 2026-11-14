module

public import ContinuousFlexibility.Analysis.MaterialEndpointWeightTransport

/-!
# Common actual height and material ratios from endpoint displacement

The two ratio estimates use the same actual material data and one common
constant and exponent. Only a fixed scaling of `E0` is at least one; the
unscaled coefficient weight is merely positive.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem material_H_M_ratios_of_bounded_endpointX_shift
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      |endpointX 1 (endpointDistance D r) - endpointX 1 (endpointDistance D s)| ≤ L →
      T.H r / T.H s ≤ K * T.E0 s ^ A ∧
        T.M r / T.M s ≤ K * T.E0 s ^ A := by
  obtain ⟨KH, AH, hKH, hAH, hH⟩ :=
    material_global_H_M_E0_rpow_bounded_X_shift hT hRef (1 : ℝ) (0 : ℝ)
      (R := 0) (by norm_num) hL
  obtain ⟨KM, AM, hKM, hAM, hM⟩ :=
    material_global_H_M_E0_rpow_bounded_X_shift hT hRef (0 : ℝ) (1 : ℝ)
      (R := 0) (by norm_num) hL
  obtain ⟨E, hE, hscale⟩ := material_E0_uniform_scaled_lower hT hRef
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  let K := KH * E ^ AM + KM * E ^ AH
  have hK : 0 < K := add_pos
    (mul_pos hKH (Real.rpow_pos_of_pos hEpos _))
    (mul_pos hKM (Real.rpow_pos_of_pos hEpos _))
  refine ⟨K, AH + AM, hK, add_nonneg hAH hAM, ?_⟩
  intro r s hr hs hdist
  have hpos := hT.2.1 s hs
  have hHs : 0 < T.H s := hpos.2.1
  have hMs : 0 < T.M s := zero_lt_one.trans_le hpos.2.2.2
  have hEs : 0 < T.E0 s := hpos.2.2.1
  have hHr : T.H r ≤ KH * (T.H s * T.E0 s ^ AH) := by
    simpa only [Real.rpow_one, Real.rpow_zero, one_mul, mul_one] using
      hH r s hr hs hdist
  have hMr : T.M r ≤ KM * (T.M s * T.E0 s ^ AM) := by
    simpa only [Real.rpow_one, Real.rpow_zero, one_mul, mul_one] using
      hM r s hr hs hdist
  have hHratio : T.H r / T.H s ≤ KH * T.E0 s ^ AH :=
    (div_le_iff₀ hHs).mpr (hHr.trans_eq (by ring))
  have hMratio : T.M r / T.M s ≤ KM * T.E0 s ^ AM :=
    (div_le_iff₀ hMs).mpr (hMr.trans_eq (by ring))
  have hpowH : 1 ≤ E ^ AH * T.E0 s ^ AH := by
    simpa only [Real.mul_rpow hEpos.le hEs.le] using
      Real.one_le_rpow (hscale s hs) hAH
  have hpowM : 1 ≤ E ^ AM * T.E0 s ^ AM := by
    simpa only [Real.mul_rpow hEpos.le hEs.le] using
      Real.one_le_rpow (hscale s hs) hAM
  constructor
  · calc
      _ ≤ KH * T.E0 s ^ AH := hHratio
      _ ≤ (KH * T.E0 s ^ AH) * (E ^ AM * T.E0 s ^ AM) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowM
          (mul_nonneg hKH.le (Real.rpow_nonneg hEs.le _))
      _ = (KH * E ^ AM) * T.E0 s ^ (AH + AM) := by
        rw [Real.rpow_add hEs]
        ring
      _ ≤ K * T.E0 s ^ (AH + AM) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (mul_nonneg hKM.le
            (Real.rpow_nonneg hEpos.le _))) (Real.rpow_nonneg hEs.le _)
  · calc
      _ ≤ KM * T.E0 s ^ AM := hMratio
      _ ≤ (KM * T.E0 s ^ AM) * (E ^ AH * T.E0 s ^ AH) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowH
          (mul_nonneg hKM.le (Real.rpow_nonneg hEs.le _))
      _ = (KM * E ^ AH) * T.E0 s ^ (AH + AM) := by
        rw [Real.rpow_add hEs]
        ring
      _ ≤ K * T.E0 s ^ (AH + AM) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (mul_nonneg hKH.le
            (Real.rpow_nonneg hEpos.le _))) (Real.rpow_nonneg hEs.le _)

end ContinuousFlexibility.Statements
