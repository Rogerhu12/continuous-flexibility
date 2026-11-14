module

public import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels
public import ContinuousFlexibility.Analysis.MaterialMEndpointShift

/-!
# Actual material weights between nearby endpoint coordinates

The actual global endpoint models retain the same material data. A
bounded displacement in `endpointX 1` preserves both prescribed real
height and material powers, with all loss in an `E0` power. The two
physical points may belong to different cells.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- The height and material exponents remain exactly `γ` and `η`. The
constants are chosen before both physical points and require no cell
reassignment or positive-component host assumption. -/
theorem material_global_H_M_E0_rpow_bounded_X_shift
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (γ η : ℝ) {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      |endpointX 1 (endpointDistance D r) - endpointX 1 (endpointDistance D s)| ≤ L →
      T.H r ^ γ * T.M r ^ η * T.E0 r ^ R ≤
        K * (T.H s ^ γ * T.M s ^ η * T.E0 s ^ A) := by
  obtain ⟨d0, L0, KH, KE, KM, _, hL0, hKH, hKE, hKM, hmodels⟩ :=
    material_global_endpoint_models hT hRef
  let X : ℝ → ℝ := fun r => endpointX d0 (endpointDistance D r)
  have hKH0 : 0 < KH := zero_lt_one.trans_le hKH
  have hKE0 : 0 < KE := zero_lt_one.trans_le hKE
  have hKM0 : 0 < KM := zero_lt_one.trans_le hKM
  have hshiftL : 0 ≤ 2 * L0 + L := by positivity
  obtain ⟨AH, hAH, hHshift⟩ := materialH_rpow_bounded_shift γ hshiftL
  obtain ⟨AM, hAM, hMshift⟩ := materialM_rpow_bounded_shift_E0 η hshiftL
  obtain ⟨K, P, hK, hP, hEshift⟩ := materialE0_rpow_oneSided_shift hR hshiftL
  let A := AH + AM + P
  have hA : 0 ≤ A := add_nonneg (add_nonneg hAH hAM) hP
  have hshift (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
      (hxy : |x - y| ≤ 2 * L0 + L) :
      materialH x ^ γ * materialM x ^ η * materialE0 x ^ R ≤
        K * (materialH y ^ γ * materialM y ^ η * materialE0 y ^ A) := by
    have hxy' : x ≤ y + (2 * L0 + L) := by linarith only [(abs_le.mp hxy).2]
    have hh := hHshift x y hx hy hxy
    have hm := hMshift x y hx hy hxy
    have he := hEshift x y hx hy hxy'
    have hpair := mul_le_mul hh hm
      (Real.rpow_nonneg (materialM_pos x).le η)
      (mul_nonneg (Real.rpow_nonneg (materialH_pos y).le γ)
        (Real.rpow_nonneg (materialE0_pos y).le AH))
    have hb := mul_le_mul hpair he (Real.rpow_nonneg (materialE0_pos x).le R)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (materialH_pos y).le γ)
          (Real.rpow_nonneg (materialE0_pos y).le AH))
        (mul_nonneg (Real.rpow_nonneg (materialM_pos y).le η)
          (Real.rpow_nonneg (materialE0_pos y).le AM)))
    exact hb.trans_eq (by
      dsimp only [A]
      rw [Real.rpow_add (materialE0_pos y), Real.rpow_add (materialE0_pos y)]
      ring)
  let KF := KH ^ |γ| * KM ^ |η| * KE ^ R
  let KG := KH ^ |γ| * KM ^ |η| * KE ^ A
  have hKF : 0 < KF := by dsimp only [KF]; positivity
  have hKG : 0 < KG := by dsimp only [KG]; positivity
  refine ⟨KF * K * KG, A, mul_pos (mul_pos hKF hK) hKG, hA, ?_⟩
  intro r s hr hs hrs
  obtain ⟨hxr, hdr, hHr, hHr', hEr, hEr', hMr, hMr'⟩ := hmodels r hr
  obtain ⟨hxs, hds, hHs, hHs', hEs, hEs', hMs, hMs'⟩ := hmodels s hs
  have hdist : |X r - X s| ≤ 2 * L0 + L := by
    have hrev : |endpointX 1 (endpointDistance D s) - X s| ≤ L0 := by
      rw [abs_sub_comm]
      exact hds
    calc
      _ ≤ |X r - endpointX 1 (endpointDistance D r)| +
          |endpointX 1 (endpointDistance D r) - X s| := abs_sub_le _ _ _
      _ ≤ L0 + (|endpointX 1 (endpointDistance D r) -
          endpointX 1 (endpointDistance D s)| +
          |endpointX 1 (endpointDistance D s) - X s|) :=
        add_le_add hdr (abs_sub_le _ _ _)
      _ ≤ L0 + (L + L0) := add_le_add le_rfl (add_le_add hrs hrev)
      _ = _ := by ring
  have hpr := hT.2.1 r hr
  have hps := hT.2.1 s hs
  have hMrpos : 0 < T.M r := zero_lt_one.trans_le hpr.2.2.2
  have hMspos : 0 < T.M s := zero_lt_one.trans_le hps.2.2.2
  have hHrγ := rpow_le_mul_rpow_of_twoSided hpr.2.1 (materialH_pos (X r))
    hKH0 hHr hHr' γ
  have hMrη := rpow_le_mul_rpow_of_twoSided hMrpos (materialM_pos (X r))
    hKM0 hMr hMr' η
  have hErR := Real.rpow_le_rpow hpr.2.2.1.le hEr hR
  rw [Real.mul_rpow hKE0.le (materialE0_pos (X r)).le] at hErR
  have hHsγ := rpow_le_mul_rpow_of_twoSided (materialH_pos (X s)) hps.2.1
    hKH0 hHs' hHs γ
  have hMsη := rpow_le_mul_rpow_of_twoSided (materialM_pos (X s)) hMspos
    hKM0 hMs' hMs η
  have hEsA := Real.rpow_le_rpow (materialE0_pos (X s)).le hEs' hA
  rw [Real.mul_rpow hKE0.le hps.2.2.1.le] at hEsA
  have hfirst : T.H r ^ γ * T.M r ^ η * T.E0 r ^ R ≤
      KF * (materialH (X r) ^ γ * materialM (X r) ^ η * materialE0 (X r) ^ R) := by
    have hHnonneg := mul_nonneg (Real.rpow_nonneg hKH0.le |γ|)
      (Real.rpow_nonneg (materialH_pos (X r)).le γ)
    have hMnonneg := mul_nonneg (Real.rpow_nonneg hKM0.le |η|)
      (Real.rpow_nonneg (materialM_pos (X r)).le η)
    have hp := mul_le_mul hHrγ hMrη (Real.rpow_nonneg hMrpos.le η) hHnonneg
    have he := mul_le_mul hp hErR (Real.rpow_nonneg hpr.2.2.1.le R)
      (mul_nonneg hHnonneg hMnonneg)
    exact he.trans_eq (by dsimp only [KF]; ring)
  have hlast : materialH (X s) ^ γ * materialM (X s) ^ η * materialE0 (X s) ^ A ≤
      KG * (T.H s ^ γ * T.M s ^ η * T.E0 s ^ A) := by
    have hHnonneg := mul_nonneg (Real.rpow_nonneg hKH0.le |γ|)
      (Real.rpow_nonneg hps.2.1.le γ)
    have hMnonneg := mul_nonneg (Real.rpow_nonneg hKM0.le |η|)
      (Real.rpow_nonneg hMspos.le η)
    have hp := mul_le_mul hHsγ hMsη (Real.rpow_nonneg (materialM_pos (X s)).le η)
      hHnonneg
    have he := mul_le_mul hp hEsA (Real.rpow_nonneg (materialE0_pos (X s)).le A)
      (mul_nonneg hHnonneg hMnonneg)
    exact he.trans_eq (by dsimp only [KG]; ring)
  calc
    _ ≤ KF * (materialH (X r) ^ γ * materialM (X r) ^ η * materialE0 (X r) ^ R) := hfirst
    _ ≤ KF * (K * (materialH (X s) ^ γ * materialM (X s) ^ η * materialE0 (X s) ^ A)) :=
      mul_le_mul_of_nonneg_left (hshift (X r) (X s) hxr hxs hdist) hKF.le
    _ ≤ KF * (K * (KG * (T.H s ^ γ * T.M s ^ η * T.E0 s ^ A))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hK.le) hKF.le
    _ = _ := by ring

end ContinuousFlexibility.Statements
