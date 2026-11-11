import ContinuousFlexibility.Analysis.CylinderMixedJets
import ContinuousFlexibility.Analysis.FlatCylinderExtension
import ContinuousFlexibility.Analysis.MaterialEndpointDecay

/-!
# Flat extension from ordinary material-weighted jet bounds

The jet bounds produced by local Sobolev estimates and material derivative
expansion imply decay faster than every fixed power of endpoint distance.
At each finite order, one common neighborhood works for every coordinate
jet. The actual Fréchet jets therefore satisfy the quadratic bound for
smooth zero extension.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

private theorem material_height_mixed_decay {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hT : IsMaterialData D T) (hγ : 0 < γ)
    (a b : ℕ) (hbound : ∃ K A : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      |mixedDerivative a b f p| ≤ K * T.H p.1 ^ γ * T.M p.1 ^ A)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ annularOpen D, endpointDistance D p.1 < δ →
      |mixedDerivative a b f p| < ε * endpointDistance D p.1 ^ k := by
  obtain ⟨K, A, hK, hbound⟩ := hbound
  have hKpos : 0 < K + 1 := by linarith
  obtain ⟨δ, hδ, hdecay⟩ := exists_material_endpoint_decay hT hγ (div_pos hε hKpos) A k
  refine ⟨δ, hδ, fun p hp hnear => ?_⟩
  have hd : 0 < endpointDistance D p.1 := lt_min (sub_pos.mpr hp.1.1) (sub_pos.mpr hp.1.2)
  have hdPow : 0 < endpointDistance D p.1 ^ k := pow_pos hd k
  have hpos := hT.2.1 p.1 hp.1
  have hweight : 0 ≤ T.H p.1 ^ γ * T.M p.1 ^ A / endpointDistance D p.1 ^ k :=
    div_nonneg (mul_nonneg (Real.rpow_pos_of_pos hpos.2.1 _).le
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hpos.2.2.2) _).le) hdPow.le
  apply (div_lt_iff₀ hdPow).mp
  calc
    |mixedDerivative a b f p| / endpointDistance D p.1 ^ k ≤
        K * (T.H p.1 ^ γ * T.M p.1 ^ A / endpointDistance D p.1 ^ k) := by
      rw [← mul_div_assoc, ← mul_assoc]
      exact div_le_div_of_nonneg_right (hbound p hp) hdPow.le
    _ ≤ (K + 1) * (T.H p.1 ^ γ * T.M p.1 ^ A / endpointDistance D p.1 ^ k) :=
      mul_le_mul_of_nonneg_right (by linarith) hweight
    _ < (K + 1) * (ε / (K + 1)) :=
      mul_lt_mul_of_pos_left (hdecay p.1 hp.1 hnear) hKpos
    _ = ε := by field_simp [hKpos.ne']

/-- Ordinary bounds of the prescribed material size imply the full
two-ended flat-jet estimate and genuine smoothness of the actual zero
extension already used in the height space. -/
theorem material_height_extension_of_ordinary_bounds {D : ReferenceData}
    {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hγ : 0 < γ) (hf : HeightMember D T γ f)
    (hbound : ∀ a b : ℕ, ∃ K A : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      |mixedDerivative a b f p| ≤ K * T.H p.1 ^ γ * T.M p.1 ^ A) :
    ContDiff ℝ ∞ f ∧ UniformFlatJets D f := by
  have hdecay (a b k : ℕ) (ε : ℝ) (hε : 0 < ε) :=
    material_height_mixed_decay hT hγ a b (hbound a b) k hε
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hjet (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ p : PolarPoint, p.1 ∈ Ioo D.a D.b →
      endpointDistance D p.1 < δ → ‖iteratedFDeriv ℝ n f p‖ ≤ endpointDistance D p.1 ^ 2 := by
    classical
    let c : ℝ := (2 : ℝ) ^ n
    have hc : 0 < c := pow_pos (by norm_num) _
    have hn (i : Fin (n + 1)) := hdecay i.val (n - i.val) 2 c⁻¹ (inv_pos.mpr hc)
    choose δ hδ hδdecay using hn
    obtain ⟨i, _, hmin⟩ := Finset.exists_min_image
      (Finset.univ : Finset (Fin (n + 1))) δ Finset.univ_nonempty
    refine ⟨δ i, hδ i, fun p hp hnear => ?_⟩
    have hpU : p ∈ annularOpen D := ⟨hp, mem_univ _⟩
    have hnonneg : 0 ≤ c⁻¹ * endpointDistance D p.1 ^ 2 :=
      mul_nonneg (inv_nonneg.mpr hc.le) (sq_nonneg _)
    calc
      ‖iteratedFDeriv ℝ n f p‖ ≤ (2 : ℝ) ^ n * (c⁻¹ * endpointDistance D p.1 ^ 2) := by
        apply norm_iteratedFDeriv_le_of_mixedDerivative hU hf.1 n hpU hnonneg
        intro a b hab
        let j : Fin (n + 1) := ⟨a, by omega⟩
        have hsub : n - j.val = b := by dsimp [j]; omega
        have hh := hδdecay j p hpU (hnear.trans_le (hmin j (Finset.mem_univ j)))
        rw [hsub] at hh
        simpa only [j, Real.norm_eq_abs] using hh.le
      _ = endpointDistance D p.1 ^ 2 := by change c * (c⁻¹ * _) = _; field_simp [hc.ne']
  have hext := Analysis.smooth_cylinder_zero_extension hf.1 hjet
  have hindicator : (annularOpen D).indicator f = f := by
    funext p
    by_cases hp : p ∈ annularOpen D
    · exact indicator_of_mem hp _
    · rw [indicator_of_notMem hp, hf.2.2.2.1 p hp]
  have hsmooth : ContDiff ℝ ∞ f := by
    have h := hext.1
    change ContDiff ℝ ∞ ((annularOpen D).indicator f) at h
    rwa [hindicator] at h
  refine ⟨hsmooth, fun a b k ε hε => ?_⟩
  obtain ⟨δ, hδ, hbound⟩ := hdecay a b k ε hε
  refine ⟨δ, hδ, fun r θ hr _ hnear => ?_⟩
  have hd : 0 < endpointDistance D r := lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hdPow : 0 < endpointDistance D r ^ k := pow_pos hd k
  have h := (div_lt_iff₀ hdPow).mpr (hbound (r, θ) ⟨hr, mem_univ θ⟩ hnear)
  rwa [zpow_neg, zpow_natCast, abs_mul, abs_inv, abs_of_pos hdPow, ← div_eq_inv_mul]

end ContinuousFlexibility.Statements
