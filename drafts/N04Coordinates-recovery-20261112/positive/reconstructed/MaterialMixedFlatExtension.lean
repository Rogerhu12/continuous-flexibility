import ContinuousFlexibility.Analysis.CylinderMixedJets
import ContinuousFlexibility.Analysis.FlatCylinderExtension
import ContinuousFlexibility.Analysis.MaterialEndpointDecay

/-!
# Flat zero extension of a material-small scalar field

Only actual interior smoothness and ordinary mixed-jet bounds are used.
No parity, periodicity, Hilbert-space membership or ambient values of the
original totalized field are needed. The resulting representative is its
literal zero extension, with every ordinary jet zero on the complement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem material_mixed_decay_of_weight_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hγ : 0 < γ) (a b : ℕ)
    (hbound : ∃ K A : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      |mixedDerivative a b f p| ≤ K * T.H p.1 ^ γ * T.M p.1 ^ A)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ annularOpen D, endpointDistance D p.1 < δ →
      |mixedDerivative a b f p| < ε * endpointDistance D p.1 ^ k := by
  obtain ⟨K, A, hK, hb⟩ := hbound
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
      exact div_le_div_of_nonneg_right (hb p hp) hdPow.le
    _ ≤ (K + 1) * (T.H p.1 ^ γ * T.M p.1 ^ A / endpointDistance D p.1 ^ k) :=
      mul_le_mul_of_nonneg_right (by linarith) hweight
    _ < (K + 1) * (ε / (K + 1)) :=
      mul_lt_mul_of_pos_left (hdecay p.1 hp.1 hnear) hKpos
    _ = ε := by field_simp [hKpos.ne']

theorem smooth_annular_zero_extension_of_material_mixed_bounds
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hγ : 0 < γ)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hbound : ∀ a b : ℕ, ∃ K A : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      |mixedDerivative a b f p| ≤ K * T.H p.1 ^ γ * T.M p.1 ^ A) :
    ContDiff ℝ ∞ ((annularOpen D).indicator f) ∧
      ∀ n (p : PolarPoint), p.1 ∉ Ioo D.a D.b →
        iteratedFDeriv ℝ n ((annularOpen D).indicator f) p = 0 := by
  have hdecay (a b k : ℕ) (ε : ℝ) (hε : 0 < ε) :=
    material_mixed_decay_of_weight_bound hT hγ a b (hbound a b) k hε
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
        apply norm_iteratedFDeriv_le_of_mixedDerivative hU hf n hpU hnonneg
        intro a b hab
        let j : Fin (n + 1) := ⟨a, by omega⟩
        have hsub : n - j.val = b := by dsimp [j]; omega
        have hh := hδdecay j p hpU (hnear.trans_le (hmin j (Finset.mem_univ j)))
        rw [hsub] at hh
        simpa only [j, Real.norm_eq_abs] using hh.le
      _ = endpointDistance D p.1 ^ 2 := by change c * (c⁻¹ * _) = _; field_simp [hc.ne']
  exact smooth_cylinder_zero_extension hf hjet

end ContinuousFlexibility.Analysis
