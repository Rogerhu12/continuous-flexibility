import ContinuousFlexibility.Analysis.MaterialPlateauGeometry

/-!
# Comparing actual material weights with their endpoint formulas

The formulas hold exactly near both endpoints. On the remaining compact
interval, positivity and continuity give two-sided comparison constants.
Thus products with arbitrary fixed real powers can be transported between
the supplied physical weights and the explicit endpoint model without
changing any exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
  (endpointX materialH materialE0 materialM materialH_pos materialE0_pos materialM_pos
    continuous_materialH continuousOn_materialE0 continuousOn_materialM)

set_option backward.isDefEq.respectTransparency false

theorem positive_functions_comparable_off_compact {f g : ℝ → ℝ} {U K : Set ℝ}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfp : ∀ r ∈ U, 0 < f r) (hgp : ∀ r ∈ U, 0 < g r)
    (heq : ∀ r ∈ U, r ∉ K → f r = g r) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ U, f r ≤ C * g r ∧ g r ≤ C * f r := by
  have hfg : ContinuousOn (fun r => f r / g r) K :=
    (hf.mono hKU).div (hg.mono hKU) (fun r hr => (hgp r (hKU hr)).ne')
  have hgf : ContinuousOn (fun r => g r / f r) K :=
    (hg.mono hKU).div (hf.mono hKU) (fun r hr => (hfp r (hKU hr)).ne')
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hfg
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hgf
  let C : ℝ := max (max A B) 1
  have hC : 1 ≤ C := le_max_right _ _
  refine ⟨C, zero_lt_one.trans_le hC, ?_⟩
  intro r hr
  by_cases hrK : r ∈ K
  · have hab : f r / g r ≤ A := by
      simpa only [Real.norm_eq_abs, abs_of_pos (div_pos (hfp r hr) (hgp r hr))] using hA r hrK
    have hba : g r / f r ≤ B := by
      simpa only [Real.norm_eq_abs, abs_of_pos (div_pos (hgp r hr) (hfp r hr))] using hB r hrK
    exact ⟨(div_le_iff₀ (hgp r hr)).mp
        (hab.trans ((le_max_left A B).trans (le_max_left _ _))),
      (div_le_iff₀ (hfp r hr)).mp
        (hba.trans ((le_max_right A B).trans (le_max_left _ _)))⟩
  · rw [heq r hr hrK]
    exact ⟨by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (hgp r hr).le,
      by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (hgp r hr).le⟩

def materialWeightProduct (T : MaterialData) (α β γ : ℝ) (r : ℝ) : ℝ :=
  T.H r ^ α * T.E0 r ^ β * T.M r ^ γ

def materialEndpointProduct (D : ReferenceData) (d₀ α β γ : ℝ) (r : ℝ) : ℝ :=
  materialH (endpointX d₀ (endpointDistance D r)) ^ α *
    materialE0 (endpointX d₀ (endpointDistance D r)) ^ β *
    materialM (endpointX d₀ (endpointDistance D r)) ^ γ

theorem materialWeightProduct_pos {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (α β γ : ℝ) {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    0 < materialWeightProduct T α β γ r := by
  have hp := hT.2.1 r hr
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hp.2.1 α)
    (Real.rpow_pos_of_pos hp.2.2.1 β))
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hp.2.2.2) γ)

theorem materialEndpointProduct_pos (D : ReferenceData) (d₀ α β γ r : ℝ) :
    0 < materialEndpointProduct D d₀ α β γ r :=
  mul_pos (mul_pos (Real.rpow_pos_of_pos (materialH_pos _) α)
    (Real.rpow_pos_of_pos (materialE0_pos _) β))
    (Real.rpow_pos_of_pos (materialM_pos _) γ)

theorem materialWeightProduct_continuousOn {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (α β γ : ℝ) :
    ContinuousOn (materialWeightProduct T α β γ) (Ioo D.a D.b) := by
  have hH := (hT.1 T.H (by simp)).continuousOn
  have hE := (hT.1 T.E0 (by simp)).continuousOn
  have hM := (hT.1 T.M (by simp)).continuousOn
  exact ((hH.rpow_const (fun r hr => Or.inl (hT.2.1 r hr).2.1.ne')).mul
    (hE.rpow_const (fun r hr => Or.inl (hT.2.1 r hr).2.2.1.ne'))).mul
    (hM.rpow_const (fun r hr => Or.inl (zero_lt_one.trans_le (hT.2.1 r hr).2.2.2).ne'))

theorem materialEndpointProduct_continuousOn {D : ReferenceData} {d₀ : ℝ}
    (hd₀ : 0 < d₀) (α β γ : ℝ) :
    ContinuousOn (materialEndpointProduct D d₀ α β γ) (Ioo D.a D.b) := by
  have hX := continuousOn_endpointX_distance (D := D) hd₀
  have hH : ContinuousOn (fun r => materialH (endpointX d₀ (endpointDistance D r)))
      (Ioo D.a D.b) := continuous_materialH.comp_continuousOn hX
  have hE : ContinuousOn (fun r => materialE0 (endpointX d₀ (endpointDistance D r)))
      (Ioo D.a D.b) :=
    continuousOn_materialE0.comp hX (fun _ _ => Real.sqrt_nonneg _)
  have hM : ContinuousOn (fun r => materialM (endpointX d₀ (endpointDistance D r)))
      (Ioo D.a D.b) :=
    continuousOn_materialM.comp hX (fun _ _ => Real.sqrt_nonneg _)
  exact ((hH.rpow_const (fun _ _ => Or.inl (materialH_pos _).ne')).mul
    (hE.rpow_const (fun _ _ => Or.inl (materialE0_pos _).ne'))).mul
    (hM.rpow_const (fun _ _ => Or.inl (materialM_pos _).ne'))

/-- One endpoint scale works for every fixed product of real powers; the
comparison constants depend on the powers, while the exponents stay exact. -/
theorem materialWeightProduct_endpoint_comparison
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ α β γ : ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ r ∈ Ioo D.a D.b,
        materialWeightProduct T α β γ r ≤ C * materialEndpointProduct D d₀ α β γ r ∧
        materialEndpointProduct D d₀ α β γ r ≤ C * materialWeightProduct T α β γ r := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hend, _⟩ := hdata
  obtain ⟨d₀, δ, hd₀, hδ, hδbound, hleft, hright⟩ := hend
  have hδhalf : δ < (D.b - D.a) / 2 := hδbound.trans_le (min_le_right _ _)
  refine ⟨d₀, hd₀, ?_⟩
  intro α β γ
  apply positive_functions_comparable_off_compact (U := Ioo D.a D.b)
    (K := Icc (D.a + δ) (D.b - δ))
    isCompact_Icc (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    (materialWeightProduct_continuousOn hT α β γ)
    (materialEndpointProduct_continuousOn hd₀ α β γ)
    (fun r hr => materialWeightProduct_pos hT α β γ hr)
    (fun r _ => materialEndpointProduct_pos D d₀ α β γ r)
  intro r hr hrK
  simp only [mem_Icc, not_and_or, not_le] at hrK
  rcases hrK with hrK | hrK
  · have hweights := hleft r ⟨hr.1, hrK⟩
    have hside : r - D.a ≤ D.b - r := by linarith only [hrK, hδhalf]
    simp only [materialWeightProduct, materialEndpointProduct, endpointDistance,
      min_eq_left hside, hweights.2.1, hweights.2.2.1, hweights.2.2.2]
  · have hweights := hright r ⟨hrK, hr.2⟩
    have hside : D.b - r ≤ r - D.a := by linarith only [hrK, hδhalf]
    simp only [materialWeightProduct, materialEndpointProduct, endpointDistance,
      min_eq_right hside, hweights.2.1, hweights.2.2.1, hweights.2.2.2]

end ContinuousFlexibility.Statements
