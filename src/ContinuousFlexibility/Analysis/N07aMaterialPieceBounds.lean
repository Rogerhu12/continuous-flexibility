module

public import ContinuousFlexibility.Analysis.N07aGeometryLengthBounds
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalMeasure

/-!
# Material ratios throughout each reference physical piece

The ratios are fixed geometric atoms, so their reference zero-jets control
them throughout the fixed reference interval. Comparison at an actual
current inverse-chart point is established separately from displacement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n07a_material_piece_ratio_envelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hinterval : ∀ m, K.physicalLeft m < K.physicalRight m) :
    ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 1 ≤ e m) ∧
      ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
        T.H p.1 / T.H (T.sample (K.cell m)) ≤ e m ∧
        T.H (T.sample (K.cell m)) / T.H p.1 ≤ e m ∧
        T.M p.1 / T.M (T.sample (K.cell m)) ≤ e m ∧
        T.M (T.sample (K.cell m)) / T.M p.1 ≤ e m := by
  obtain ⟨B, hB, hBb⟩ := href.2 0
  let e : ℕ → ℝ := fun m => 1 + B * T.E0 (T.sample (K.cell m)) ^ B
  have hsub : N07aSampleSubpower T K e :=
    (N07aSampleSubpower.const hD hT (K := K) 1).add
      (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT B)
        (N07aSampleSubpower.e0_rpow hD hT B))
  have he (m : ℕ) : 1 ≤ e m := by
    have hE := (hT.2.1 _
      (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))).2.2.1
    exact le_add_of_nonneg_right (mul_nonneg hB.le (Real.rpow_nonneg hE.le B))
  refine ⟨e, hsub, he, fun m p hp => ?_⟩
  let x := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m p
  have hx : x ∈ CanonicalGeometry.unitStrip :=
    n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData K) (hinterval m) hp
  have hpoint : CanonicalGeometry.physicalUnitPoint K m x = p :=
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K) (hinterval m) p
  have hb (a : CanonicalGeometry.Atom) :
      CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m a x ≤ e m := by
    have h := hBb m a x hx 0 0 (by omega)
    rw [spaces_mixedDerivative_zero] at h
    exact (le_abs_self _).trans (h.trans (by dsimp only [e]; linarith))
  have h₁ := hb .ratioH
  have h₂ := hb .ratioHInverse
  have h₃ := hb .ratioM
  have h₄ := hb .ratioMInverse
  change T.H (CanonicalGeometry.physicalUnitPoint K m x).1 /
    T.H (T.sample (K.cell m)) ≤ e m at h₁
  change T.H (T.sample (K.cell m)) /
    T.H (CanonicalGeometry.physicalUnitPoint K m x).1 ≤ e m at h₂
  change T.M (CanonicalGeometry.physicalUnitPoint K m x).1 /
    T.M (T.sample (K.cell m)) ≤ e m at h₃
  change T.M (T.sample (K.cell m)) /
    T.M (CanonicalGeometry.physicalUnitPoint K m x).1 ≤ e m at h₄
  rw [hpoint] at h₁ h₂ h₃ h₄
  exact ⟨h₁, h₂, h₃, h₄⟩

/-- The reciprocal material length is controlled on each fixed reference
piece by one sampled subpower envelope. -/
theorem n07a_reference_materialEllInverse_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hinterval : ∀ m, K.physicalLeft m < K.physicalRight m) :
    ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ m p, p ∈ referencePhysicalPieceOpen S K m → (T.ell p.1)⁻¹ ≤ e m := by
  obtain ⟨B, hB, hBb⟩ := href.2 0
  let e : ℕ → ℝ := fun m => B * T.E0 (T.sample (K.cell m)) ^ B
  have he : N07aSampleSubpower T K e := N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.const hD hT B) (N07aSampleSubpower.e0_rpow hD hT B)
  have he0 (m : ℕ) : 0 ≤ e m := by
    have hp := hT.2.1 _
      (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    exact mul_nonneg hB.le (Real.rpow_nonneg hp.2.2.1.le B)
  refine ⟨e, he, he0, fun m p hp => ?_⟩
  let x := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m p
  have hx : x ∈ CanonicalGeometry.unitStrip :=
    n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData K) (hinterval m) hp
  have hpoint : CanonicalGeometry.physicalUnitPoint K m x = p :=
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K) (hinterval m) p
  have hb := hBb m .materialEllInverse x hx 0 0 (by omega)
  rw [spaces_mixedDerivative_zero] at hb
  change |(T.ell (CanonicalGeometry.physicalUnitPoint K m x).1)⁻¹| ≤ e m at hb
  rw [hpoint] at hb
  exact (le_abs_self _).trans hb

/-- One fixed ratio envelope controls the actual height and any chosen
material weight. The integer power belongs to the complete envelope. -/
theorem n07a_material_piece_decay_compare
    {h h₀ m m₀ e γ : ℝ} (hh : 0 < h) (hh₀ : 0 < h₀)
    (hm : 0 < m) (hm₀ : 0 < m₀) (he : 1 ≤ e)
    (hhr : h / h₀ ≤ e) (hmr : m₀ / m ≤ e)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (c : ℕ) :
    h ^ γ * (m ^ c)⁻¹ ≤ e ^ (c + 1) * h₀ ^ γ * (m₀ ^ c)⁻¹ := by
  have hep : 0 < e := zero_lt_one.trans_le he
  have hratio : (h / h₀) ^ γ ≤ e :=
    (Real.rpow_le_rpow (div_pos hh hh₀).le hhr hγ).trans
      ((Real.rpow_le_rpow_of_exponent_le he hγ1).trans_eq (Real.rpow_one e))
  have hheight : h ^ γ ≤ h₀ ^ γ * e := by
    have hpow := mul_le_mul_of_nonneg_left hratio (Real.rpow_pos_of_pos hh₀ γ).le
    rw [Real.div_rpow hh.le hh₀.le] at hpow
    calc
      h ^ γ = h₀ ^ γ * (h ^ γ / h₀ ^ γ) := by
        field_simp [(Real.rpow_pos_of_pos hh₀ γ).ne']
      _ ≤ _ := hpow
  have hmweight : (m ^ c)⁻¹ ≤ e ^ c * (m₀ ^ c)⁻¹ := by
    have hpow := pow_le_pow_left₀ (div_pos hm₀ hm).le hmr c
    rw [div_pow] at hpow
    have h := mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr (pow_nonneg hm₀.le c))
    calc
      (m ^ c)⁻¹ = (m₀ ^ c / m ^ c) * (m₀ ^ c)⁻¹ := by
        field_simp [pow_ne_zero c hm.ne', pow_ne_zero c hm₀.ne']
      _ ≤ _ := h
  calc
    _ ≤ (h₀ ^ γ * e) * (e ^ c * (m₀ ^ c)⁻¹) :=
      mul_le_mul hheight hmweight (inv_nonneg.mpr (pow_nonneg hm.le c))
        (mul_nonneg (Real.rpow_pos_of_pos hh₀ γ).le hep.le)
    _ = _ := by rw [pow_succ]; ring

end ContinuousFlexibility.Analysis
