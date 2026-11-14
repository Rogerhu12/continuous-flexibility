module

public import ContinuousFlexibility.Analysis.N07aActualMaterialComparison

/-!
# Absorbing the complete piece envelope without changing height weight

The two extra material orders are fixed. All geometric factors, including
the comparison between sampled and physical weights, enter the same
subpower envelope before its single material power is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε γ : ℝ}

private theorem n07a_weighted_sample_cancellation
    {H M E R γ : ℝ} (hH : 0 < H) (hM : 0 < M) (c : ℕ) :
    E * M ^ c * H ^ (-γ) * (R ^ (c + 3) * H ^ γ * (M ^ (c + 2))⁻¹) =
      (E * R ^ (c + 3)) * (M ^ 2)⁻¹ := by
  rw [Real.rpow_neg hH.le, pow_add M c 2]
  field_simp [hM.ne', (Real.rpow_pos_of_pos hH γ).ne', pow_ne_zero c hM.ne']
  <;> ring

private theorem n07a_sampleMaterial_absorb_of_ratios
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {ι : Type*} (U : Set ι) (W : ι → ℕ → Set PolarPoint)
    (hcore : ∀ z ∈ U, ∀ m x, x ∈ W z m → x.1 ∈ radialCore D)
    {r : ℕ → ℝ} (hrs : N07aSampleSubpower T K r) (hr1 : ∀ m, 1 ≤ r m)
    (hrb : ∀ z ∈ U, ∀ m x, x ∈ W z m →
      T.H x.1 / T.H (T.sample (K.cell m)) ≤ r m ∧
      T.H (T.sample (K.cell m)) / T.H x.1 ≤ r m ∧
      T.M x.1 / T.M (T.sample (K.cell m)) ≤ r m ∧
      T.M (T.sample (K.cell m)) / T.M x.1 ≤ r m)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {e : ℕ → ℝ} (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m)
    (c : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z ∈ U, ∀ m x, x ∈ W z m →
      e m * T.M x.1 ^ c * T.H x.1 ^ (-γ) *
        (T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ (c + 2))⁻¹) ≤
          A * (T.M x.1)⁻¹ := by
  have hfull := N07aSampleSubpower.mul hD hT he (hrs.nat_pow hD hT (c + 4))
  obtain ⟨A, hA, hAb⟩ := hfull.one_power
  refine ⟨A, hA, fun z hz m x hx => ?_⟩
  have hxD := hcore z hz m x hx
  have hxp := hT.2.1 x.1 hxD
  have hsp := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  have hMx : 0 < T.M x.1 := zero_lt_one.trans_le hxp.2.2.2
  have hMs : 0 < T.M (T.sample (K.cell m)) := zero_lt_one.trans_le hsp.2.2.2
  have hR : 0 < r m := zero_lt_one.trans_le (hr1 m)
  have hrat := hrb z hz m x hx
  have hdecay := n07a_material_piece_decay_compare hsp.2.1 hxp.2.1
    hMs hMx (hr1 m) hrat.2.1 hrat.2.2.1 hγ hγ1 (c + 2)
  have hMsx : T.M (T.sample (K.cell m)) ≤ r m * T.M x.1 :=
    (div_le_iff₀ hMx).mp hrat.2.2.2
  have hcomplete : e m * r m ^ (c + 4) ≤ A * (r m * T.M x.1) :=
    ((le_abs_self _).trans (hAb m)).trans (mul_le_mul_of_nonneg_left hMsx hA.le)
  have heR : e m * r m ^ (c + 3) ≤ A * T.M x.1 := by
    apply (mul_le_mul_iff_left₀ hR).mp
    calc
      (e m * r m ^ (c + 3)) * r m = e m * r m ^ (c + 4) := by
        rw [show c + 4 = (c + 3) + 1 by omega, pow_succ]
        ring
      _ ≤ A * (r m * T.M x.1) := hcomplete
      _ = (A * T.M x.1) * r m := by ring
  calc
    _ ≤ e m * T.M x.1 ^ c * T.H x.1 ^ (-γ) *
        (r m ^ (c + 3) * T.H x.1 ^ γ * (T.M x.1 ^ (c + 2))⁻¹) :=
      mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg (mul_nonneg (he0 m) (pow_nonneg hMx.le c))
          (Real.rpow_nonneg hxp.2.1.le _))
    _ = (e m * r m ^ (c + 3)) * (T.M x.1 ^ 2)⁻¹ :=
      n07a_weighted_sample_cancellation hxp.2.1 hMx c
    _ ≤ (A * T.M x.1) * (T.M x.1 ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right heR (inv_nonneg.mpr (sq_nonneg _))
    _ = A * (T.M x.1)⁻¹ := by field_simp [hMx.ne'] <;> ring

theorem n07a_sampleMaterial_absorb
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {e : ℕ → ℝ} (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m)
    (c : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ m x, x ∈ referencePhysicalPieceOpen S K m →
      e m * T.M x.1 ^ c * T.H x.1 ^ (-γ) *
        (T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ (c + 2))⁻¹) ≤
          A * (T.M x.1)⁻¹ := by
  obtain ⟨r, hrs, hr1, hrb⟩ := n07a_material_piece_ratio_envelope hD hT href
    (fun m => (h04.1.referenceBounds m).1)
  obtain ⟨A, hA, hAb⟩ := n07a_sampleMaterial_absorb_of_ratios hD hT
    (univ : Set Unit) (fun _ => referencePhysicalPieceOpen S K)
    (fun _ _ m x hx => (h04.1.referenceBounds m).2.2 hx.1)
    hrs hr1 (fun _ _ => hrb) hγ hγ1 he he0 c
  exact ⟨A, hA, fun m x hx => hAb () (mem_univ _) m x hx⟩

/-- The same single material-power absorption holds on every current
physical piece, using the derived current ratio certificate. -/
theorem n07a_sampleMaterial_absorb_actual
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {e : ℕ → ℝ} (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m)
    (c : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m x,
      x ∈ physicalPieceOpen S K (liftSectorParameter S C z) m →
      e m * T.M x.1 ^ c * T.H x.1 ^ (-γ) *
        (T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ (c + 2))⁻¹) ≤
          A * (T.M x.1)⁻¹ := by
  obtain ⟨r, hrs, hr1, hrb⟩ := hRatio
  apply n07a_sampleMaterial_absorb_of_ratios hD hT
    (sectorNeighborhood S base ε ε)
    (fun z m => physicalPieceOpen S K (liftSectorParameter S C z) m)
    (fun z hz m x hx => ((hgeom.domains (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).2.2.1 hx).1)
    hrs hr1 hrb hγ hγ1 he he0 c

end ContinuousFlexibility.Analysis
