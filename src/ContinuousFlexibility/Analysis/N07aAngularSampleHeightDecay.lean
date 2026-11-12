import ContinuousFlexibility.Analysis.N07aAngularFixedJetEnvelope
import ContinuousFlexibility.Analysis.N07aActualMaterialComparison

/-!
# A strict height margin absorbs the complete physical transport envelope

The fixed-parameter reference transport need only enter a lower natural
exponent. The genuine material-ratio atom transfers the retained sampled
height to the actual physical radius, and the strict margin absorbs every
finite coefficient product at once.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n07a_sampleHeight_decay_of_ratios
    {F : Type*} [NormedAddCommGroup F]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {ι : Type*} (U : Set ι) (W : ι → ℕ → Set PolarPoint)
    (hcore : ∀ z ∈ U, ∀ m p, p ∈ W z m → p.1 ∈ radialCore D)
    {a : ℕ → ℝ} (ha : N07aSampleSubpower T K a) (ha1 : ∀ m, 1 ≤ a m)
    (hab : ∀ z ∈ U, ∀ m p, p ∈ W z m →
      T.H (T.sample (K.cell m)) / T.H p.1 ≤ a m)
    {β γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hgap : γ < β)
    {f : ι → ℕ → PolarPoint → F} {e : ℕ → ℝ}
    (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m)
    (hb : ∀ z ∈ U, ∀ m p, p ∈ W z m →
      ‖f z m p‖ ≤ e m * T.H (T.sample (K.cell m)) ^ β) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ U, ∀ m p, p ∈ W z m →
      ‖f z m p‖ ≤ B * T.H p.1 ^ γ := by
  obtain ⟨B, hB, hBb⟩ := (N07aSampleSubpower.mul hD hT he ha).height_absorption
    hD hT (sub_pos.mpr hgap)
  refine ⟨B, hB, fun z hz m p hp => (hb z hz m p hp).trans ?_⟩
  have hsample := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  have hH₀ : 0 < T.H (T.sample (K.cell m)) := (hT.2.1 _ hsample).2.1
  have hH : 0 < T.H p.1 := (hT.2.1 _ (hcore z hz m p hp)).2.1
  have ha0 : 0 ≤ a m := zero_le_one.trans (ha1 m)
  have hheight : T.H (T.sample (K.cell m)) ^ γ ≤ a m * T.H p.1 ^ γ := by
    have h := n07a_material_piece_decay_compare hH₀ hH zero_lt_one zero_lt_one
      (ha1 m) (hab z hz m p hp) (by simpa only [div_one] using ha1 m) hγ hγ1 0
    simpa only [pow_zero, inv_one, mul_one, Nat.zero_add, pow_one] using h
  have hHgap : 0 ≤ T.H (T.sample (K.cell m)) ^ (β - γ) :=
    (Real.rpow_pos_of_pos hH₀ _).le
  have hpow : T.H (T.sample (K.cell m)) ^ (β - γ) *
      T.H (T.sample (K.cell m)) ^ γ = T.H (T.sample (K.cell m)) ^ β := by
    rw [← Real.rpow_add hH₀, sub_add_cancel]
  calc
    e m * T.H (T.sample (K.cell m)) ^ β =
        (T.H (T.sample (K.cell m)) ^ (β - γ) * e m) *
          T.H (T.sample (K.cell m)) ^ γ := by
      rw [← hpow]
      ring
    _ ≤ (T.H (T.sample (K.cell m)) ^ (β - γ) * e m) *
        (a m * T.H p.1 ^ γ) :=
      mul_le_mul_of_nonneg_left hheight (mul_nonneg hHgap (he0 m))
    _ = (T.H (T.sample (K.cell m)) ^ (β - γ) * |e m * a m|) * T.H p.1 ^ γ := by
      rw [abs_of_nonneg (mul_nonneg (he0 m) ha0)]
      ring
    _ ≤ B * T.H p.1 ^ γ :=
      mul_le_mul_of_nonneg_right (hBb m) (Real.rpow_pos_of_pos hH γ).le

theorem n07a_sampleHeight_decay_on_physicalPiece
    {F : Type*} [NormedAddCommGroup F]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m)
    (hcore : ∀ m, Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D)
    {β γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hgap : γ < β)
    {f : ℕ → PolarPoint → F} {e : ℕ → ℝ}
    (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m)
    (hb : ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      ‖f m p‖ ≤ e m * T.H (T.sample (K.cell m)) ^ β) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      ‖f m p‖ ≤ B * T.H p.1 ^ γ := by
  obtain ⟨a, ha, ha1, hab⟩ := n07a_material_piece_ratio_envelope hD hT href hphysical
  obtain ⟨B, hB, hBb⟩ := n07a_sampleHeight_decay_of_ratios hD hT
    (univ : Set Unit) (fun _ => referencePhysicalPieceOpen S K)
    (fun _ _ m p hp => hcore m hp.1) ha ha1 (fun _ _ m p hp => (hab m p hp).2.1)
    hγ hγ1 hgap (f := fun _ => f) he he0 (fun _ _ => hb)
  exact ⟨B, hB, fun m p hp => hBb () (mem_univ _) m p hp⟩

/-- A strict height margin absorbs the full current transport envelope
at actual current physical points. -/
theorem n07a_sampleHeight_decay_on_physicalPiece_actual
    {F : Type*} [NormedAddCommGroup F]
    {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    {β γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hgap : γ < β)
    {f : CanonicalGeometry.Parameter S → ℕ → PolarPoint → F} {e : ℕ → ℝ}
    (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m)
    (hb : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m p,
      p ∈ physicalPieceOpen S K (liftSectorParameter S C z) m →
      ‖f z m p‖ ≤ e m * T.H (T.sample (K.cell m)) ^ β) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m p,
      p ∈ physicalPieceOpen S K (liftSectorParameter S C z) m →
      ‖f z m p‖ ≤ B * T.H p.1 ^ γ := by
  obtain ⟨a, ha, ha1, hab⟩ := hRatio
  exact n07a_sampleHeight_decay_of_ratios hD hT
    (sectorNeighborhood S base ε ε)
    (fun z m => physicalPieceOpen S K (liftSectorParameter S C z) m)
    (fun z hz m p hp => ((hgeom.domains (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).2.2.1 hp).1)
    ha ha1 (fun z hz m p hp => (hab z hz m p hp).2.1)
    hγ hγ1 hgap he he0 hb

theorem N07aAngularFixedJetEnvelope.physical_height_decay
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m)
    (hcore : ∀ m, Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D)
    {β γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hgap : γ < β)
    {f : ℕ → PolarPoint → F}
    (hf : N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ β) f) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      ‖iteratedFDeriv ℝ n (f m) p‖ ≤ B * T.H p.1 ^ γ := by
  obtain ⟨e, he, he0, heb⟩ := hf n
  exact n07a_sampleHeight_decay_on_physicalPiece hD hT href hphysical hcore
    hγ hγ1 hgap he he0 heb

end ContinuousFlexibility.Analysis
