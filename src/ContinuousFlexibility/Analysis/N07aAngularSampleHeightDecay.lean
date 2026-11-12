import ContinuousFlexibility.Analysis.N07aAngularFixedJetEnvelope
import ContinuousFlexibility.Analysis.N07aMaterialPieceBounds

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

theorem n07a_sampleHeight_decay_on_physicalPiece
    {F : Type*} [NormedAddCommGroup F]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m)
    (hcore : ∀ m, Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D)
    {β γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hgap : γ < β)
    {f : ℕ → PolarPoint → F} {e : ℕ → ℝ}
    (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m)
    (hb : ∀ m p, p ∈ physicalPieceOpen S K m →
      ‖f m p‖ ≤ e m * T.H (T.sample (K.cell m)) ^ β) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ physicalPieceOpen S K m →
      ‖f m p‖ ≤ B * T.H p.1 ^ γ := by
  obtain ⟨a, ha, ha1, hab⟩ := n07a_material_piece_ratio_envelope hD hT href hphysical
  obtain ⟨B, hB, hBb⟩ := (N07aSampleSubpower.mul hD hT he ha).height_absorption
    hD hT (sub_pos.mpr hgap)
  refine ⟨B, hB, fun m p hp => (hb m p hp).trans ?_⟩
  have hsample := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  have hH₀ : 0 < T.H (T.sample (K.cell m)) := (hT.2.1 _ hsample).2.1
  have hH : 0 < T.H p.1 := (hT.2.1 _ (hcore m hp.1)).2.1
  have ha0 : 0 ≤ a m := zero_le_one.trans (ha1 m)
  have hheight : T.H (T.sample (K.cell m)) ^ γ ≤ a m * T.H p.1 ^ γ := by
    have h := n07a_material_piece_decay_compare hH₀ hH zero_lt_one zero_lt_one
      (ha1 m) (hab m p hp).2.1 (by simpa only [div_one] using ha1 m) hγ hγ1 0
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

theorem N07aAngularFixedJetEnvelope.physical_height_decay
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m)
    (hcore : ∀ m, Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D)
    {β γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hgap : γ < β)
    {f : ℕ → PolarPoint → F}
    (hf : N07aAngularFixedJetEnvelope T K (physicalPieceOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ β) f) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ physicalPieceOpen S K m →
      ‖iteratedFDeriv ℝ n (f m) p‖ ≤ B * T.H p.1 ^ γ := by
  obtain ⟨e, he, he0, heb⟩ := hf n
  exact n07a_sampleHeight_decay_on_physicalPiece hD hT href hphysical hcore
    hγ hγ1 hgap he he0 heb

end ContinuousFlexibility.Analysis
