import ContinuousFlexibility.Analysis.N04RealizationTransportRatios

/-!
# From sampled subpower envelopes to the physical material weight

The inverse material-ratio atom is multiplied into the complete sampled
envelope before its one-power estimate is used. Its positive factor then
cancels, leaving one power of the material weight at the actual point.
This estimate is uniform in the piece index and is valid for any family
of domains carrying the displayed material comparison.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

/-- Absorb the complete sampled coefficient and the inverse ratio together.
The result uses the material weight at the point, rather than at the sample. -/
theorem n04Realization_sampleSubpower_point_weight
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {W : ℕ → Set PolarPoint}
    (hcore : ∀ m p, p ∈ W m → p.1 ∈ radialCore D)
    {a e : ℕ → ℝ} (ha : N07aSampleSubpower T K a) (ha1 : ∀ m, 1 ≤ a m)
    (hratio : ∀ m p, p ∈ W m → T.M (T.sample (K.cell m)) / T.M p.1 ≤ a m)
    (he : N07aSampleSubpower T K e) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ W m → |e m| ≤ B * T.M p.1 := by
  obtain ⟨B, hB, hbound⟩ := (N07aSampleSubpower.mul hD hT he ha).one_power
  refine ⟨B, hB, fun m p hp => ?_⟩
  have ha0 : 0 < a m := zero_lt_one.trans_le (ha1 m)
  have hM : 0 < T.M p.1 := zero_lt_one.trans_le (hT.2.1 _ (hcore m p hp)).2.2.2
  have hsample : T.M (T.sample (K.cell m)) ≤ a m * T.M p.1 :=
    (div_le_iff₀ hM).mp (hratio m p hp)
  apply (mul_le_mul_iff_of_pos_right ha0).mp
  calc
    |e m| * a m = |e m * a m| := by rw [abs_mul, abs_of_pos ha0]
    _ ≤ B * T.M (T.sample (K.cell m)) := hbound m
    _ ≤ B * (a m * T.M p.1) := mul_le_mul_of_nonneg_left hsample hB.le
    _ = (B * T.M p.1) * a m := by ring

/-- Reference jets supply the exact inverse ratio needed for the pointwise
conversion of any sampled subpower envelope. -/
theorem n04Realization_sampleSubpower_reference_weight
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    {e : ℕ → ℝ} (he : N07aSampleSubpower T K e) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      |e m| ≤ B * T.M p.1 := by
  obtain ⟨a, ha, ha1, hab⟩ := n07a_material_piece_ratio_envelope hD hT href
    (fun m => (hgeom.referenceBounds m).1)
  exact n04Realization_sampleSubpower_point_weight hD hT
    (fun m p hp => (hgeom.referenceBounds m).2.2 hp.1) ha ha1
    (fun m p hp => (hab m p hp).2.2.2) he

/-- A continuous scalar bound by a sampled envelope on the reference pieces
extends to a bound by the physical material weight on the whole annulus. -/
theorem n04Realization_continuous_weighted_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    {f : PolarPoint → ℝ} (hf : ContinuousOn f (annularOpen D))
    {e : ℕ → ℝ} (he : N07aSampleSubpower T K e)
    (hbound : ∀ m p, p ∈ referencePhysicalPieceOpen S K m → f p ≤ e m) :
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ annularOpen D, f p ≤ B * T.M p.1 := by
  obtain ⟨B, hB, hpoint⟩ := n04Realization_sampleSubpower_reference_weight hD hT hgeom href he
  have hM : ContDiffOn ℝ ∞ T.M (radialCore D) := hT.1 T.M (by simp)
  have hMpos (p : PolarPoint) (hp : p ∈ annularOpen D) : 0 < T.M p.1 :=
    zero_lt_one.trans_le (hT.2.1 _ hp.1).2.2.2
  have hcont : ContinuousOn (fun p : PolarPoint => f p / T.M p.1) (annularOpen D) :=
    hf.div (hM.continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1))
      (fun p hp => (hMpos p hp).ne')
  have hcover : ∃ E : Set ℝ, volume E = 0 ∧ ∀ r ∈ Ioo D.a D.b \ E,
      ∃ m : ℕ, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) := by
    obtain ⟨E, hE, hcover⟩ := hgeom.referencePartition
    exact ⟨E, hE, fun r hr => (hcover r hr).exists⟩
  have hratio : ∀ p ∈ annularOpen D, f p / T.M p.1 ≤ B := by
    apply n04Realization_continuous_bound_of_radial_cover hcover hcont
    intro m p hp
    have hpD : p ∈ annularOpen D := ⟨(hgeom.referenceBounds m).2.2 hp.1, mem_univ _⟩
    exact (div_le_iff₀ (hMpos p hpD)).mpr
      ((hbound m p hp).trans ((le_abs_self (e m)).trans (hpoint m p hp)))
  exact ⟨B, hB, fun p hp => (div_le_iff₀ (hMpos p hp)).mp (hratio p hp)⟩

/-- Local equality transfers the actual derivative bound. Finite global
regularity then extends it across every radial interface of the atlas. -/
theorem n04Realization_iteratedFDeriv_weighted_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    {f : PolarPoint → F} (hf : ContDiffOn ℝ 3 f (annularOpen D))
    {g : ℕ → PolarPoint → F}
    (heq : ∀ m, EqOn f (g m) (referencePhysicalPieceOpen S K m))
    {n : ℕ} (hn : n ≤ 2) {e : ℕ → ℝ} (he : N07aSampleSubpower T K e)
    (hbound : ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      ‖iteratedFDeriv ℝ n (g m) p‖ ≤ e m) :
    ∃ B : ℝ, 0 < B ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n f p‖ ≤ B * T.M p.1 := by
  have hcont : ContinuousOn (fun p => ‖iteratedFDeriv ℝ n f p‖) (annularOpen D) := by
    intro p hp
    have hn' : (n : ℕ∞ω) ≤ 3 := by exact_mod_cast (show n ≤ 3 by omega)
    exact ((hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).continuousAt_iteratedFDeriv
      hn').norm.continuousWithinAt
  apply n04Realization_continuous_weighted_bound hD hT hgeom href hcont he
  intro m p hp
  have hlocal : f =ᶠ[𝓝 p] g m := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with y hy
    exact heq m hy
  rw [(hlocal.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hbound m p hp

end ContinuousFlexibility.Analysis
