import ContinuousFlexibility.Analysis.N07aActualMaterialComparison
import ContinuousFlexibility.Analysis.N07aAngularPieceCover
import ContinuousFlexibility.Analysis.N07aPhysicalPieceBound

/-!
# Compact support and continuous bounds on the moving pieces

The planar almost-everywhere partition gives pointwise inequalities by
continuity. Compact radial supports meet only finitely many current
pieces on the derived material-ratio neighborhood. The counting measure
uses the disjoint reference intervals; it does not identify them with the
current domains.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ENNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_actualPhysicalPiece_bound
    (hgeom : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {f B : PolarPoint → ℝ} (hf : ContinuousOn f (annularOpen D))
    (hB : ContinuousOn B (annularOpen D))
    (hbound : ∀ m p, p ∈ physicalPieceOpen S K z m → f p ≤ B p) :
    ∀ p ∈ annularOpen D, f p ≤ B p := by
  obtain ⟨E, hE, hcover⟩ := hgeom.partition z hz hs
  have hEr : ∀ᵐ p ∂(volume : Measure PolarPoint), p ∉ E := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hE
  have hEr' := hEr.filter_mono (ae_mono (Measure.restrict_le_self
    (μ := (volume : Measure PolarPoint)) (s := annularOpen D)))
  have he : f =ᵐ[volume.restrict (annularOpen D)] fun p => min (f p) (B p) := by
    filter_upwards [hEr', ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)]
      with p hpE hpD
    obtain ⟨m, hm, _⟩ := hcover p ⟨hpD, hpE⟩
    exact (min_eq_left (hbound m p hm)).symm
  intro p hp
  have hpoint := Measure.eqOn_open_of_ae_eq he (isOpen_Ioo.prod isOpen_univ) hf
    ((continuous_fst.min continuous_snd).comp_continuousOn (hf.prodMk hB)) hp
  exact hpoint.trans_le (min_le_right _ _)

/-- The reference length controls the number of current pieces meeting a
compact set; the material comparison is evaluated at the actual point. -/
theorem n07a_actualPhysicalPieces_finite_inter_compact
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    {J : Set ℝ} (hJ : IsCompact J) (hJcore : J ⊆ Ioo D.a D.b) :
    Set.Finite {m : ℕ | ∃ z ∈ sectorNeighborhood S base ε ε,
      ∃ p ∈ physicalPieceOpen S K (liftSectorParameter S C z) m, p.1 ∈ J} := by
  obtain ⟨e, he, he1, heb⟩ := hRatio
  let d : ℕ → ℝ := fun m => (K.physicalRight m - K.physicalLeft m)⁻¹
  have hd : N07aSampleSubpower T K d := n07a_physicalLengthInverse_subpower hD hT href
  obtain ⟨A, hA, hAb⟩ := (N07aSampleSubpower.mul hD hT hd he).one_power
  have hlength (z : CanonicalGeometry.Parameter S)
      (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) (p : PolarPoint)
      (hp : p ∈ physicalPieceOpen S K (liftSectorParameter S C z) m)
      (hpJ : p.1 ∈ J) : d m ≤ A * T.M p.1 := by
    have hM : 0 < T.M p.1 := zero_lt_one.trans_le (hT.2.1 p.1 (hJcore hpJ)).2.2.2
    have hd0 : 0 < d m := inv_pos.mpr (sub_pos.mpr (h04.1.referenceBounds m).1)
    have he0 : 0 < e m := zero_lt_one.trans_le (he1 m)
    have hratio : T.M (T.sample (K.cell m)) ≤ e m * T.M p.1 :=
      (div_le_iff₀ hM).mp (heb z hz m p hp).2.2.2
    have hprod : d m * e m ≤ (A * T.M p.1) * e m := by
      calc
        _ = |d m * e m| := (abs_of_pos (mul_pos hd0 he0)).symm
        _ ≤ A * T.M (T.sample (K.cell m)) := hAb m
        _ ≤ A * (e m * T.M p.1) := mul_le_mul_of_nonneg_left hratio hA.le
        _ = _ := by ring
    exact (mul_le_mul_iff_of_pos_right he0).mp hprod
  obtain ⟨B, hB⟩ := hJ.bddAbove_image ((hT.1 T.M (by simp)).continuousOn.mono hJcore)
  let B' : ℝ := max 1 B
  have hB' : 0 < B' := zero_lt_one.trans_le (le_max_left _ _)
  have hAB : 0 < A * B' := mul_pos hA hB'
  have hfinite : volume (⋃ m, Ioo (K.physicalLeft m) (K.physicalRight m)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (show volume (Ioo D.a D.b) ≠ ∞ by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
    exact measure_mono (iUnion_subset fun m => (h04.1.referenceBounds m).2.2)
  have hlarge := Measure.finite_const_le_meas_of_disjoint_iUnion volume
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hAB))
    (fun _ : ℕ => measurableSet_Ioo) (n07a_physicalPieces_pairwise_disjoint h04) hfinite
  apply hlarge.subset
  rintro m ⟨z, hz, p, hp, hpJ⟩
  have hMp : T.M p.1 ≤ B' := (hB ⟨p.1, hpJ, rfl⟩).trans (le_max_right _ _)
  have hlen : 0 < K.physicalRight m - K.physicalLeft m :=
    sub_pos.mpr (h04.1.referenceBounds m).1
  have hbound : (A * B')⁻¹ ≤ K.physicalRight m - K.physicalLeft m :=
    (inv_le_comm₀ hlen hAB).mp ((hlength z hz m p hp hpJ).trans
      (mul_le_mul_of_nonneg_left hMp hA.le))
  simpa only [Set.mem_ofPred_eq, Real.volume_Ioo] using ENNReal.ofReal_le_ofReal hbound

end ContinuousFlexibility.Analysis
