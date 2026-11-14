module

public import ContinuousFlexibility.Analysis.N07aActualMaterialComparison
public import ContinuousFlexibility.Analysis.N07aAngularPieceCover
public import ContinuousFlexibility.Analysis.N07aPhysicalPieceBound

/-!
# Compact support and continuous bounds on the moving pieces

The planar almost-everywhere partition gives pointwise inequalities by
continuity. Compact radial supports meet only finitely many current
pieces on the derived material-ratio neighborhood. The counting measure
uses the disjoint reference intervals; it does not identify them with the
current domains.
-/

@[expose] public section

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

private theorem n07a_actualPieceCover_with_exists {α : Type*} {Condition : α → Prop}
    {P : Prop} (h : ∃ a, Condition a) (hP : ∀ a, Condition a → P) : P := by
  obtain ⟨a, ha⟩ := h
  exact hP a ha

private theorem n07a_actualPieceCover_inverseLength
    {d e Ms Mx A : ℝ} (hd : 0 < d) (he : 0 < e) (hMx : 0 < Mx)
    (hA : 0 ≤ A) (hratio : Ms / Mx ≤ e) (henvelope : |d * e| ≤ A * Ms) :
    d ≤ A * Mx := by
  have hMs : Ms ≤ e * Mx := (div_le_iff₀ hMx).mp hratio
  have hprod : d * e ≤ (A * Mx) * e := by
    calc
      _ = |d * e| := (abs_of_pos (mul_pos hd he)).symm
      _ ≤ A * Ms := henvelope
      _ ≤ A * (e * Mx) := mul_le_mul_of_nonneg_left hMs hA
      _ = _ := by ring
  exact (mul_le_mul_iff_of_pos_right he).mp hprod

private theorem n07a_actualPieceCover_count
    {left right : ℕ → ℝ} {a b : ℝ} {M : ℝ → ℝ} {J : Set ℝ}
    (hJ : IsCompact J) (hM : ContinuousOn M J)
    (hinterval : ∀ m, left m < right m)
    (hsub : ∀ m, Ioo (left m) (right m) ⊆ Ioo a b)
    (hdisjoint : Pairwise (fun m n => Disjoint
      (Ioo (left m) (right m)) (Ioo (left n) (right n))))
    {A : ℝ} (hA : 0 < A) {P : ℕ → Prop}
    (hlength : ∀ m, P m → ∃ x ∈ J, (right m - left m)⁻¹ ≤ A * M x) :
    Set.Finite {m : ℕ | P m} := by
  obtain ⟨B, hB⟩ := hJ.bddAbove_image hM
  let B' : ℝ := max 1 B
  have hB' : 0 < B' := zero_lt_one.trans_le (le_max_left _ _)
  have hAB : 0 < A * B' := mul_pos hA hB'
  have hfinite : volume (⋃ m, Ioo (left m) (right m)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (show volume (Ioo a b) ≠ ∞ by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
    exact measure_mono (iUnion_subset hsub)
  have hlarge := Measure.finite_const_le_meas_of_disjoint_iUnion volume
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hAB))
    (fun _ : ℕ => measurableSet_Ioo) hdisjoint hfinite
  apply hlarge.subset
  intro m hm
  obtain ⟨x, hx, hlengthx⟩ := hlength m hm
  have hMp : M x ≤ B' := (hB ⟨x, hx, rfl⟩).trans (le_max_right _ _)
  have hlen : 0 < right m - left m := sub_pos.mpr (hinterval m)
  have hbound : (A * B')⁻¹ ≤ right m - left m :=
    (inv_le_comm₀ hlen hAB).mp (hlengthx.trans
      (mul_le_mul_of_nonneg_left hMp hA.le))
  simpa only [Set.mem_ofPred_eq, Real.volume_Ioo] using ENNReal.ofReal_le_ofReal hbound

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
  refine n07a_actualPieceCover_with_exists hRatio ?_
  intro e heall
  have he : N07aSampleSubpower T K e := heall.1
  have he1 : ∀ m, 1 ≤ e m := heall.2.1
  have heb := heall.2.2
  let d : ℕ → ℝ := fun m => (K.physicalRight m - K.physicalLeft m)⁻¹
  have hd : N07aSampleSubpower T K d := n07a_physicalLengthInverse_subpower hD hT href
  refine n07a_actualPieceCover_with_exists (N07aSampleSubpower.mul hD hT hd he).one_power ?_
  intro A hAall
  have hA : 0 < A := hAall.1
  have hAb := hAall.2
  apply n07a_actualPieceCover_count (left := K.physicalLeft) (right := K.physicalRight)
    (a := D.a) (b := D.b) (M := T.M) hJ
    ((hT.1 T.M (by simp)).continuousOn.mono hJcore)
    (fun m => (h04.1.referenceBounds m).1)
    (fun m => (h04.1.referenceBounds m).2.2)
    (n07a_physicalPieces_pairwise_disjoint h04) hA
  rintro m ⟨z, hz, p, hp, hpJ⟩
  refine ⟨p.1, hpJ, ?_⟩
  exact n07a_actualPieceCover_inverseLength
    (inv_pos.mpr (sub_pos.mpr (h04.1.referenceBounds m).1))
    (zero_lt_one.trans_le (he1 m))
    (zero_lt_one.trans_le (hT.2.1 p.1 (hJcore hpJ)).2.2.2)
    hA.le (heb z hz m p hp).2.2.2 (hAb m)

end ContinuousFlexibility.Analysis
