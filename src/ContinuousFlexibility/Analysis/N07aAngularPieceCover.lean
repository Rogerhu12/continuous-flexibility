module

public import ContinuousFlexibility.Statements.N07aCanonicalGeometry
public import ContinuousFlexibility.Analysis.SpacesTraceRestriction
public import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
public import ContinuousFlexibility.Analysis.SpacesCylinderIntegration
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Compactness.LocallyFinite

/-!
# The actual physical canonical pieces are locally finite

The a.e. uniqueness clause makes their open intervals pairwise disjoint.
The primitive zeroth-order geometry bounds then prevent arbitrarily
short pieces from meeting a compact subinterval of the annulus. This
uses the material envelope and the actual ratio of sample and point
weights; it needs no properness or multiplicity assumption on `K.cell`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis CanonicalGeometry
open scoped ENNReal Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- A.e. uniqueness of an open interval cover is actual pairwise disjointness. -/
theorem n07a_physicalPieces_pairwise_disjoint
    (h04 : N04Properties D T S C L K base loss ε) :
    Pairwise (fun m n => Disjoint
      (Ioo (K.physicalLeft m) (K.physicalRight m))
      (Ioo (K.physicalLeft n) (K.physicalRight n))) := by
  obtain ⟨E, hE, hcover⟩ := h04.1.referencePartition
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro r hrm hrn
  have hsub : Ioo (K.physicalLeft m) (K.physicalRight m) ∩
      Ioo (K.physicalLeft n) (K.physicalRight n) ⊆ E := by
    intro x hx
    by_contra hxE
    obtain ⟨k, _, hk⟩ := hcover x ⟨(h04.1.referenceBounds m).2.2 hx.1, hxE⟩
    exact hmn ((hk m hx.1).trans (hk n hx.2).symm)
  have hzero := measure_mono_null hsub hE
  exact (isOpen_Ioo.inter isOpen_Ioo).measure_ne_zero volume ⟨r, hrm, hrn⟩ hzero

/-- The elementary cancellation behind the compactness estimate. -/
private theorem n07a_inverseLength_of_materialRatio
    {d e Ms Mx B A : ℝ} (he : 0 < e) (hMx : 0 < Mx)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hlen : d⁻¹ ≤ B * e) (hratio : Ms / Mx ≤ B * e)
    (henvelope : e * e ≤ A * Ms) :
    d⁻¹ ≤ (A * B ^ 2) * Mx := by
  have hMs : Ms ≤ B * e * Mx := (div_le_iff₀ hMx).mp hratio
  have hsq : e * e ≤ e * (A * B * Mx) := by
    calc
      e * e ≤ A * Ms := henvelope
      _ ≤ A * (B * e * Mx) := mul_le_mul_of_nonneg_left hMs hA
      _ = e * (A * B * Mx) := by ring
  have heupper : e ≤ A * B * Mx := (mul_le_mul_iff_of_pos_left he).mp hsq
  calc
    d⁻¹ ≤ B * e := hlen
    _ ≤ B * (A * B * Mx) := mul_le_mul_of_nonneg_left heupper hB
    _ = (A * B ^ 2) * Mx := by ring

/-- Primitive reference jets give a pointwise lower bound for the actual
physical piece length, expressed using the material weight at that point. -/
theorem n07a_physicalPiece_inverseLength_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : ReferenceJets D T S C L K) :
    ∃ A : ℝ, 0 < A ∧ ∀ m x, x ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
      (K.physicalRight m - K.physicalLeft m)⁻¹ ≤ A * T.M x := by
  obtain ⟨B, hB, hbound⟩ := hjets.2 0
  obtain ⟨A, hA, henvelope⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.1 (B + B)
  refine ⟨A * B ^ 2, mul_pos hA (sq_pos_of_pos hB), ?_⟩
  intro m x hx
  have hlen : 0 < K.physicalRight m - K.physicalLeft m :=
    sub_pos.mpr (h04.1.referenceBounds m).1
  have hxcore := (h04.1.referenceBounds m).2.2 hx
  have hM : 0 < T.M x := zero_lt_one.trans_le (hT.2.1 x hxcore).2.2.2
  have hsample := spaces_trace_sample_mem hD hT (K.cell m)
  have hE : 0 < T.E0 (T.sample (K.cell m)) := (hT.2.1 _ hsample).2.2.1
  have hMs : 0 < T.M (T.sample (K.cell m)) :=
    zero_lt_one.trans_le (hT.2.1 _ hsample).2.2.2
  let p : PolarPoint := ((x - K.physicalLeft m) /
    (K.physicalRight m - K.physicalLeft m), 0)
  have hp : p ∈ unitStrip := by
    refine ⟨⟨div_pos (sub_pos.mpr hx.1) hlen, ?_⟩, mem_univ _⟩
    exact (div_lt_one hlen).mpr (sub_lt_sub_right hx.2 _)
  have hpoint : physicalUnitPoint K m p = (x, 0) := by
    dsimp only [physicalUnitPoint, p]
    congr 1
    field_simp [ne_of_gt hlen]
    ring
  have hl := hbound m .physicalLengthInverse p hp 0 0 (by omega)
  have hr := hbound m .ratioMInverse p hp 0 0 (by omega)
  have hl' : (K.physicalRight m - K.physicalLeft m)⁻¹ ≤
      B * T.E0 (T.sample (K.cell m)) ^ B := by
    simpa only [spaces_mixedDerivative_zero, atom, abs_of_pos (inv_pos.mpr hlen)] using hl
  have hr' : T.M (T.sample (K.cell m)) / T.M x ≤
      B * T.E0 (T.sample (K.cell m)) ^ B := by
    simpa only [spaces_mixedDerivative_zero, atom, hpoint,
      abs_of_pos (div_pos hMs hM)] using hr
  have he' : T.E0 (T.sample (K.cell m)) ^ B * T.E0 (T.sample (K.cell m)) ^ B ≤
      A * T.M (T.sample (K.cell m)) := by
    rw [← Real.rpow_add hE]
    exact henvelope _ hsample
  exact n07a_inverseLength_of_materialRatio (Real.rpow_pos_of_pos hE B)
    hM hB.le hA.le hl' hr' he'

/-- Every compact subset of the open annulus meets only finitely many
actual physical canonical pieces. -/
theorem n07a_physicalPieces_finite_inter_compact
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : ReferenceJets D T S C L K)
    {J : Set ℝ} (hJ : IsCompact J) (hJcore : J ⊆ Ioo D.a D.b) :
    Set.Finite {m : ℕ | (J ∩ Ioo (K.physicalLeft m) (K.physicalRight m)).Nonempty} := by
  obtain ⟨A, hA, hlen⟩ := n07a_physicalPiece_inverseLength_bound hD hT h04 hjets
  have hM : ContinuousOn T.M J :=
    (hT.1 T.M (by simp)).continuousOn.mono hJcore
  obtain ⟨B, hB⟩ := hJ.bddAbove_image hM
  let B' : ℝ := max 1 B
  have hB' : 0 < B' := zero_lt_one.trans_le (le_max_left _ _)
  have hAB : 0 < A * B' := mul_pos hA hB'
  have hfinite : volume (⋃ m, Ioo (K.physicalLeft m) (K.physicalRight m)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (show volume (Ioo D.a D.b) ≠ ∞ by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
    exact measure_mono (iUnion_subset fun m => (h04.1.referenceBounds m).2.2)
  have hfiniteLarge := Measure.finite_const_le_meas_of_disjoint_iUnion volume
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hAB))
    (fun _ : ℕ => measurableSet_Ioo) (n07a_physicalPieces_pairwise_disjoint h04) hfinite
  apply hfiniteLarge.subset
  rintro m ⟨x, hxJ, hxm⟩
  have hMx : T.M x ≤ B' := (hB ⟨x, hxJ, rfl⟩).trans (le_max_right _ _)
  have hd : 0 < K.physicalRight m - K.physicalLeft m :=
    sub_pos.mpr (h04.1.referenceBounds m).1
  have hbound : (A * B')⁻¹ ≤ K.physicalRight m - K.physicalLeft m :=
    (inv_le_comm₀ hd hAB).mp ((hlen m x hxm).trans
      (mul_le_mul_of_nonneg_left hMx hA.le))
  simpa only [Set.mem_ofPred_eq, Real.volume_Ioo] using ENNReal.ofReal_le_ofReal hbound

/-- The same finiteness includes pieces touching the compact set only at
an endpoint. The larger interior compact interval removes that distinction. -/
theorem n07a_physicalClosedPieces_finite_inter_compact
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : ReferenceJets D T S C L K)
    {J : Set ℝ} (hJ : IsCompact J) (hJcore : J ⊆ Ioo D.a D.b) :
    Set.Finite {m : ℕ | (J ∩ Icc (K.physicalLeft m) (K.physicalRight m)).Nonempty} := by
  have hab : D.a < D.b := by
    obtain ⟨x, hx⟩ := Set.nonempty_Ioo.mpr (h04.1.referenceBounds 0).1
    exact ((h04.1.referenceBounds 0).2.2 hx).1.trans ((h04.1.referenceBounds 0).2.2 hx).2
  obtain ⟨l, r, hal, hlr, hrb, hJlr⟩ :=
    exists_inner_interval_of_isCompact_subset_Ioo hab hJ hJcore
  have hcore : Icc l r ⊆ Ioo D.a D.b :=
    fun _ hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩
  apply (n07a_physicalPieces_finite_inter_compact hD hT h04 hjets
    isCompact_Icc hcore).subset
  rintro m ⟨x, hxJ, hxm⟩
  have hxcl : x ∈ closure (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
    rw [closure_Ioo (ne_of_lt (h04.1.referenceBounds m).1)]
    exact hxm
  obtain ⟨y, hylr, hym⟩ := mem_closure_iff.mp hxcl (Ioo l r) isOpen_Ioo (hJlr hxJ)
  exact ⟨y, Ioo_subset_Icc_self hylr, hym⟩

end ContinuousFlexibility.Statements
