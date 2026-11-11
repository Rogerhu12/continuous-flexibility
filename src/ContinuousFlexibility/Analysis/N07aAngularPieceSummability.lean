import ContinuousFlexibility.Analysis.N07aAngularPieceCover
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Summability at the actual physical piece samples

The primitive inverse-length bound and the material envelope imply
`M(sample(cell m))⁻¹ ≤ C * physicalLength m`. The true disjoint intervals
have total length at most `b-a`. Hence the original sequence of pieces,
without any grouping by `K.cell`, has a summable inverse material weight.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis CanonicalGeometry
open scoped ENNReal

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_physicalPiece_sampleInverse_le_length
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : ReferenceJets D T S C L K) :
    ∃ A : ℝ, 0 < A ∧ ∀ m,
      (T.M (T.sample (K.cell m)))⁻¹ ≤
        A * (K.physicalRight m - K.physicalLeft m) := by
  obtain ⟨B, hB, hbound⟩ := hjets.2 0
  obtain ⟨A, hA, henvelope⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.1 B
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro m
  have hlen : 0 < K.physicalRight m - K.physicalLeft m :=
    sub_pos.mpr (h04.2.2.2.1 m).1
  have hsample := spaces_trace_sample_mem hD hT (K.cell m)
  have hM : 0 < T.M (T.sample (K.cell m)) :=
    zero_lt_one.trans_le (hT.2.1 _ hsample).2.2.2
  have hp : ((1 / 2 : ℝ), 0) ∈ unitStrip := by
    constructor
    · constructor <;> norm_num
    · exact mem_univ _
  have hraw := hbound m .physicalLengthInverse ((1 / 2 : ℝ), 0) hp 0 0 (by omega)
  have hraw' : (K.physicalRight m - K.physicalLeft m)⁻¹ ≤
      B * T.E0 (T.sample (K.cell m)) ^ B := by
    simpa only [spaces_mixedDerivative_zero, atom, abs_of_pos (inv_pos.mpr hlen)] using hraw
  apply (inv_le_iff_one_le_mul₀ hM).mpr
  calc
    1 = (K.physicalRight m - K.physicalLeft m) *
        (K.physicalRight m - K.physicalLeft m)⁻¹ := (mul_inv_cancel₀ hlen.ne').symm
    _ ≤ (K.physicalRight m - K.physicalLeft m) *
        (B * (A * T.M (T.sample (K.cell m)))) :=
      mul_le_mul_of_nonneg_left (hraw'.trans
        (mul_le_mul_of_nonneg_left (henvelope _ hsample) hB.le)) hlen.le
    _ = ((A * B) * (K.physicalRight m - K.physicalLeft m)) *
        T.M (T.sample (K.cell m)) := by ring

/-- The actual physical intervals have finite total length. -/
theorem n07a_physicalPieces_length_summable
    (h04 : N04Properties D T S C L K base loss ε) :
    Summable (fun m => K.physicalRight m - K.physicalLeft m) ∧
      (∑' m, (K.physicalRight m - K.physicalLeft m)) ≤ D.b - D.a := by
  have hlen (m : ℕ) : 0 ≤ K.physicalRight m - K.physicalLeft m :=
    (sub_pos.mpr (h04.2.2.2.1 m).1).le
  have hab : D.a < D.b := by
    obtain ⟨x, hx⟩ := Set.nonempty_Ioo.mpr (h04.2.2.2.1 0).1
    exact ((h04.2.2.2.1 0).2.2 hx).1.trans ((h04.2.2.2.1 0).2.2 hx).2
  have hsum : (∑' m, ENNReal.ofReal (K.physicalRight m - K.physicalLeft m)) ≤
      ENNReal.ofReal (D.b - D.a) := by
    have hμ : volume (⋃ m, Ioo (K.physicalLeft m) (K.physicalRight m)) ≤
        volume (Ioo D.a D.b) :=
      measure_mono (iUnion_subset fun m => (h04.2.2.2.1 m).2.2)
    rw [measure_iUnion (n07a_physicalPieces_pairwise_disjoint h04)
      (fun _ => measurableSet_Ioo)] at hμ
    simpa only [Real.volume_Ioo] using hμ
  have hfinite : (∑' m, ENNReal.ofReal (K.physicalRight m - K.physicalLeft m)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have he (m : ℕ) : (ENNReal.ofReal (K.physicalRight m - K.physicalLeft m)).toReal =
      K.physicalRight m - K.physicalLeft m := ENNReal.toReal_ofReal (hlen m)
  refine ⟨?_, ?_⟩
  · simpa only [he] using ENNReal.summable_toReal hfinite
  · have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] at hr
    simpa only [he] using hr

/-- One fixed material loss suffices to sum over every actual piece. -/
theorem n07a_physicalPiece_sampleInverse_summable
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : ReferenceJets D T S C L K) :
    ∃ A : ℝ, 0 < A ∧
      Summable (fun m => (T.M (T.sample (K.cell m)))⁻¹) ∧
      (∑' m, (T.M (T.sample (K.cell m)))⁻¹) ≤ A * (D.b - D.a) := by
  obtain ⟨A, hA, hbound⟩ := n07a_physicalPiece_sampleInverse_le_length hD hT h04 hjets
  obtain ⟨hlen, hlenbound⟩ := n07a_physicalPieces_length_summable h04
  have hnonneg (m : ℕ) : 0 ≤ (T.M (T.sample (K.cell m)))⁻¹ :=
    inv_nonneg.mpr ((zero_lt_one.trans_le
      (hT.2.1 _ (spaces_trace_sample_mem hD hT (K.cell m))).2.2.2).le)
  have hs := Summable.of_nonneg_of_le hnonneg hbound (hlen.mul_left A)
  refine ⟨A, hA, hs, ?_⟩
  calc
    (∑' m, (T.M (T.sample (K.cell m)))⁻¹) ≤
        ∑' m, A * (K.physicalRight m - K.physicalLeft m) :=
      hs.tsum_le_tsum hbound (hlen.mul_left A)
    _ = A * (∑' m, (K.physicalRight m - K.physicalLeft m)) := tsum_mul_left
    _ ≤ A * (D.b - D.a) := mul_le_mul_of_nonneg_left hlenbound hA.le

end ContinuousFlexibility.Statements
