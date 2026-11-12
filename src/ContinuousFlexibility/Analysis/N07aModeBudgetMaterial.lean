import ContinuousFlexibility.Analysis.N07aGeometryLengthBounds
import ContinuousFlexibility.Analysis.N07aCanonicalModeEnergySum

/-!
# Material envelopes for the actual weak mode budget

The complete energy expression, the affine L² normalization, and any
fixed material output weight are absorbed after they have been formed.
The positive height gain is used only once in that final step.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

theorem N07aSampleSubpower.sqrt
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {f : ℕ → ℝ} (hf : N07aSampleSubpower T K f) :
    N07aSampleSubpower T K (fun m => Real.sqrt (f m)) := by
  apply (hf.abs.add (N07aSampleSubpower.const hD hT (K := K) 1)).mono
  intro m
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by positivity : 0 ≤ |f m| + 1)]
  exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [le_abs_self (f m), sq_nonneg |f m|]⟩

theorem N07aSampleSubpower.weighted_height_absorption
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {f : ℕ → ℝ} (hf : N07aSampleSubpower T K f) {γ : ℝ} (hγ : 0 < γ) (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m,
      T.H (T.sample (K.cell m)) ^ γ * T.M (T.sample (K.cell m)) ^ t * |f m| ≤ C := by
  obtain ⟨B, hB, hb⟩ := hf.one_power
  obtain ⟨C, hC, hc, _⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.2.1 (t + 1) γ hγ
  refine ⟨B * C, mul_pos hB hC, fun m => ?_⟩
  have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  have hH := (hT.2.1 _ hm).2.1
  have hM : 0 < T.M (T.sample (K.cell m)) := zero_lt_one.trans_le (hT.2.1 _ hm).2.2.2
  calc
    _ ≤ T.H (T.sample (K.cell m)) ^ γ * T.M (T.sample (K.cell m)) ^ t *
        (B * T.M (T.sample (K.cell m))) :=
      mul_le_mul_of_nonneg_left (hb m) (by positivity)
    _ = B * (T.H (T.sample (K.cell m)) ^ γ * T.M (T.sample (K.cell m)) ^ (t + 1)) := by
      rw [Real.rpow_add hM, Real.rpow_one]
      ring
    _ ≤ B * C := mul_le_mul_of_nonneg_left (hc _ hm) hB.le

variable {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}

theorem n07a_canonicalModeNormalization_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) :
    N07aSampleSubpower T K (fun m => Real.sqrt (Real.pi * (K.right m - K.left m))) :=
  (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT Real.pi)
    (n07a_canonicalLength_subpower hD hT href)).sqrt hD hT

theorem n07a_referenceModeBudget_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) (A P Q : ℝ) :
    N07aSampleSubpower T K (fun m =>
      n07aReferenceModeBudget A P Q (K.right m - K.left m) (T.E0 (T.sample (K.cell m)))) := by
  have hconst (c : ℝ) := N07aSampleSubpower.const hD hT (K := K) c
  have hp (a : ℝ) := N07aSampleSubpower.e0_rpow hD hT (K := K) a
  have hlen := n07a_canonicalLength_subpower hD hT href
  have hinv := n07a_canonicalLengthInverse_subpower hD hT href
  have hbase := ((hconst 1).add (N07aSampleSubpower.mul hD hT (hconst A) (hp A))).add
    (N07aSampleSubpower.mul hD hT (hconst P) (hp P))
  have hfirst := N07aSampleSubpower.mul hD hT (hconst 16384)
    ((N07aSampleSubpower.mul hD hT (hconst 4) (hbase.nat_pow hD hT 5)).nat_pow hD hT 10)
  have hr := N07aSampleSubpower.mul hD hT (hlen.nat_pow hD hT 2)
    (N07aSampleSubpower.mul hD hT (hconst Q) (hp Q))
  have hsecond := N07aSampleSubpower.mul hD hT (hconst 2)
    (((hconst 1).add (hr.nat_pow hD hT 2)).add (hlen.nat_pow hD hT 4))
  have hthird := N07aSampleSubpower.mul hD hT hinv (hconst Real.pi⁻¹)
  exact N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.mul hD hT hfirst hsecond) hthird

theorem n07a_principalModeEnvelope_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) (A P Q B : ℝ) :
    N07aSampleSubpower T K (fun m =>
      112 * (1 + (K.right m - K.left m)) ^ 6 * B * T.E0 (T.sample (K.cell m)) ^ B *
        Real.sqrt (n07aReferenceModeBudget A P Q (K.right m - K.left m)
          (T.E0 (T.sample (K.cell m)))) * Real.sqrt (Real.pi * (K.right m - K.left m))) := by
  have hconst (c : ℝ) := N07aSampleSubpower.const hD hT (K := K) c
  have hlen := n07a_canonicalLength_subpower hD hT href
  have hpower := ((hconst 1).add hlen).nat_pow hD hT 6
  have hbudget := (n07a_referenceModeBudget_subpower hD hT href A P Q).sqrt hD hT
  have hnormal := n07a_canonicalModeNormalization_subpower hD hT href
  exact N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.mul hD hT
      (N07aSampleSubpower.mul hD hT
        (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.mul hD hT (hconst 112) hpower) (hconst B))
        (N07aSampleSubpower.e0_rpow hD hT B)) hbudget) hnormal

end ContinuousFlexibility.Analysis
