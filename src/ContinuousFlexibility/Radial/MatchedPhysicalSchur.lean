import ContinuousFlexibility.Radial.MatchedPhysicalSchurRows

/-!
# Actual weighted boundedness of the modal inverse from its raw blocks

The operator in the conclusion is the given continuous linear map.
The assumptions concern norms of its actual local blocks and the one
scalar border. Weighted L² membership of its output is proved.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ENNReal
open ContinuousFlexibility.Statements

theorem matchedPhysicalOutputCell_norm_sq {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (k : ℕ) (U : RadialModePair D) :
    ‖matchedPhysicalOutputCell D hD hP k U‖ ^ 2 =
      ∫ r, (D.localizer k r * U.1 r) ^ 2 ∂volume.restrict (radialCore D) := by
  rw [matchedL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [matchedPhysicalCellField_ae hD hP k U] with r hr
  exact congrArg (fun z : ℝ => z ^ 2) hr

theorem matchedPhysicalOutputCell_localized_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (k : ℕ) (U : RadialModePair D) :
    MemLp (fun r => D.localizer k r * U.1 r) 2
      (volume.restrict (radialCore D)) :=
  (Lp.memLp (matchedPhysicalOutputCell D hD hP k U)).congr
    (matchedPhysicalCellField_ae hD hP k U)

theorem matchedPhysicalOutputSequence_energy {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (γ M : ℝ) (U : RadialModePair D)
    (hs : Summable (fun k => matchedPhysicalOutputSequence D hD hP γ M U k ^ 2)) :
    MemLp (U.1 : ℝ → ℝ) 2 (referenceRadialWeightedMeasure D γ M) ∧
      (∑' k, matchedPhysicalOutputSequence D hD hP γ M U k ^ 2) =
        U.2 ^ 2 + ∫ r, U.1 r ^ 2 ∂referenceRadialWeightedMeasure D γ M := by
  have he (k : ℕ) :
      matchedPhysicalOutputSequence D hD hP γ M U (k + 1) ^ 2 =
        matchedRadialCellSquare D γ M U.1 k := by
    change (matchedRadialWeight D γ M k * ‖matchedPhysicalOutputCell D hD hP k U‖) ^ 2 = _
    rw [mul_pow, matchedPhysicalOutputCell_norm_sq hD hP]
    rfl
  have htail := (summable_nat_add_iff 1).mpr hs
  have hcell : Summable (matchedRadialCellSquare D γ M U.1) :=
    htail.congr he
  have hm := (Lp.aestronglyMeasurable U.1).mono_ac
    (matchedModeLebesgue_absolutelyContinuous hD)
  have hf := matchedRadial_memLp_of_cellSquare_summable hP hm
    (fun k => matchedPhysicalOutputCell_localized_memLp hD hP k U) hcell
  refine ⟨hf, ?_⟩
  rw [hs.tsum_eq_zero_add, matchedRadialWeighted_integral_sq hP hf]
  change ‖U.2‖ ^ 2 +
    (∑' k, matchedPhysicalOutputSequence D hD hP γ M U (k + 1) ^ 2) = _
  rw [Real.norm_eq_abs, sq_abs]
  exact congrArg (fun z : ℝ => U.2 ^ 2 + z) (tsum_congr he)

/-- The exact product of the row sum, column sum and partition costs. -/
theorem matchedPhysicalSchur_weighted_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (f : MatchedPhysicalL2 D) (u : RadialModeL2 D) (t : ℝ)
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => -f r / matchingDensity D r)
    {A B T γ M₀ Mout : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 1 ≤ T)
    (hpart : ∀ r ∈ radialCore D, (matchedPartitionSquare D r)⁻¹ ≤ T)
    (hf : MemLp (f : ℝ → ℝ) 2 (referenceRadialWeightedMeasure D γ M₀))
    (K : ℕ → ℕ → ℝ) (hK : ∀ k m, 0 ≤ K k m)
    (hrow : ∀ k, Summable (K k) ∧ ∑' m, K k m ≤ A)
    (hcol : ∀ m, Summable (fun k => K k m) ∧ ∑' k, K k m ≤ B)
    (hmajor : ∀ k m,
      matchedPhysicalChannelWeight D γ Mout k * matchedPhysicalRawKernel D hD hP G k m ≤
        K k m * matchedPhysicalChannelWeight D γ M₀ m) :
    MemLp ((G (u, t)).1 : ℝ → ℝ) 2 (referenceRadialWeightedMeasure D γ Mout) ∧
      ((∫ r, (G (u, t)).1 r ^ 2 ∂referenceRadialWeightedMeasure D γ Mout) +
        (G (u, t)).2 ^ 2) ≤
      (A * B * T ^ 2) *
        ((∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M₀) + t ^ 2) := by
  obtain ⟨hxs, hxb⟩ := matchedPhysicalSourceSequence_sq hP hT hpart f t hf
  have hbound := matchedPhysical_outputSequence_bound hD hP G f u t hu γ M₀ Mout K
    hK (fun k => (hrow k).1) hxs hmajor
  obtain ⟨hys, hyb⟩ := real_schur_square_bound K hA hB hK hrow hcol
    (matchedPhysicalSourceSequence D hP γ M₀ f t)
    (matchedPhysicalOutputSequence D hD hP γ Mout (G (u, t)))
    (matchedPhysicalSourceSequence_nonneg D hP γ M₀ f t)
    (matchedPhysicalOutputSequence_nonneg D hD hP γ Mout (G (u, t))) hxs hbound
  obtain ⟨hmem, he⟩ := matchedPhysicalOutputSequence_energy hD hP γ Mout (G (u, t)) hys
  refine ⟨hmem, ?_⟩
  have hb := hyb.trans (mul_le_mul_of_nonneg_left hxb (mul_nonneg hA hB))
  rw [he] at hb
  nlinarith

/-- A common constant precedes the operator, both weights, the kernel,
and the source. Thus one set of raw row and column bounds works for
all three attenuation exponents of R11a with the same operator. -/
theorem exists_matchedPhysicalSchur_uniform_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : RadialModePair D →L[ℝ] RadialModePair D) (γ M₀ Mout : ℝ)
        (K : ℕ → ℕ → ℝ),
      0 ≤ γ → 0 ≤ M₀ →
      (∀ k m, 0 ≤ K k m) →
      (∀ k, Summable (K k) ∧ ∑' m, K k m ≤ A) →
      (∀ m, Summable (fun k => K k m) ∧ ∑' k, K k m ≤ B) →
      (∀ k m,
        matchedPhysicalChannelWeight D γ Mout k * matchedPhysicalRawKernel D hD hP G k m ≤
          K k m * matchedPhysicalChannelWeight D γ M₀ m) →
      ∀ (f : ℝ → ℝ) (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M₀))
        (F : RadialModePair D),
      ((F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        fun r => -f r / matchingDensity D r) →
      MemLp ((G F).1 : ℝ → ℝ) 2 (referenceRadialWeightedMeasure D γ Mout) ∧
        ((∫ r, (G F).1 r ^ 2 ∂referenceRadialWeightedMeasure D γ Mout) + (G F).2 ^ 2) ≤
          C ^ 2 * ((∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M₀) + F.2 ^ 2) := by
  obtain ⟨T₀, _, hT₀⟩ := exists_matchedPartitionSquare_inv_bound hP
  let T := max T₀ 1
  have hT : 1 ≤ T := le_max_right _ _
  have hpart : ∀ r ∈ radialCore D, (matchedPartitionSquare D r)⁻¹ ≤ T :=
    fun r hr => (hT₀ r hr).trans (le_max_left _ _)
  let C := T * (A + B + 1)
  have hC : 0 < C := mul_pos (zero_lt_one.trans_le hT) (by linarith)
  have hcoeff : A * B * T ^ 2 ≤ C ^ 2 := by
    have hh : A * B ≤ (A + B + 1) ^ 2 := by
      nlinarith [mul_nonneg hA hB, sq_nonneg A, sq_nonneg B]
    calc
      A * B * T ^ 2 ≤ (A + B + 1) ^ 2 * T ^ 2 :=
        mul_le_mul_of_nonneg_right hh (sq_nonneg T)
      _ = C ^ 2 := by dsimp only [C]; ring
  refine ⟨C, hC, ?_⟩
  intro G γ M₀ Mout K hγ hM₀ hK hrow hcol hmajor f hf F hF
  have hp := matchedPhysical_memLp_of_weighted hP hγ hM₀ hf
  let fp : MatchedPhysicalL2 D := hp.toLp f
  have hfp : (fp : ℝ → ℝ) =ᵐ[volume.restrict (radialCore D)] f := hp.coeFn_toLp
  have hfpW : (fp : ℝ → ℝ) =ᵐ[referenceRadialWeightedMeasure D γ M₀] f :=
    (matchedRadialWeighted_ae_iff hP γ M₀).mpr hfp
  have hfpμ : (fp : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] f :=
    (radialHilbertMeasure_ae_iff hD).mpr hfp
  have hinput : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => -fp r / matchingDensity D r := by
    filter_upwards [hF, hfpμ] with r hr hfr
    rw [hr, hfr]
  obtain ⟨hmem, hb⟩ := matchedPhysicalSchur_weighted_bound hD hP G fp F.1 F.2 hinput
    hA hB hT hpart (hf.congr hfpW.symm) K hK hrow hcol hmajor
  have hI : (∫ r, fp r ^ 2 ∂referenceRadialWeightedMeasure D γ M₀) =
      ∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M₀ := by
    apply integral_congr_ae
    exact hfpW.mono (fun _ hr => congrArg (fun z : ℝ => z ^ 2) hr)
  rw [hI] at hb
  refine ⟨hmem, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hcoeff
    (add_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg F.2))

end ContinuousFlexibility.Radial
