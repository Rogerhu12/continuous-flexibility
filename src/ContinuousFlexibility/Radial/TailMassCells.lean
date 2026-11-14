module

public import ContinuousFlexibility.Radial.TailMassResistanceData
public import ContinuousFlexibility.Radial.TailMassAverages
public import ContinuousFlexibility.Radial.TailTestPairing

/-!
# The actual weighted mass cells

The scalar interval masses in the deep-tail hypotheses are the measures of
the corresponding open mass cells for `deepTailMeasure`. Thus their
normalized averages form a bounded map on the actual weighted `L²` space.
The offset parameter allows the first Dirichlet cell to be omitted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff lp ENNReal InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements

def tailMassCell (T : DeepTailData) (n : ℕ) : Set ℝ :=
  Ioo (T.node n) (T.massEnd n)

theorem tailMassCell_measurable (T : DeepTailData) (n : ℕ) :
    MeasurableSet (tailMassCell T n) :=
  measurableSet_Ioo

theorem tailMassCell_subset {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    tailMassCell T n ⊆ Ioo T.entrance T.endpoint := by
  intro x hx
  exact ⟨(deepTail_entrance_le_node hT n).trans_lt hx.1,
    hx.2.trans (deepTail_massEnd_lt_endpoint hT n)⟩

/-- Restricting the weighted measure to a measurable subset of the tail
gives the same density against ordinary Lebesgue measure on that subset. -/
theorem tail_setIntegral_density {T : DeepTailData} (hT : DeepTailHypotheses T)
    {s : Set ℝ} (hs : MeasurableSet s) (hsub : s ⊆ Ioo T.entrance T.endpoint)
    (f : ℝ → ℝ) :
    (∫ x in s, f x ∂deepTailMeasure T) = ∫ x in s, T.p x * f x := by
  have hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint) :=
    (deepTail_contDiffOn hT).mono (fun _ hx => ⟨hx.1.le, hx.2⟩)
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (T.p x)) (volume.restrict s) :=
    ((hp.continuousOn.mono hsub).aemeasurable hs).ennreal_ofReal
  rw [deepTailMeasure, restrict_withDensity hs,
    Measure.restrict_restrict_of_subset hsub,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  have hx' := hsub hx
  simp only [ENNReal.toReal_ofReal (deepTail_pos hT x ⟨hx'.1.le, hx'.2⟩).le,
    smul_eq_mul]

theorem tail_interval_measure {T : DeepTailData} (hT : DeepTailHypotheses T)
    {a b : ℝ} (ha : T.entrance ≤ a) (hab : a ≤ b) (hb : b < T.endpoint) :
    deepTailMeasure T (Ioo a b) = ENNReal.ofReal (∫ x in a..b, T.p x) := by
  have hsub : Ioo a b ⊆ Ioo T.entrance T.endpoint :=
    fun _ hx => ⟨ha.trans_lt hx.1, hx.2.trans hb⟩
  have hc : ContinuousOn T.p (Icc a b) :=
    (deepTail_contDiffOn hT).continuousOn.mono (deepTail_Icc_subset hT ha hb)
  have hi : IntegrableOn T.p (Ioo a b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
      (hc.intervalIntegrable_of_Icc hab)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo a b)] T.p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (deepTail_pos hT x ⟨ha.trans hx.1.le, hx.2.trans hb⟩).le
  rw [deepTailMeasure, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict_of_subset hsub,
    ← ofReal_integral_eq_lintegral_ofReal hi hnonneg,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem tailMassCell_measure {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    deepTailMeasure T (tailMassCell T n) = ENNReal.ofReal (tailMass T n) :=
  tail_interval_measure hT (deepTail_entrance_le_node hT n)
    (deepTail_node_lt_massEnd hT n).le (deepTail_massEnd_lt_endpoint hT n)

theorem tailMassCell_measure_ne_top {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    deepTailMeasure T (tailMassCell T n) ≠ (⊤ : ℝ≥0∞) := by
  rw [tailMassCell_measure hT n]
  exact ENNReal.ofReal_ne_top

theorem tailMassCell_real {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    (deepTailMeasure T).real (tailMassCell T n) = tailMass T n := by
  rw [measureReal_def, tailMassCell_measure hT n,
    ENNReal.toReal_ofReal (tailMass_pos hT n).le]

theorem tailMassCell_real_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    0 < (deepTailMeasure T).real (tailMassCell T n) := by
  rw [tailMassCell_real hT n]
  exact tailMass_pos hT n

theorem tailMassCell_pairwiseDisjoint {T : DeepTailData} (hT : DeepTailHypotheses T) :
    Pairwise (fun n m => Disjoint (tailMassCell T n) (tailMassCell T m)) := by
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hnm | hmn
  · have hsep : T.massEnd n < T.node m :=
      (deepTail_massEnd_lt_succ_node hT n).trans_le
        ((deepTail_node_strictMono hT).monotone (Nat.succ_le_of_lt hnm))
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact lt_asymm (hx.2.trans hsep) hy.1
  · have hsep : T.massEnd m < T.node n :=
      (deepTail_massEnd_lt_succ_node hT m).trans_le
        ((deepTail_node_strictMono hT).monotone (Nat.succ_le_of_lt hmn))
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact lt_asymm (hy.2.trans hsep) hx.1

theorem tailMassCell_offset_pairwiseDisjoint {T : DeepTailData}
    (hT : DeepTailHypotheses T) (offset : ℕ) :
    Pairwise (fun n m => Disjoint (tailMassCell T (offset + n))
      (tailMassCell T (offset + m))) := by
  intro n m hnm
  exact tailMassCell_pairwiseDisjoint hT (fun h => hnm (Nat.add_left_cancel h))

/-- Actual normalized weighted averages on the mass cells from `offset`
onwards. The index of its `n`th coordinate is `offset + n`. -/
def tailMassCellAnalysis {T : DeepTailData} (hT : DeepTailHypotheses T) (offset : ℕ) :
    DeepTailL2 T →L[ℝ] ℓ²(ℕ, ℝ) :=
  tailMassAnalysis (fun n => tailMassCell T (offset + n))
    (fun n => tailMassCell_measurable T (offset + n))
    (fun n => tailMassCell_measure_ne_top hT (offset + n))
    (fun n => tailMassCell_real_pos hT (offset + n))
    (tailMassCell_offset_pairwiseDisjoint hT offset)

theorem tailMassCellAnalysis_apply {T : DeepTailData} (hT : DeepTailHypotheses T)
    (offset : ℕ) (u : DeepTailL2 T) (n : ℕ) :
    tailMassCellAnalysis hT offset u n =
      (Real.sqrt (tailMass T (offset + n)))⁻¹ *
        ∫ x in tailMassCell T (offset + n), u x ∂deepTailMeasure T := by
  rw [tailMassCellAnalysis, tailMassAnalysis_apply, tailMassCell_real hT]

theorem tailMassCellAnalysis_apply_density {T : DeepTailData} (hT : DeepTailHypotheses T)
    (offset : ℕ) (u : DeepTailL2 T) (n : ℕ) :
    tailMassCellAnalysis hT offset u n =
      (Real.sqrt (tailMass T (offset + n)))⁻¹ *
        ∫ x in tailMassCell T (offset + n), T.p x * u x := by
  rw [tailMassCellAnalysis_apply,
    tail_setIntegral_density hT (tailMassCell_measurable T _) (tailMassCell_subset hT _)]

theorem norm_tailMassCellAnalysis_le {T : DeepTailData} (hT : DeepTailHypotheses T)
    (offset : ℕ) : ‖tailMassCellAnalysis hT offset‖ ≤ 1 :=
  norm_tailMassAnalysis_le _ _ _ _ _

end ContinuousFlexibility.Radial
