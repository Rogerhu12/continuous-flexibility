module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05CanonicalSourceEmbedding
public import ContinuousFlexibility.Analysis.N05CanonicalEvenDensity

/-!
# A single actual source block retains its endpoint exponent

The source is the genuine local lift, extended by zero in the radial variable.
The estimate keeps its endpoint exponential. Only the fixed coordinate and
cell-index errors enter the coefficient power; no endpoint gap is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology BigOperators

def n05CanonicalSourceBlock (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) : PolarPoint → ℝ := by
  classical
  exact fun p => if p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
    then n05CanonicalSourcePieceLift S C K m u p else 0

theorem n05CanonicalSourceBlock_periodic (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    (u : CanonicalL2 S K m) :
    Function.Periodic (n05CanonicalSourceBlock S C K m u) (0, Real.pi) := by
  classical
  intro p
  simp only [n05CanonicalSourceBlock, Prod.fst_add, add_zero]
  split_ifs
  · exact n05CanonicalSourcePieceLift_periodic S C K m u p
  · rfl

theorem n05CanonicalSourceBlock_even (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    (u : CanonicalL2 S K m) (r θ : ℝ) :
    n05CanonicalSourceBlock S C K m u (r, -θ) =
      n05CanonicalSourceBlock S C K m u (r, θ) := by
  classical
  simp only [n05CanonicalSourceBlock]
  split_ifs
  · exact n05CanonicalSourcePieceLift_even S C K m u r θ
  · rfl

/-- The constants precede both the piece and its arbitrary L² input.
Reflection averaging is part of the fixed lift and is a contraction. -/
theorem n05_canonicalSourceBlock_reference_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε γ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hγ : 0 ≤ γ) (M : ℝ) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ m (u : CanonicalL2 S K m),
      SourceDerivativeMember D γ M (n05CanonicalSourceBlock S C K m u) ∧
      sourceNormSquare D γ M (n05CanonicalSourceBlock S C K m u, 0) ≤
        C0 * radialE (D.cellIndex (K.cell m)) ^ A *
          Real.exp (2 * γ * radialS (D.cellIndex (K.cell m))) * ‖u‖ ^ 2 := by
  classical
  obtain ⟨Bc, Ac, hBc, hAc, hc⟩ :=
    n05_referenceCanonicalHeight_density_piece_bound h hcoordinates
  obtain ⟨window, hwindow, hindex⟩ := n05_referencePiece_cell_swindow hT hcoordinates
  obtain ⟨Bw, Aw, hBw, hAw, hw⟩ :=
    n05_referenceSourceWeight_swindow hwindow.le hγ M
  refine ⟨(2 * Real.pi)⁻¹ * (2 * (Bc * Bw)), Ac + Aw, by positivity,
    add_pos_of_pos_of_nonneg hAc hAw, fun m u => ?_⟩
  let e := n05CanonicalEvenProjection S K m u
  let f := n05CanonicalSourceBlock S C K m u
  let E := radialE (D.cellIndex (K.cell m))
  let W := Bw * E ^ Aw * Real.exp (2 * γ * radialS (D.cellIndex (K.cell m)))
  let B := (Bc * Bw) * E ^ (Ac + Aw) *
    Real.exp (2 * γ * radialS (D.cellIndex (K.cell m)))
  let P := referencePhysicalPieceOpen S K m
  let μ : Measure PolarPoint := volume.restrict
    (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)
  have hE : 0 < E := Real.exp_pos _
  have hW : 0 < W := by dsimp only [W]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  have hangle : ∀ p ∈ P, (K.chart (C.referenceState, 0) m p).2 = p.2 :=
    fun _ hp => n05_controlledReference_chart_second hcoordinates m hp
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hcharts := n05_reference_charts h04
  obtain ⟨_, _, _, _, hchart, _, hheight, _⟩ := hcharts hz hs m
  have he := (n05CanonicalEvenPeriodicRepresentative_ae_average S K m u).trans
    (n05CanonicalEvenProjection_ae S K m u).symm
  have hep := (n05_referenceCanonicalChart_ae_iff h.2.2.2.2.1 hz hs m hangle
    (fun p => n05CanonicalEvenPeriodicRepresentative S K m u p = e p)).mp he
  have hrep : f =ᵐ[μ] (fun p =>
      (|planeJacobian (K.chart (C.referenceState, 0) m) p| /
        K.height (C.referenceState, 0) m p) * e (K.chart (C.referenceState, 0) m p)) := by
    filter_upwards [hep, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
    have hpo : p ∈ referencePhysicalPieceOpen S K m := ⟨hpm.1, mem_univ _⟩
    simp only [f, n05CanonicalSourceBlock, if_pos hpm.1]
    rw [n05CanonicalSourcePieceLift_eq_actual h hcoordinates m u hpo, hp]
    ring
  have hh : AEStronglyMeasurable (K.height (C.referenceState, 0) m) μ :=
    (hheight.continuousOn.mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc)
  have hjcont : ContinuousOn (planeJacobian (K.chart (C.referenceState, 0) m))
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
    intro p hp
    exact (contDiffAt_planeJacobian (hchart.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp.1, mem_univ _⟩))).continuousAt.continuousWithinAt
  have hj : AEStronglyMeasurable
      (fun p => |planeJacobian (K.chart (C.referenceState, 0) m) p|) μ :=
    hjcont.abs.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioc)
  have hecomp := n05_referenceCanonicalChart_aestronglyMeasurable_comp h.2.2.2.2.1 hz hs m hangle
    (Lp.memLp e).aestronglyMeasurable
  have hf : AEStronglyMeasurable f μ := ((hj.div₀ hh).mul hecomp).congr hrep.symm
  have hmajor : Integrable (fun p => |planeJacobian (K.chart (C.referenceState, 0) m) p| *
      e (K.chart (C.referenceState, 0) m p) ^ 2) μ :=
    (n05_referenceCanonicalChart_integrable_iff h.2.2.2.2.1 hz hs m hangle _).mp (Lp.memLp e).integrable_sq
  have hfiniteWeight (q : Finset ℕ) {p : PolarPoint} (hp : p ∈ P) :
      n05ReferenceFiniteSourceWeight D γ M q p.1 ≤ W := by
    calc
      _ ≤ ∑ j ∈ q, W * D.localizer j p.1 ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : D.localizer j p.1 = 0
        · simp only [hj, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
        · exact mul_le_mul_of_nonneg_right
            (hw (D.cellIndex j) (D.cellIndex (K.cell m))
              (hindex m j p.1 hp.1 (hD.choose_spec.2.1.2.2.1 j hj))) (sq_nonneg _)
      _ = W * ∑ j ∈ q, D.localizer j p.1 ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ W * 1 := mul_le_mul_of_nonneg_left
        (Radial.profile_localizer_sq_sum_le_one hD.choose_spec.2.1 q p.1) hW.le
      _ = W := mul_one _
  have hfinite (q : Finset ℕ) :
      MemLp (fun p => Real.sqrt (n05ReferenceFiniteSourceWeight D γ M q p.1) * f p) 2
        (radialPhysicalMeasure D) ∧
      (∫ p, (Real.sqrt (n05ReferenceFiniteSourceWeight D γ M q p.1) * f p) ^ 2
        ∂radialPhysicalMeasure D) ≤ 2 * B * ‖u‖ ^ 2 := by
    let g : PolarPoint → ℝ := fun p => Real.sqrt (n05ReferenceFiniteSourceWeight D γ M q p.1) * f p
    have hg : AEStronglyMeasurable g μ :=
      (((n05ReferenceFiniteSourceWeight_continuous hD.choose_spec.2.1 γ M q).sqrt.comp
        continuous_fst).aestronglyMeasurable).mul hf
    have hdom : ∀ᵐ p ∂μ, g p ^ 2 ≤ B *
        (|planeJacobian (K.chart (C.referenceState, 0) m) p| *
          e (K.chart (C.referenceState, 0) m p) ^ 2) := by
      filter_upwards [hrep, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
      have hpo : p ∈ P := ⟨hpm.1, mem_univ _⟩
      have hcoeff := mul_le_mul (hfiniteWeight q hpo) (hc m p hpo)
        (mul_nonneg (abs_nonneg _) (sq_nonneg _)) hW.le
      have hproduct : W * (Bc * E ^ Ac) = B := by
        dsimp only [W, B]
        rw [Real.rpow_add hE]
        ring
      rw [hproduct] at hcoeff
      have hmul := mul_le_mul_of_nonneg_right hcoeff
        (mul_nonneg (abs_nonneg (planeJacobian (K.chart (C.referenceState, 0) m) p))
          (sq_nonneg (e (K.chart (C.referenceState, 0) m p))))
      dsimp only [g]
      rw [hp, mul_pow, Real.sq_sqrt (n05ReferenceFiniteSourceWeight_nonneg D γ M q p.1)]
      convert hmul using 1 <;> simp only [div_eq_mul_inv] <;> ring
    have hi : Integrable (fun p => g p ^ 2) μ := by
      apply (hmajor.const_mul B).mono' (hg.pow 2)
      filter_upwards [hdom] with p hp
      change ‖g p ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g p))]
      exact hp
    have hhalf : MemLp g 2 μ := (memLp_two_iff_integrable_sq hg).mpr hi
    have hI : (∫ p, g p ^ 2 ∂μ) ≤ B * ‖u‖ ^ 2 := by
      have heNorm : (∫ p, e p ^ 2 ∂canonicalMeasure S K m) = ‖e‖ ^ 2 := by
        simpa only [Lp.toLp_coeFn] using
          (Radial.reference_memLp_norm_sq_eq_integral (Lp.memLp e)).symm
      calc
        _ ≤ ∫ p, B * (|planeJacobian (K.chart (C.referenceState, 0) m) p| *
            e (K.chart (C.referenceState, 0) m p) ^ 2) ∂μ :=
          integral_mono_ae hi (hmajor.const_mul B) hdom
        _ = B * ‖e‖ ^ 2 := by
          have hchange : (∫ p, e p ^ 2 ∂canonicalMeasure S K m) =
              ∫ p, |planeJacobian (K.chart (C.referenceState, 0) m) p| *
                e (K.chart (C.referenceState, 0) m p) ^ 2 ∂μ :=
            n05_referenceCanonicalChart_integral h.2.2.2.2.1 hz hs m hangle (fun p => e p ^ 2)
          rw [integral_const_mul, ← hchange, heNorm]
        _ ≤ B * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (n05CanonicalEvenProjection_bound S K m u) 2) hB.le
    have hperiodic : Function.Periodic g (0, Real.pi) := by
      intro p
      have heq : f (p + (0, Real.pi)) = f p := n05CanonicalSourceBlock_periodic S C K m u p
      have hfst : (p + (0, Real.pi)).1 = p.1 := add_zero _
      change Real.sqrt (n05ReferenceFiniteSourceWeight D γ M q (p + (0, Real.pi)).1) *
        f (p + (0, Real.pi)) = Real.sqrt (n05ReferenceFiniteSourceWeight D γ M q p.1) * f p
      rw [hfst, heq]
    have hfull := n05_piPeriodic_memLp_fullPeriod measurableSet_Ioo hperiodic hhalf
    have hP : MeasurableSet P := measurableSet_Ioo.prod MeasurableSet.univ
    have hrestrict : (radialPhysicalMeasure D).restrict P = volume.restrict
        (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) := by
      rw [radialPhysicalMeasure, Measure.restrict_restrict hP]
      congr 1
      ext p
      constructor
      · rintro ⟨hp, hcore, hθ⟩
        exact ⟨hp.1, hθ⟩
      · rintro ⟨hr, hθ⟩
        exact ⟨⟨hr, mem_univ _⟩, (hpieces m).2.2 hr, hθ⟩
    have hzero (p : PolarPoint) (hp : p ∉ P) : g p = 0 := by
      have hr : p.1 ∉ Ioo (K.physicalLeft m) (K.physicalRight m) :=
        fun hr => hp ⟨hr, mem_univ _⟩
      simp only [g, f, n05CanonicalSourceBlock, if_neg hr, mul_zero]
    have hind : P.indicator g = g := by
      funext p
      by_cases hp : p ∈ P
      · exact indicator_of_mem hp g
      · rw [indicator_of_notMem hp, hzero p hp]
    have hglobal : MemLp g 2 (radialPhysicalMeasure D) := by
      rw [← hind, memLp_indicator_iff_restrict hP, hrestrict]
      exact hfull
    refine ⟨hglobal, ?_⟩
    calc
      _ = ∫ p, g p ^ 2 ∂(radialPhysicalMeasure D).restrict P :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun p hp => by
            change g p ^ 2 = 0
            rw [hzero p hp]
            norm_num)).symm
      _ = 2 * ∫ p, g p ^ 2 ∂μ := by
        rw [hrestrict, n05_piPeriodic_integral_sq_fullPeriod measurableSet_Ioo hperiodic hhalf]
      _ ≤ _ := by nlinarith only [hI]
  have hcell := n05_radialCellIntegrable_of_finiteSourceWeights hD.choose_spec.2.1 γ M
    (fun q => (hfinite q).1)
  have hab := hD.choose_spec.1.2.1.le
  have hsum (q : Finset ℕ) : (∑ j ∈ q, sourceCellSquare D γ M f j) ≤
      ((2 * Real.pi)⁻¹ * (2 * B)) * ‖u‖ ^ 2 := by
    rw [n05_finiteSourceNormSquare_eq hab γ M hcell q]
    exact (mul_le_mul_of_nonneg_left (hfinite q).2 (by positivity)).trans_eq (by ring)
  refine ⟨⟨hcell, summable_of_sum_le (sourceCellSquare_nonneg hab γ M hcell) hsum⟩, ?_⟩
  have hb := Real.tsum_le_of_sum_le (sourceCellSquare_nonneg hab γ M hcell) hsum
  change 0 ^ 2 + (∑' j, sourceCellSquare D γ M f j) ≤ _
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, B, E, mul_assoc] using hb

end ContinuousFlexibility.Statements
