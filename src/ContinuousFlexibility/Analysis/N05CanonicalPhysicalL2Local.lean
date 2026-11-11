import ContinuousFlexibility.Analysis.N05CanonicalPhysicalCoefficient
import ContinuousFlexibility.Radial.ReferenceGraphNorms

/-!
# Local physical endpoint L² control from a canonical height representative

The actual chart transfers measurability as well as null sets. Combining
its genuine change-of-variables formula with the proved coefficient bound
gives a uniform square-integral estimate on every physical piece.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- Composition with the actual chart preserves the measurable class on
the half-period rectangles. Global measurability of the totalized chart is
not required. -/
theorem n05_canonicalChart_aestronglyMeasurable_comp
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (hangle : ∀ p ∈ physicalPieceOpen S K m, (K.chart z m p).2 = p.2)
    {g : PolarPoint → ℝ} (hg : AEStronglyMeasurable g (canonicalMeasure S K m)) :
    AEStronglyMeasurable (fun p => g (K.chart z m p))
      (volume.restrict
        (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)) := by
  have hpullAE : (fun p => g (K.chart z m p))
      =ᵐ[volume.restrict
        (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)]
          (fun p => hg.mk g (K.chart z m p)) :=
    (n05_canonicalChart_ae_iff h04 hz hs m hangle
      (fun p => g p = hg.mk g p)).mp hg.ae_eq_mk
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  have hc := (hcharts z hz hs m).2.2.2.2.1.continuousOn
  have hmap : AEMeasurable (K.chart z m)
      (volume.restrict
        (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)) :=
    (hc.mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).aemeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc)
  exact (hg.measurable_mk.comp_aemeasurable hmap).aestronglyMeasurable.congr
    (Filter.EventuallyEq.symm hpullAE)

/-- The constant is selected before the piece, its L² representative, and
the physical field. All coefficient and Jacobian estimates are derived from
the actual N04 and material data. -/
theorem n05_canonicalHeight_endpoint_piece_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γ : ℝ} (hγ : 0 < γ) (t : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (u : CanonicalL2 S K m) (f : PolarPoint → ℝ),
      ((fun p => n05CanonicalSampleWeight T S K γ t m * u p)
        =ᵐ[canonicalMeasure S K m] canonicalHeight S K (C.referenceState, 0) m f) →
      MemLp (fun p => Real.sqrt ((D.w p.1)⁻¹) * f p) 2
        (volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)) ∧
      (∫ p, (Real.sqrt ((D.w p.1)⁻¹) * f p) ^ 2
        ∂volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)) ≤
        B * ‖u‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ :=
    n05_referenceCanonicalHeight_physical_weight_bound hD hT h hcoordinates hγ t
  refine ⟨B, hB, fun m u f hrep => ?_⟩
  have h01 := h.1.1.1
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hs : stateSector S C.referenceState :=
    n05_referenceState_sector h01.2.2.1
  have hangle : ∀ p ∈ physicalPieceOpen S K m,
      (K.chart (C.referenceState, 0) m p).2 = p.2 :=
    fun _ hp => n05_controlledReference_chart_second hcoordinates m hp
  have hpull := (n05_canonicalChart_ae_iff h.2.2.2.2 hz hs m hangle
    (fun p => n05CanonicalSampleWeight T S K γ t m * u p =
      canonicalHeight S K (C.referenceState, 0) m f p)).mp hrep
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, hpieces, _, _, _, hcharts, _⟩
  obtain ⟨_, _, hleft, _, _, _, hheight, hnonzero⟩ :=
    hcharts (C.referenceState, 0) hz hs m
  let μ : Measure PolarPoint := volume.restrict
    (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)
  have hreconstruct : f =ᵐ[μ] (fun p => K.height (C.referenceState, 0) m p *
      n05CanonicalSampleWeight T S K γ t m * u (K.chart (C.referenceState, 0) m p)) := by
    filter_upwards [hpull,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
    have hpo : p ∈ physicalPieceOpen S K m := ⟨hpm.1, mem_univ _⟩
    simp only [canonicalHeight, hleft p hpo] at hp
    calc
      f p = (n05CanonicalSampleWeight T S K γ t m *
          u (K.chart (C.referenceState, 0) m p)) * K.height (C.referenceState, 0) m p :=
        (div_eq_iff (hnonzero p hpo).1.ne').mp hp.symm
      _ = _ := by ring
  have hucomp := n05_canonicalChart_aestronglyMeasurable_comp h.2.2.2.2 hz hs m hangle
    (Lp.memLp u).aestronglyMeasurable
  have hh : AEStronglyMeasurable (K.height (C.referenceState, 0) m) μ :=
    (hheight.continuousOn.mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc)
  have hf : AEStronglyMeasurable f μ :=
    ((hh.mul_const (n05CanonicalSampleWeight T S K γ t m)).mul hucomp).congr
      hreconstruct.symm
  have hw : Measurable (fun p : PolarPoint => Real.sqrt ((D.w p.1)⁻¹)) :=
    (hD.choose_spec.1.2.2.1.1.continuous.measurable.comp measurable_fst).inv.sqrt
  have hweighted : AEStronglyMeasurable
      (fun p : PolarPoint => Real.sqrt ((D.w p.1)⁻¹) * f p) μ :=
    hw.aestronglyMeasurable.mul hf
  have hmajor : Integrable (fun p =>
      |planeJacobian (K.chart (C.referenceState, 0) m) p| *
        u (K.chart (C.referenceState, 0) m p) ^ 2) μ :=
    (n05_canonicalChart_integrable_iff h.2.2.2.2 hz hs m hangle
      (fun p => u p ^ 2)).mp (Lp.memLp u).integrable_sq
  have hdom : ∀ᵐ p ∂μ, (Real.sqrt ((D.w p.1)⁻¹) * f p) ^ 2 ≤
      B * (|planeJacobian (K.chart (C.referenceState, 0) m) p| *
        u (K.chart (C.referenceState, 0) m p) ^ 2) := by
    filter_upwards [hreconstruct,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
    have hpo : p ∈ physicalPieceOpen S K m := ⟨hpm.1, mem_univ _⟩
    have hwpos : 0 < D.w p.1 :=
      hD.choose_spec.1.2.2.2.2.1 p.1 ((hpieces m).2.2 hpm.1)
    calc
      _ = ((D.w p.1)⁻¹ * K.height (C.referenceState, 0) m p ^ 2 *
          (n05CanonicalSampleWeight T S K γ t m) ^ 2) *
            u (K.chart (C.referenceState, 0) m p) ^ 2 := by
        rw [hp, mul_pow, Real.sq_sqrt (inv_nonneg.mpr hwpos.le)]
        ring
      _ ≤ (B * |planeJacobian (K.chart (C.referenceState, 0) m) p|) *
          u (K.chart (C.referenceState, 0) m p) ^ 2 :=
        mul_le_mul_of_nonneg_right (hb m p hpo) (sq_nonneg _)
      _ = _ := by ring
  have hint : Integrable (fun p => (Real.sqrt ((D.w p.1)⁻¹) * f p) ^ 2) μ := by
    apply (hmajor.const_mul B).mono' (hweighted.pow 2)
    filter_upwards [hdom] with p hp
    change ‖(Real.sqrt ((D.w p.1)⁻¹) * f p) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.sqrt ((D.w p.1)⁻¹) * f p))]
    exact hp
  refine ⟨(memLp_two_iff_integrable_sq hweighted).mpr hint, ?_⟩
  have hnorm : (∫ p, u p ^ 2 ∂canonicalMeasure S K m) = ‖u‖ ^ 2 := by
    simpa only [Lp.toLp_coeFn] using
      (ContinuousFlexibility.Radial.reference_memLp_norm_sq_eq_integral (Lp.memLp u)).symm
  calc
    _ ≤ ∫ p, B * (|planeJacobian (K.chart (C.referenceState, 0) m) p| *
        u (K.chart (C.referenceState, 0) m p) ^ 2) ∂μ :=
      integral_mono_ae hint (hmajor.const_mul B) hdom
    _ = B * ∫ p, u p ^ 2 ∂canonicalMeasure S K m := by
      rw [integral_const_mul,
        ← n05_canonicalChart_integral h.2.2.2.2 hz hs m hangle (fun p => u p ^ 2)]
    _ = B * ‖u‖ ^ 2 := by rw [hnorm]

end ContinuousFlexibility.Statements
