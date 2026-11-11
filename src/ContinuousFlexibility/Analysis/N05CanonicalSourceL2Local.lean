import ContinuousFlexibility.Analysis.N05CanonicalSourceFiniteWeight
import ContinuousFlexibility.Analysis.N05CanonicalPhysicalL2Local
import ContinuousFlexibility.Geometry.EuclideanRigidity

/-!
# Local L² bounds for the actual canonical source lift

The canonical source equality is pulled back through the real chart. Its
genuine Jacobian and height reconstruct the physical source. Finite
localized reference weights have a uniform density bound, so the actual
change of variables yields L² membership and a common square-integral
estimate before any infinite source summability is known.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem n05_canonicalSource_finite_weight_piece_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : Finset ℕ) (m : ℕ) (u : CanonicalL2 S K m)
      (f : PolarPoint → ℝ),
      ((fun p => n05CanonicalSampleWeight T S K γ t m * u p)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m f) →
      MemLp (fun p => Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) 2
        (volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)) ∧
      (∫ p, (Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) ^ 2
        ∂volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)) ≤
        B * ‖u‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ :=
    n05_referenceCanonicalSource_finite_density_bound hD hT h hcoordinates hγw hgap t M
  refine ⟨B, hB, fun q m u f hrep => ?_⟩
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
      canonicalSource S K (C.referenceState, 0) m f p)).mp hrep
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  obtain ⟨_, _, hleft, _, hchart, _, hheight, hnonzero⟩ :=
    hcharts (C.referenceState, 0) hz hs m
  let μ : Measure PolarPoint := volume.restrict
    (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)
  have hreconstruct : f =ᵐ[μ] (fun p =>
      (|planeJacobian (K.chart (C.referenceState, 0) m) p| /
        K.height (C.referenceState, 0) m p) *
        n05CanonicalSampleWeight T S K γ t m * u (K.chart (C.referenceState, 0) m p)) := by
    filter_upwards [hpull,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
    have hpo : p ∈ physicalPieceOpen S K m := ⟨hpm.1, mem_univ _⟩
    have hn := hnonzero p hpo
    simp only [canonicalSource, hleft p hpo] at hp
    calc
      f p = (K.height (C.referenceState, 0) m p * f p /
          |planeJacobian (K.chart (C.referenceState, 0) m) p|) *
          (|planeJacobian (K.chart (C.referenceState, 0) m) p| /
            K.height (C.referenceState, 0) m p) := by
        field_simp [hn.1.ne', abs_ne_zero.mpr hn.2.1] <;> ring
      _ = (n05CanonicalSampleWeight T S K γ t m * u (K.chart (C.referenceState, 0) m p)) *
          (|planeJacobian (K.chart (C.referenceState, 0) m) p| /
            K.height (C.referenceState, 0) m p) := by rw [← hp]
      _ = _ := by ring
  have hucomp := n05_canonicalChart_aestronglyMeasurable_comp h.2.2.2.2 hz hs m hangle
    (Lp.memLp u).aestronglyMeasurable
  have hh : AEStronglyMeasurable (K.height (C.referenceState, 0) m) μ :=
    (hheight.continuousOn.mono (fun _ hp => ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc)
  have hjcont : ContinuousOn (planeJacobian (K.chart (C.referenceState, 0) m))
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
    intro p hp
    exact (contDiffAt_planeJacobian
      (hchart.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨hp.1, mem_univ _⟩))).continuousAt.continuousWithinAt
  have hj : AEStronglyMeasurable
      (fun p => |planeJacobian (K.chart (C.referenceState, 0) m) p|) μ :=
    hjcont.abs.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioc)
  have hf : AEStronglyMeasurable f μ :=
    (((hj.div₀ hh).mul_const (n05CanonicalSampleWeight T S K γ t m)).mul hucomp).congr
      hreconstruct.symm
  have hw : Continuous (fun p : PolarPoint =>
      Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1)) :=
    (n05ReferenceFiniteSourceWeight_continuous hD.choose_spec.2.1 γw M q).sqrt.comp
      continuous_fst
  have hweighted : AEStronglyMeasurable
      (fun p => Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) μ :=
    hw.aestronglyMeasurable.mul hf
  have hmajor : Integrable (fun p =>
      |planeJacobian (K.chart (C.referenceState, 0) m) p| *
        u (K.chart (C.referenceState, 0) m p) ^ 2) μ :=
    (n05_canonicalChart_integrable_iff h.2.2.2.2 hz hs m hangle
      (fun p => u p ^ 2)).mp (Lp.memLp u).integrable_sq
  have hdom : ∀ᵐ p ∂μ,
      (Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) ^ 2 ≤
        B * (|planeJacobian (K.chart (C.referenceState, 0) m) p| *
          u (K.chart (C.referenceState, 0) m p) ^ 2) := by
    filter_upwards [hreconstruct,
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpm
    have hpo : p ∈ physicalPieceOpen S K m := ⟨hpm.1, mem_univ _⟩
    calc
      _ = (n05ReferenceFiniteSourceWeight D γw M q p.1 *
          (|planeJacobian (K.chart (C.referenceState, 0) m) p| /
            K.height (C.referenceState, 0) m p) ^ 2 *
          n05CanonicalSampleWeight T S K γ t m ^ 2) *
            u (K.chart (C.referenceState, 0) m p) ^ 2 := by
        rw [hp, mul_pow, Real.sq_sqrt (n05ReferenceFiniteSourceWeight_nonneg D γw M q p.1)]
        ring
      _ ≤ (B * |planeJacobian (K.chart (C.referenceState, 0) m) p|) *
          u (K.chart (C.referenceState, 0) m p) ^ 2 :=
        mul_le_mul_of_nonneg_right (hb q m p hpo) (sq_nonneg _)
      _ = _ := by ring
  have hint : Integrable
      (fun p => (Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) ^ 2) μ := by
    apply (hmajor.const_mul B).mono' (hweighted.pow 2)
    filter_upwards [hdom] with p hp
    change ‖(Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (sq_nonneg (Real.sqrt (n05ReferenceFiniteSourceWeight D γw M q p.1) * f p))]
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
