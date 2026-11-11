import ContinuousFlexibility.Radial.ReferenceNaturalKernel

/-!
# The second-mode inverse identifies the actual homogeneous profile

The radial Hilbert density is bounded on the finite closed annulus, so
physical radial L² coefficients are genuine modal Hilbert vectors. A
zero ordinary source and unit border datum then identify the modal
solution with the given homogeneous field by the actual inverse's
uniqueness clause.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem memLp_radialHilbertMeasure_of_memLp_core {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (radialCore D))) :
    MemLp u 2 (radialHilbertMeasure D) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (matchingDensity_continuousOn hD)
  have hm : radialHilbertMeasure D ≤
      ENNReal.ofReal C • volume.restrict (radialCore D) := by
    change (volume.restrict (radialCore D)).withDensity
      (fun r => ENNReal.ofReal (matchingDensity D r)) ≤ _
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hC r (Ioo_subset_Icc_self hr))
  exact hu.of_measure_le_smul ENNReal.ofReal_ne_top hm

/-- The whole modal graph, including its scalar sign convention, has only
the normalized homogeneous solution at datum (0,1). -/
theorem modeFullGraph_two_zeroSource_eq_phi {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hphi : ∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0)
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D 2 G) {U : RadialModePair D}
    (hU : ModeFullGraph D 2 U (0, 1)) :
    (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] D.phi ∧ U.2 = 0 := by
  have hflat : EndpointFlat D D.phi := (matchingProfileGeometry hD).2.2.2.1
  have hLp : MemLp D.phi 2 (radialHilbertMeasure D) :=
    endpointFlat_memLp_radialHilbert hD hflat
  have hnull : NaturalRadialNull D 2 D.phi := by
    apply naturalRadialNull_of_smooth hD 2 hflat.1 hLp
    intro r hr
    simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hphi r hr
  let V : RadialModeL2 D := hLp.toLp D.phi
  have hV : (V : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] D.phi := hLp.coeFn_toLp
  have hgraph : ModeFullGraph D 2 (V, 0) (0, 1) := by
    refine ⟨modeLocalEquation_of_naturalRadialNull hD hnull V hV 1, ?_⟩
    change (∫ r in D.a..D.b, referenceColumn D r * V r) = 1
    calc
      _ = ∫ r in D.a..D.b, referenceColumn D r * D.phi r := by
        apply matchingInterval_congr_ae hD
        filter_upwards [hV] with r hr
        rw [hr]
      _ = 1 := hborder.2.2.2.1
  have heq : U = (V, 0) := (hG.2 U (0, 1) hU).symm.trans (hG.2 (V, 0) (0, 1) hgraph)
  rw [heq]
  exact ⟨hV, rfl⟩

end ContinuousFlexibility.Radial
