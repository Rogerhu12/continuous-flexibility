import ContinuousFlexibility.Analysis.SmoothCompactL2Density
import ContinuousFlexibility.Radial.ReferenceSmoothSources
import ContinuousFlexibility.Radial.ReferenceWeightedMeasure

/-!
# Local finiteness of the reference weighted measure

Although the source weight can have infinite mass at the endpoints, its
restriction to every compact radial subset of the open core is finite.
The proof uses the actual compact local finiteness of the cell family.
The radial measure used below is the marginal of the existing weighted
physical measure, so no alternate weighted-space representation is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements
open ContinuousFlexibility.Analysis

theorem referenceWeightedCellMeasure_isFinite {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) (m : ℕ) :
    IsFiniteMeasure (referenceWeightedCellMeasure D γ M m) := by
  have hf : RadialCellIntegrable D (fun _ => (1 : ℝ)) :=
    radialCellIntegrable_of_continuous hD continuous_const
  have hi := integrable_sq_referenceWeightedCellMeasure hD γ M m hf
  have hi' : Integrable (fun _ : PolarPoint => (1 : ℝ))
      (referenceWeightedCellMeasure D γ M m) := by
    simpa only [one_pow] using hi
  exact (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp hi'

/-- A slab over a compact radial subset of the core meets only finitely
many localized measures, each of finite total mass. -/
theorem referenceWeightedMeasure_radialCompact_lt_top {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (γ M : ℝ) {K : Set ℝ}
    (hK : IsCompact K) (hcore : K ⊆ radialCore D) :
    referenceWeightedMeasure D γ M (Prod.fst ⁻¹' K) < ⊤ := by
  classical
  obtain ⟨C, hC⟩ := hD
  have hpart : RadialPartition D := hC.2.1
  have hfinite : Set.Finite {m | (D.cells m ∩ K).Nonempty} :=
    hC.2.2.2.2.2.1 K hK hcore
  have hslab : MeasurableSet (Prod.fst ⁻¹' K : Set PolarPoint) :=
    measurable_fst hK.measurableSet
  have hz (m : ℕ) (hm : m ∉ hfinite.toFinset) :
      referenceWeightedCellMeasure D γ M m (Prod.fst ⁻¹' K) = 0 := by
    have hm' : ¬(D.cells m ∩ K).Nonempty := by
      intro hmeet
      apply hm
      rw [Set.Finite.mem_toFinset]
      change (D.cells m ∩ K).Nonempty
      exact hmeet
    rw [referenceWeightedCellMeasure, withDensity_apply _ hslab]
    calc
      (∫⁻ x in Prod.fst ⁻¹' K,
          referenceCellMeasureDensity D γ M m x ∂radialPhysicalMeasure D) =
          ∫⁻ _x in Prod.fst ⁻¹' K, (0 : ℝ≥0∞) ∂radialPhysicalMeasure D := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hslab] with x hx
        have hlocal : D.localizer m x.1 = 0 := by
          by_contra h
          exact hm' ⟨x.1, hpart.2.2.1 m (Function.mem_support.mpr h), hx⟩
        simp only [referenceCellMeasureDensity, hlocal, zero_pow (by decide : (2 : ℕ) ≠ 0),
          mul_zero, ENNReal.ofReal_zero]
      _ = 0 := by simp
  rw [referenceWeightedMeasure, Measure.sum_apply _ hslab, tsum_eq_sum hz]
  apply ENNReal.sum_lt_top.mpr
  intro m _
  letI := referenceWeightedCellMeasure_isFinite hpart γ M m
  exact measure_lt_top _ _

theorem referenceWeightedMeasure_compact_lt_top {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (γ M : ℝ) {K : Set PolarPoint}
    (hK : IsCompact K) (hcore : K ⊆ radialCore D ×ˢ (univ : Set ℝ)) :
    referenceWeightedMeasure D γ M K < ⊤ := by
  have hK' : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hcore' : Prod.fst '' K ⊆ radialCore D := by
    rintro r ⟨x, hx, rfl⟩
    exact (hcore hx).1
  exact (measure_mono (subset_preimage_image Prod.fst K)).trans_lt
    (referenceWeightedMeasure_radialCompact_lt_top hD γ M hK' hcore')

theorem referenceWeightedMeasure_ae_core {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) :
    ∀ᵐ x ∂referenceWeightedMeasure D γ M, x.1 ∈ radialCore D := by
  apply (referenceWeightedMeasure_ae_iff hD γ M).mpr
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioo.prod measurableSet_Ioc :
      MeasurableSet (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)))] with x hx
  exact hx.1

/-- The actual radial marginal of the reference weighted measure. -/
def referenceRadialWeightedMeasure (D : ReferenceData) (γ M : ℝ) : Measure ℝ :=
  (referenceWeightedMeasure D γ M).map Prod.fst

theorem referenceRadialWeightedMeasure_ae_core {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) :
    ∀ᵐ r ∂referenceRadialWeightedMeasure D γ M, r ∈ radialCore D := by
  exact (ae_map_iff measurable_fst.aemeasurable measurableSet_Ioo).mpr
    (referenceWeightedMeasure_ae_core hD γ M)

theorem referenceRadialWeightedMeasure_compact_lt_top {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (γ M : ℝ) {K : Set ℝ}
    (hK : IsCompact K) (hcore : K ⊆ radialCore D) :
    referenceRadialWeightedMeasure D γ M K < ⊤ := by
  rw [referenceRadialWeightedMeasure, Measure.map_apply measurable_fst hK.measurableSet]
  exact referenceWeightedMeasure_radialCompact_lt_top hD γ M hK hcore

/-- Radial L² coefficients can be approximated by smooth functions whose
compact support lies strictly in the core. -/
theorem exists_referenceRadial_smooth_approximation {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ radialCore D ∧
      ∃ hg : MemLp g 2 (referenceRadialWeightedMeasure D γ M),
        ‖hg.toLp g - hf.toLp f‖ < ε := by
  have hpart : RadialPartition D := by obtain ⟨C, hC⟩ := hD; exact hC.2.1
  exact Analysis.MemLp.exists_contDiff_compact_approximation hf isOpen_Ioo
    (referenceRadialWeightedMeasure_ae_core hpart γ M)
    (fun K hK hcore => referenceRadialWeightedMeasure_compact_lt_top hD γ M hK hcore) hε

theorem memLp_referenceRadial_lift {D : ReferenceData} {γ M : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M)) :
    MemLp (fun x : PolarPoint => f x.1) 2 (referenceWeightedMeasure D γ M) :=
  hf.comp_of_map measurable_fst.aemeasurable

theorem norm_referenceRadial_lift {D : ReferenceData} {γ M : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M)) :
    ‖(memLp_referenceRadial_lift hf).toLp (fun x : PolarPoint => f x.1)‖ =
      ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  exact (eLpNorm_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).symm

end ContinuousFlexibility.Radial
