import ContinuousFlexibility.Analysis.N06ReferenceModeTransport
import ContinuousFlexibility.Analysis.N06ReferenceRemainderTraces

/-!
# The actual canonical modes pull back to the physical reference modes

Null sets in the radial canonical variable are transported by the genuine
reference chart. The original physical L2 field supplies angular
integrability almost everywhere. Consequently a canonical modal
representative, composed with the actual radial chart and multiplied by
its actual height, represents the same physical Fourier mode.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private instance : SFinite angleMeasure := by unfold angleMeasure; infer_instance

private instance : NeZero angleMeasure := ⟨by
  intro h
  have he := congrArg (fun μ : Measure ℝ => μ univ) h
  simp only [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero] at he
  exact (ENNReal.ofReal_pos.mpr Real.pi_pos).ne' he⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- A radial almost-everywhere predicate follows through the original
reference chart, without assuming a pointwise mode identity. -/
theorem n06_controlledReference_radial_ae_pullback
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) {P : ℝ → Prop}
    (hP : ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)), P y) :
    ∀ᵐ r ∂volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m)),
      P ((K.chart (C.referenceState, 0) m (r, 0)).1) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hp : ∀ᵐ p ∂canonicalMeasure S K m, P p.1 := by
    rw [n06_canonicalMeasure_eq_radial_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hP
  have hx := (n05_canonicalChart_ae_iff h04 href hs m
    (fun p hp => n05_controlledReference_chart_second hcoordinates m hp)
    (fun p => P p.1)).mp hp
  have hprod : (volume : Measure PolarPoint).restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) =
      (volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m))).prod angleMeasure := by
    exact (Measure.prod_restrict _ _).symm
  rw [hprod] at hx
  filter_upwards [Measure.ae_ae_of_ae_prod hx, ae_restrict_mem measurableSet_Ioo] with r hr hrI
  obtain ⟨θ, hθ⟩ := hr.exists
  have he := (hcoordinates.1 m (r, θ) ⟨hrI, mem_univ _⟩).1
  simpa only [he] using hθ

/-- The actual physical L2 field supplies the half-period integrability
needed to identify canonical modes with full-period reference modes. -/
theorem n06_physical_halfMode_integrable_ae
    {η : PolarPoint → ℝ} (hη : MemLp η 2 (radialPhysicalMeasure D)) (n : ℕ) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      IntervalIntegrable (fun θ => η (r, θ) * referenceAngularBasis n θ)
        volume 0 Real.pi := by
  have hb : MemLp (referenceAngularBasis n) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    angularInterval_memLp_of_continuous (contDiff_referenceAngularBasis n).continuous
  filter_upwards [r11b_physical_memLp_angular_sections hη] with r hr
  have hi : IntervalIntegrable (fun θ => η (r, θ) * referenceAngularBasis n θ)
      volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
      (hr.integrable_mul hb)
  apply hi.mono_set
  rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])

/-- A representative of the original canonical half-cosine mode gives
the actual physical full-period mode after the genuine height change. -/
theorem n06_controlledReference_modal_representation
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {η W : PolarPoint → ℝ} (hη : MemLp η 2 (radialPhysicalMeasure D))
    (hperiod : Function.Periodic η (0, Real.pi)) (m n : ℕ) {v : ℝ → ℝ}
    (hrep : W =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m η)
    (hmode : n06HalfCosineCoefficient W n
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v) :
    evenFourierCoefficient η n =ᵐ[volume.restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m))]
      (fun r => K.height (C.referenceState, 0) m (r, 0) *
        v ((K.chart (C.referenceState, 0) m (r, 0)).1)) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hcoef := (n06_canonical_halfCosineCoefficient_congr_ae hrep n).symm.trans hmode
  have hpull := n06_controlledReference_radial_ae_pullback h hcoordinates m hcoef
  have hsub : Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ radialCore D :=
    (h04.2.2.2.1 m).2.2
  have hi := ae_restrict_of_ae_restrict_of_subset hsub (n06_physical_halfMode_integrable_ae hη n)
  filter_upwards [hpull, hi, ae_restrict_mem measurableSet_Ioo] with r hr hir hrI
  have hper : Function.Periodic (fun θ => η (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hperiod (r, θ)
  have he := n06_controlledReferenceHeight_mode h hcoordinates η m n hrI hper hir
  have hH : 0 < K.height (C.referenceState, 0) m (r, 0) :=
    ((h04.2.2.2.2.2.2.2.1 _ href hs m).2.2.2.2.2.2.2 (r, 0) ⟨hrI, mem_univ _⟩).1
  have hv : evenFourierCoefficient η n r / K.height (C.referenceState, 0) m (r, 0) =
      v ((K.chart (C.referenceState, 0) m (r, 0)).1) := he.symm.trans hr
  exact (div_eq_iff hH.ne').mp hv |>.trans (mul_comm _ _)

end ContinuousFlexibility.Statements
