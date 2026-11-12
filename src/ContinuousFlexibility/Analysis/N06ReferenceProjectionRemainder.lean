import ContinuousFlexibility.Analysis.N06ReferenceProjectionRepresentatives
import ContinuousFlexibility.Analysis.N06ReferenceRemainderTraces

/-!
# Physical projection retains the original left-height coordinate

The reference graph's physical height is in the original full-period L2
space. Its projection commutes almost everywhere with subtraction of any
radial field, so the actual S.chiLeft is retained without identifying it
with the reference data's cutoff. Genuine reference chart pullback then
identifies the projected canonical height with the projected physical
height minus that same left scalar column.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped BigOperators Topology

/-- Subtracting an arbitrary radial field changes just the retained mean
mode. Only the original L2 angular slices are used in the proof. -/
theorem n06_referenceBasisProjection_sub_radial_ae
    {D : ReferenceData} {η : PolarPoint → ℝ}
    (hη : MemLp η 2 (radialPhysicalMeasure D))
    (a : ℝ → ℝ) {I : Finset ℕ} (h0 : 0 ∈ I) :
    referenceBasisProjection I (fun p => η p - a p.1)
      =ᵐ[radialPhysicalMeasure D]
        (fun p => referenceBasisProjection I η p - a p.1) := by
  have hco : ∀ᵐ r ∂volume.restrict (radialCore D), ∀ n : ℕ,
      evenFourierCoefficient (fun p => η p - a p.1) n r =
        evenFourierCoefficient η n r - if n = 0 then a r else 0 :=
    ae_all_iff.mpr (n06_evenFourierCoefficient_sub_radial_ae hη a)
  rw [radialPhysicalMeasure_eq_prod]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hco] with p hp
  have hproj (f : PolarPoint → ℝ) : referenceBasisProjection I f p =
      ∑ n ∈ I, evenFourierCoefficient f n p.1 * referenceAngularBasis n p.2 := by
    apply Finset.sum_congr rfl
    intro n _
    exact congrArg (· * referenceAngularBasis n p.2)
      (n06_referenceAngularCoefficient_eq_evenFourier f n p.1)
  rw [hproj, hproj]
  simp_rw [hp, sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp only [ite_true, referenceAngularBasis, mul_one]
  · intro n _ hn
    simp only [ite_eq_right hn, zero_mul]
  · exact fun hn => (hn h0).elim

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- Equality in the original physical measure passes to the actual
reference height coordinates on each original canonical piece. -/
theorem n06_controlledReferenceHeight_congr_ae_physical
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[radialPhysicalMeasure D] g) (m : ℕ) :
    canonicalHeight S K (C.referenceState, 0) m f
      =ᵐ[canonicalMeasure S K m] canonicalHeight S K (C.referenceState, 0) m g := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hc := h04.1.charts (C.referenceState, 0) href hs m
  have hhalf : f =ᵐ[volume.restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)] g := by
    apply ae_restrict_of_ae_restrict_of_subset _ hfg
    intro p hp
    exact ⟨(h04.1.referenceBounds m).2.2 hp.1, hp.2.1,
      hp.2.2.trans (by linarith [Real.pi_pos])⟩
  have hangle : ∀ p ∈ physicalPieceOpen S K (C.referenceState, 0) m,
      (K.chart (C.referenceState, 0) m p).2 = p.2 := by
    intro p hp
    apply n05_controlledReference_chart_second hcoordinates m
    simpa only [h04.1.referenceDomain m] using hp
  apply (n05_canonicalChart_ae_iff h04 href hs m hangle
    (fun p => canonicalHeight S K (C.referenceState, 0) m f p =
      canonicalHeight S K (C.referenceState, 0) m g p)).mpr
  simp only [h04.1.referenceDomain m, referencePhysicalPieceOpen,
    prod_inter_prod, inter_univ, univ_inter]
  filter_upwards [hhalf,
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp hpU
  have hpo : p ∈ physicalPieceOpen S K (C.referenceState, 0) m := by
    rw [h04.1.referenceDomain m]
    exact ⟨hpU.1, mem_univ _⟩
  simp only [canonicalHeight, hc.2.2.1 p hpo, hp]

/-- The projected L2 remainder represents the projected physical height
with its original left scalar and its actual space cutoff unchanged. -/
theorem n06_controlledReferenceRemainder_fourierCut_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) (U : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ))
    {η : PolarPoint → ℝ} (hη : MemLp η 2 (radialPhysicalMeasure D))
    (hηp : Function.Periodic η (0, Real.pi)) (aL : ℝ)
    (hrep : (U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m
        (fun p => η p - aL * S.chiLeft p.1)) (N : ℕ) :
    (n06CanonicalFourierCutL2 N U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m
        (fun p => referenceBasisProjection (Finset.range (N + 1)) η p -
          aL * S.chiLeft p.1) := by
  have hperiod : Function.Periodic (fun p : PolarPoint => η p - aL * S.chiLeft p.1)
      (0, Real.pi) := by
    intro p
    simp only [hηp p, Prod.fst_add, add_zero]
  have hcut := n06_controlledReferenceHeight_fourierCut_ae
    h hcoordinates m U he hperiod hrep N
  have hphysical := n06_referenceBasisProjection_sub_radial_ae hη
    (fun r => aL * S.chiLeft r)
    (I := Finset.range (N + 1)) (Finset.mem_range.mpr (Nat.zero_lt_succ N))
  exact hcut.trans (n06_controlledReferenceHeight_congr_ae_physical h hcoordinates hphysical m)

end ContinuousFlexibility.Statements
