import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Continuous bounds extend through the null complement of the actual reference pieces. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements

theorem n04_referencePieces_le_on_annularOpen
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {f g : PolarPoint → ℝ}
    (hf : ContinuousOn f (annularOpen D)) (hg : ContinuousOn g (annularOpen D))
    (hpieces : ∀ m p, p ∈ referencePhysicalPieceOpen S K m → f p ≤ g p) :
    ∀ p ∈ annularOpen D, f p ≤ g p := by
  obtain ⟨E, hE, hcover⟩ := hgeom.partition (C.referenceState, 0) href hsector
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have havoid : ∀ᵐ p ∂(volume : Measure PolarPoint), p ∉ E :=
    measure_eq_zero_iff_ae_notMem.mp hE
  have hAE : (fun p => min (f p) (g p))
      =ᵐ[(volume : Measure PolarPoint).restrict (annularOpen D)] f := by
    filter_upwards [ae_restrict_of_ae havoid, ae_restrict_mem hU.measurableSet]
      with p hpE hpU
    obtain ⟨m, hm, _⟩ := hcover p ⟨hpU, hpE⟩
    have hmref : p ∈ referencePhysicalPieceOpen S K m := by
      rw [← hgeom.referenceDomain m]
      exact hm
    exact min_eq_left (hpieces m p hmref)
  have hmin : ContinuousOn (fun p => min (f p) (g p)) (annularOpen D) :=
    fun p hp => Filter.Tendsto.min (hf p hp) (hg p hp)
  have heq : EqOn (fun p => min (f p) (g p)) f (annularOpen D) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq
      (μ := (volume : Measure PolarPoint)) hAE hU hmin hf
  intro p hp
  exact (heq p hp).symm.trans_le (min_le_right _ _)

end ContinuousFlexibility.Analysis
