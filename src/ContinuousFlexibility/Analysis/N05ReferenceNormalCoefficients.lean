import ContinuousFlexibility.Analysis.N05PhysicalPieceRadialMultiplier
import ContinuousFlexibility.Analysis.N05CanonicalRadialTestDerivative

/-!
# The actual coefficients of the canonical first radial derivative

The leading inverse Jacobian and the logarithmic height correction are
chosen once on the genuine physical pieces. They are measurable and their
fixed coefficient bounds follow from the selected reference coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n05ReferenceNormalLeading (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) : PolarPoint → ℝ :=
  fun p => n05PhysicalPieceRadialMultiplier S K
    (fun m r => (deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)⁻¹) p.1

def n05ReferenceNormalDrift (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) : PolarPoint → ℝ :=
  fun p => n05PhysicalPieceRadialMultiplier S K
    (fun m r => deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r /
      K.height (C.referenceState, 0) m (r, 0) /
        deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r) p.1

def n05ReferenceRadialNormalField (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (u ur : PolarPoint → ℝ) : PolarPoint → ℝ :=
  fun p => n05ReferenceNormalLeading S C K p * ur p - n05ReferenceNormalDrift S C K p * u p

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include h hcoordinates in
theorem n05_referenceNormal_slices (m : ℕ) :
    ContDiffOn ℝ ∞ (fun r => K.height (C.referenceState, 0) m (r, 0))
      (Ioo (K.physicalLeft m) (K.physicalRight m)) ∧
    ContDiffOn ℝ ∞ (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1)
      (Ioo (K.physicalLeft m) (K.physicalRight m)) ∧
    (∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m),
      K.height (C.referenceState, 0) m (r, 0) ≠ 0 ∧
      deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r ≠ 0) := by
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  obtain ⟨_, _, _, _, hc, _, hh, hn⟩ := hcharts (C.referenceState, 0) hz hs m
  have hline : ContDiff ℝ ∞ (fun r : ℝ => (r, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hmap : MapsTo (fun r : ℝ => (r, (0 : ℝ)))
      (Ioo (K.physicalLeft m) (K.physicalRight m)) (physicalPieceOpen S K m) :=
    fun r hr => ⟨hr, mem_univ _⟩
  refine ⟨hh.comp hline.contDiffOn hmap, (hc.comp hline.contDiffOn hmap).fst, ?_⟩
  intro r hr
  have hp : (r, (0 : ℝ)) ∈ physicalPieceOpen S K m := ⟨hr, mem_univ _⟩
  refine ⟨(hn (r, 0) hp).1.ne', ?_⟩
  rw [← n05_reference_planeJacobian_radial h hcoordinates m hp]
  exact (hn (r, 0) hp).2.1

include h hcoordinates in
theorem n05ReferenceNormal_coefficients_measurable :
    Measurable (n05ReferenceNormalLeading S C K) ∧
      Measurable (n05ReferenceNormalDrift S C K) := by
  have hlead (m : ℕ) : ContinuousOn
      (fun r => (deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)⁻¹)
      (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
    obtain ⟨_, hc, hn⟩ := n05_referenceNormal_slices h hcoordinates m
    exact (hc.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).inv₀ (fun r hr => (hn r hr).2)
  have hdrift (m : ℕ) : ContinuousOn
      (fun r => deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r /
        K.height (C.referenceState, 0) m (r, 0) /
          deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)
      (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
    obtain ⟨hh, hc, hn⟩ := n05_referenceNormal_slices h hcoordinates m
    exact ((hh.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).div hh.continuousOn
      (fun r hr => (hn r hr).1)).div
        (hc.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)) (fun r hr => (hn r hr).2)
  exact ⟨(n05PhysicalPieceRadialMultiplier_measurable S K _ hlead).comp measurable_fst,
    (n05PhysicalPieceRadialMultiplier_measurable S K _ hdrift).comp measurable_fst⟩

include h hcoordinates in
theorem n05ReferenceRadialNormalField_eq (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) (u ur : PolarPoint → ℝ) :
    n05ReferenceRadialNormalField S C K u ur p =
      (ur p - u p * (radialPartial (K.height (C.referenceState, 0) m) p /
        K.height (C.referenceState, 0) m p)) /
          planeJacobian (K.chart (C.referenceState, 0) m) p := by
  unfold n05ReferenceRadialNormalField n05ReferenceNormalLeading n05ReferenceNormalDrift
  rw [n05PhysicalPieceRadialMultiplier_eq h.2.2.2.2 _ hp.1,
    n05PhysicalPieceRadialMultiplier_eq h.2.2.2.2 _ hp.1,
    n05_referenceHeight_radial_deriv h hcoordinates m hp,
    ← (hcoordinates.1 m p hp).2,
    ← n05_reference_planeJacobian_radial h hcoordinates m hp]
  simp only [div_eq_mul_inv]
  ring

theorem n05ReferenceRadialNormalField_periodic {u ur : PolarPoint → ℝ}
    (hu : Function.Periodic u (0, Real.pi)) (hur : Function.Periodic ur (0, Real.pi)) :
    Function.Periodic (n05ReferenceRadialNormalField S C K u ur) (0, Real.pi) := by
  intro p
  simp only [n05ReferenceRadialNormalField, n05ReferenceNormalLeading,
    n05ReferenceNormalDrift, Prod.fst_add, add_zero, hu p, hur p]

end ContinuousFlexibility.Statements
