import ContinuousFlexibility.Analysis.N07aClosedJets
import ContinuousFlexibility.Analysis.N07aAngularPhysicalRepresentative

/-!
# Genuine closed physical heights from the canonical jet extension

The extension is composed with the actual chart on its actual state domain.
Its restriction to that domain has the same values as the smooth decoder.
Boundary smoothness is within the physical closure, not across its boundary.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open N07aClosedJets
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The actual height reconstructed from the unique closed zeroth jet. -/
def n07aClosedPhysicalHeight (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v) (p : PolarPoint) : ℝ :=
  K.height z m p * J.value 0 0 (K.chart z m p)

theorem n07aClosedPhysicalHeight_contDiffOn
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v) :
    ContDiffOn ℝ ∞ (n07aClosedPhysicalHeight K z m J)
      (physicalPieceClosed S K z m) := by
  have hb := h04.1.boundary z hz hs m
  have hchart : ContDiffOn ℝ ∞ (K.chart z m) (physicalPieceClosed S K z m) :=
    fun p hp => (hb.2.2.2.2.1 p hp).1.contDiffWithinAt
  have hh : ContDiffOn ℝ ∞ (K.height z m) (physicalPieceClosed S K z m) :=
    fun p hp => (hb.2.2.2.2.1 p hp).2.1.contDiffWithinAt
  exact hh.mul ((J.contDiffOn (h04.1.referenceBounds m).2.1 0 0).comp hchart hb.1)

theorem n07aClosedPhysicalHeight_eqOn
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v) :
    EqOn (n07aClosedPhysicalHeight K z m J)
      (n07aPhysicalHeightRepresentative K z m v) (physicalPieceOpen S K z m) := by
  intro p hp
  have he := J.agrees 0 0 ((h04.1.charts z hz hs m).1 hp)
  simpa only [n07aClosedPhysicalHeight, n07aPhysicalHeightRepresentative,
    spaces_mixedDerivative_zero] using congrArg (K.height z m p * ·) he

theorem n07a_referencePhysicalPieceClosed
    (h04 : N04Properties D T S C L K base loss ε) (m : ℕ) :
    physicalPieceClosed S K (C.referenceState, 0) m =
      closedStrip (K.physicalLeft m) (K.physicalRight m) := by
  rw [physicalPieceClosed, h04.1.referenceDomain m]
  exact closure_openStrip (h04.1.referenceBounds m).1

/-- At the reference state the genuine closure is the fixed closed strip. -/
theorem n07aClosedPhysicalHeight_reference_contDiffOn
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v) :
    ContDiffOn ℝ ∞ (n07aClosedPhysicalHeight K (C.referenceState, 0) m J)
      (closedStrip (K.physicalLeft m) (K.physicalRight m)) := by
  rw [← n07a_referencePhysicalPieceClosed h04 m]
  exact n07aClosedPhysicalHeight_contDiffOn h04 href hsref m J

/-- The closed reference height retains the actual angular period. -/
theorem n07aClosedPhysicalHeight_reference_periodic
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (m : ℕ) {v : PolarPoint → ℝ} (hvp : Function.Periodic v (0, Real.pi))
    (J : ClosedJetTower (K.left m) (K.right m) v) :
    ∀ p ∈ closedStrip (K.physicalLeft m) (K.physicalRight m),
      n07aClosedPhysicalHeight K (C.referenceState, 0) m J (p + (0, Real.pi)) =
        n07aClosedPhysicalHeight K (C.referenceState, 0) m J p := by
  let W := n07aClosedPhysicalHeight K (C.referenceState, 0) m J
  have hW := (n07aClosedPhysicalHeight_reference_contDiffOn h04 href hsref m J).continuousOn
  have he : EqOn (fun p => W (p + (0, Real.pi))) W
      (openStrip (K.physicalLeft m) (K.physicalRight m)) := by
    intro p hp
    have hp' : p + (0, Real.pi) ∈
        openStrip (K.physicalLeft m) (K.physicalRight m) :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
    have hphys : p ∈ physicalPieceOpen S K (C.referenceState, 0) m := by
      rw [h04.1.referenceDomain m]
      exact hp
    have hphys' : p + (0, Real.pi) ∈ physicalPieceOpen S K (C.referenceState, 0) m := by
      rw [h04.1.referenceDomain m]
      exact hp'
    exact (n07aClosedPhysicalHeight_eqOn h04 href hsref m J hphys').trans
      ((n07aPhysicalHeightRepresentative_periodic_on h04 href hsref m hvp p hphys).trans
        (n07aClosedPhysicalHeight_eqOn h04 href hsref m J hphys).symm)
  have hshift : MapsTo (fun p : PolarPoint => p + (0, Real.pi))
      (closedStrip (K.physicalLeft m) (K.physicalRight m))
      (closedStrip (K.physicalLeft m) (K.physicalRight m)) := by
    intro p hp
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  exact he.of_subset_closure
    (hW.comp (continuous_id.add continuous_const).continuousOn hshift) hW
    (fun _ hp => ⟨Ioo_subset_Icc_self hp.1, hp.2⟩)
    (by rw [closure_openStrip (h04.1.referenceBounds m).1])

end ContinuousFlexibility.Analysis
