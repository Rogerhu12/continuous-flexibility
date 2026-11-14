module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Topology.Constructions.SumProd

/-!
# Access to current and reference canonical geometry

Current half-period pieces are intersections with the actual physical
domain. Only at the reference state does `referenceDomain` identify them
with a radial rectangle. The accessors below make that specialization
explicit and keep the current-state domain in every general statement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

def n05PhysicalPieceHalfPeriod (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : Set PolarPoint :=
  physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)

theorem n05_physicalPieceHalfPeriod_measurable
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    MeasurableSet (n05PhysicalPieceHalfPeriod S K z m) :=
  (h04.1.domains z hz hs m).1.measurableSet.inter
    (MeasurableSet.univ.prod measurableSet_Ioc)

theorem n05_reference_physicalHalfPeriod_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} (h04 : N04Properties D T S C L K base loss ε) (m : ℕ) :
    n05PhysicalPieceHalfPeriod S K (C.referenceState, 0) m =
      Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi := by
  rw [n05PhysicalPieceHalfPeriod, h04.1.referenceDomain m]
  ext p
  simp only [referencePhysicalPieceOpen, mem_inter_iff, mem_prod, mem_univ,
    and_true, true_and]

theorem n05_reference_physicalClosed_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} (h04 : N04Properties D T S C L K base loss ε) (m : ℕ) :
    physicalPieceClosed S K (C.referenceState, 0) m =
      Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ (univ : Set ℝ) := by
  rw [physicalPieceClosed, h04.1.referenceDomain m, referencePhysicalPieceOpen,
    closure_prod_eq, closure_Ioo (h04.1.referenceBounds m).1.ne, closure_univ]

theorem n05_reference_charts
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} (h04 : N04Properties D T S C L K base loss ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (m : ℕ) :
    MapsTo (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m)
        (canonicalOpen S K m) ∧
      MapsTo (K.inverseChart (C.referenceState, 0) m) (canonicalOpen S K m)
        (referencePhysicalPieceOpen S K m) ∧
      (∀ p ∈ referencePhysicalPieceOpen S K m,
        K.inverseChart (C.referenceState, 0) m (K.chart (C.referenceState, 0) m p) = p) ∧
      (∀ p ∈ canonicalOpen S K m,
        K.chart (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) = p) ∧
      ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.inverseChart (C.referenceState, 0) m) (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.height (C.referenceState, 0) m) (referencePhysicalPieceOpen S K m) ∧
      (∀ p ∈ referencePhysicalPieceOpen S K m,
        0 < K.height (C.referenceState, 0) m p ∧
        planeJacobian (K.chart (C.referenceState, 0) m) p ≠ 0 ∧
        K.chart (C.referenceState, 0) m (p + (0, Real.pi)) =
          K.chart (C.referenceState, 0) m p + (0, Real.pi) ∧
        K.height (C.referenceState, 0) m (p + (0, Real.pi)) =
          K.height (C.referenceState, 0) m p) := by
  simpa only [h04.1.referenceDomain m] using
    h04.1.charts (C.referenceState, 0) hz hs m

theorem n05_reference_closed_properties
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} (h04 : N04Properties D T S C L K base loss ε)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    ContDiffAt ℝ ∞ (K.chart (C.referenceState, 0) m) p ∧
      ContDiffAt ℝ ∞ (K.height (C.referenceState, 0) m) p ∧
      planeJacobian (K.chart (C.referenceState, 0) m) p ≠ 0 ∧
      0 < K.height (C.referenceState, 0) m p := by
  have hp' : p ∈ physicalPieceClosed S K (C.referenceState, 0) m := by
    rw [n05_reference_physicalClosed_eq h04 m]
    exact ⟨hp, mem_univ _⟩
  exact (h04.1.boundary (C.referenceState, 0) hz hs m).2.2.2.2.1 p hp'

end ContinuousFlexibility.Statements
