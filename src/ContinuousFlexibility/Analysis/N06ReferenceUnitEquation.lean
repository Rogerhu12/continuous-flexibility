module

public import ContinuousFlexibility.Analysis.N06ReferenceCanonicalEquation
public import ContinuousFlexibility.Analysis.N06RadialCanonicalOperator
public import ContinuousFlexibility.Analysis.N06WeakCylinderGraph

/-!
# The genuine N05 reference equation on the unit cylinder

The radial identities for the actual canonical coefficients identify its
formal test operator. Combining that identity with the original N05 graph
gives precisely the weak equation used by the graph estimates, retaining
the same height and the source with its three actual scalar columns.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

theorem n06N05_positive_unitWeakPairing
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {Vol : VolumeModelData S K}
    {base b m : ℕ} {ε : ℝ} {B : CanonicalDomainData S K Vol b}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hS : IsPhysicalSpaces D T S)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hN05 : N05Properties D T S C K Vol b B)
    (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (u : B.Space) (hm : K.positive m = true)
    {a c V : ℝ → ℝ}
    (ha : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a p.1) (canonicalOpen S K m))
    (hb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hc : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun p => c p.1) (canonicalOpen S K m))
    (hV : EqOn (K.potential (C.referenceState, 0) m)
      (fun p => V p.1) (canonicalOpen S K m))
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, u.val.1.1 m p * n06UnitReferenceTestOperator a c V φ p
      ∂canonicalMeasure S K m) =
      ∫ p, n06ReferenceCanonicalForcing D S C K u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m p * φ p ∂canonicalMeasure S K m := by
  exact (n06_canonicalOperator_pairing_eq_unitReference hB hz hs hm
    ha hb hc hV hcd (u.val.1.1 m) hφ.1).symm.trans
      (n06N05_positive_canonicalWeakPairing hD hborder hS hN03 hA hN05
        href hz hs u hm hφ)

/-- After the actual unit endpoint identities, this is the very weak PDE
from which the simultaneous modal graph construction starts. -/
theorem n06N05_positive_unitWeakEquation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {Vol : VolumeModelData S K}
    {base b m : ℕ} {ε : ℝ} {B : CanonicalDomainData S K Vol b}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hS : IsPhysicalSpaces D T S)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hN05 : N05Properties D T S C K Vol b B)
    (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (u : B.Space) (hm : K.positive m = true)
    (hl : K.left m = 0) (hr : K.right m = 1)
    {a c V : ℝ → ℝ}
    (ha : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a p.1) (canonicalOpen S K m))
    (hb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hc : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun p => c p.1) (canonicalOpen S K m))
    (hV : EqOn (K.potential (C.referenceState, 0) m)
      (fun p => V p.1) (canonicalOpen S K m))
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y) :
    n06UnitReferenceWeakEquation a c V (u.val.1.1 m)
      (n06ReferenceCanonicalForcing D S C K u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m) := by
  intro φ hφ
  have h := n06N05_positive_unitWeakPairing hD hborder hS hN03 hA hB hN05 href hz hs
    u hm ha hb hc hV hcd ((n06_unitCanonicalTest_iff hl hr φ).mp hφ)
  simpa only [n06_canonical_unit_measure_eq_window hl hr] using h

end ContinuousFlexibility.Analysis
