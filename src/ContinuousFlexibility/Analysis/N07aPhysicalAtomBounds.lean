import ContinuousFlexibility.Analysis.N07aCanonicalAtomBounds
import ContinuousFlexibility.Analysis.N07aAngularPhysicalMeasure

/-!
# Raw atoms on the fixed reference physical intervals

Physical atoms are unscaled with the fixed reference interval inverse.
CurrentJets samples these reference intervals even at a current state;
the bounds here therefore have the explicit reference domain. Current
moving-domain estimates must instead use the actual inverse-chart bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

def n07aPhysicalAtomField (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (a : CanonicalGeometry.Atom)
    (z : CanonicalGeometry.Parameter S) (m : ℕ) : PolarPoint → ℝ :=
  CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m a ∘
    n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m

theorem n07a_physicalAtomField_smooth
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.physicalLeft m < K.physicalRight m) (a : CanonicalGeometry.Atom)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) :
    ContDiffOn ℝ ∞ (n07aPhysicalAtomField D T S C L K a z m) (referencePhysicalPieceOpen S K m) :=
  (hcur.1 z hz m a).1.comp n07aCanonicalUnitInversePoint_contDiff.contDiffOn
    (n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData K) (hinterval m))

theorem n07a_physicalAtomFields_sampleJetBounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.physicalLeft m < K.physicalRight m) :
    ∃ loss : ℕ, ∀ a : CanonicalGeometry.Atom,
      N07aSampleJetBounds T K (CanonicalGeometry.parameterGrading S)
        (sectorNeighborhood S base ε ε) (referencePhysicalPieceOpen S K) loss
        (n07aPhysicalAtomField D T S C L K a) := by
  have hb := n07a_geometryAtom_absolute_jet_bound hD hT href hcur
  let loss : ℕ := hb.choose
  have hbounds := hb.choose_spec
  have hlength := n07a_physicalLengthInverse_subpower hD hT href
  refine ⟨loss, fun atom a b => ?_⟩
  let e : ℕ → ℝ := (hbounds (a + b)).choose
  have he := (hbounds (a + b)).choose_spec.1
  have he0 := (hbounds (a + b)).choose_spec.2.1
  have heb := (hbounds (a + b)).choose_spec.2.2
  refine ⟨fun m => (K.physicalRight m - K.physicalLeft m)⁻¹ ^ a * e m,
    N07aSampleSubpower.mul hD hT (hlength.nat_pow hD hT a) he,
    fun m => mul_nonneg (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (hinterval m)).le) _) (he0 m), ?_⟩
  intro z hz m y hy
  have hx := n07aCanonicalUnitInversePoint_maps
    (K := n07aPhysicalIntervalData K) (hinterval m) hy
  have h := heb z hz m atom
    ⟨n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m y, hx⟩ a b le_rfl
  have hc : 0 ≤ (K.physicalRight m - K.physicalLeft m)⁻¹ ^ a :=
    pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (hinterval m)).le) a
  change |mixedDerivative a b
    (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m atom ∘
      n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m) y| ≤ _
  rw [n07a_mixedDerivative_unitInverse, abs_mul]
  have hc' : 0 ≤
      ((n07aPhysicalIntervalData K).right m - (n07aPhysicalIntervalData K).left m)⁻¹ ^ a := hc
  rw [abs_of_nonneg hc']
  exact (mul_le_mul_of_nonneg_left h hc).trans_eq (by ring)

theorem n07a_physicalAtomField_height (m : ℕ)
    (hm : K.physicalLeft m < K.physicalRight m) (z : CanonicalGeometry.Parameter S) :
    n07aPhysicalAtomField D T S C L K .height z m = K.height (liftSectorParameter S C z) m := by
  funext y
  have hy := n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K) hm y
  exact congrArg (K.height (liftSectorParameter S C z) m) hy

end ContinuousFlexibility.Analysis
