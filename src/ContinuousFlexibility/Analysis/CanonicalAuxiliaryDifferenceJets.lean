import ContinuousFlexibility.Analysis.CanonicalAuxiliaryNormalization
import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
import ContinuousFlexibility.Analysis.SolveReturnEquations
import ContinuousFlexibility.Analysis.StateNeighborhood
import ContinuousFlexibility.Analysis.N08Neighborhoods

/-!
# The actual auxiliary atom has a zero difference tower

The auxiliary column is the one retained by the physical spaces.  Its
proved support condition freezes its canonical source on the open strip.
Open-set locality gives every actual mixed difference jet, and the zero
continuous multilinear maps form a genuine state derivative tower.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry

theorem canonical_auxiliaryColumn_eqOn_reference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hA : CanonicalGeometry D S C K base ε) (hψ : AuxiliaryColumnGauge S K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    EqOn (atom D T S C L K z m .auxiliaryColumn)
      (atom D T S C L K (C.referenceState, 0) m .auxiliaryColumn) unitStrip := by
  have he := canonicalSource_eqOn_reference_of_normalization hA
    (reference_mem_stateNeighborhood S C base hN.1.1.2.1)
    hN.1.1.2.2.1.stateSector hz hs m ((S.height (3 / 4 : ℝ)).decode S.psi) hψ.2
  intro p hp
  have hlen := (hA.referenceBounds m).2.1
  have hl : 0 < (K.right m - K.left m) * p.1 :=
    mul_pos (sub_pos.mpr hlen) hp.1.1
  have hu : (K.right m - K.left m) * p.1 < K.right m - K.left m :=
    mul_lt_of_lt_one_right (sub_pos.mpr hlen) hp.1.2
  have hpoint : canonicalUnitPoint K m p ∈ canonicalOpen S K m := by
    refine ⟨?_, mem_univ _⟩
    dsimp only [canonicalUnitPoint]
    constructor <;> linarith
  exact he hpoint

theorem canonical_auxiliaryDifferenceJets_eq_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hA : CanonicalGeometry D S C K base ε) (hψ : AuxiliaryColumnGauge S K)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε)
    (m i j : ℕ) (p : unitStrip) :
    differenceJets D T S C L K z .auxiliaryColumn m i j p = 0 := by
  have hz' := liftSectorParameter_mem_stateNeighborhood hz (le_refl ε)
  have hs := hN.1.1.2.2.1.liftSectorParameter_sector z
  have he := canonical_auxiliaryColumn_eqOn_reference hN hA hψ hz' hs m
  have hzero : EqOn
      (fun q => atom D T S C L K (liftSectorParameter S C z) m .auxiliaryColumn q -
        atom D T S C L K (C.referenceState, 0) m .auxiliaryColumn q)
      (fun _ : PolarPoint => (0 : ℝ)) unitStrip := by
    intro q hq
    exact sub_eq_zero.mpr (he hq)
  have hderiv := (mixedDerivative_eqOn_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) hzero i j) (x := (p : PolarPoint)) p.property
  simpa only [differenceJets, mixedDerivative, iteratedDeriv_fun_const_zero] using hderiv

/-- This is the tower of the auxiliary slice of the actual difference
field.  It makes no assertion that the other primitive atoms are zero. -/
theorem exists_canonicalAuxiliaryDifference_zero_tower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hA : CanonicalGeometry D S C K base ε) (hψ : AuxiliaryColumnGauge S K) :
    ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z : Parameter S => differenceJets D T S C L K z .auxiliaryColumn),
      ∀ k z v, J.D k z v = 0 := by
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z : Parameter S => differenceJets D T S C L K z .auxiliaryColumn) := {
    open_domain := n08_isOpen_sectorNeighborhood S base ε ε
    D := fun _ _ => 0
    zero := by
      intro z hz
      funext m i j p
      exact (canonical_auxiliaryDifferenceJets_eq_zero hN hA hψ hz m i j p).symm
    continuous := by
      intro n
      simpa only [ContinuousMultilinearMap.zero_apply] using
        (continuous_const.continuousOn : ContinuousOn
          (fun _ : Parameter S × (Fin n → Parameter S) =>
            (0 : ℕ → ℕ → ℕ → unitStrip → ℝ))
          (sectorNeighborhood S base ε ε ×ˢ univ))
    derivative := by
      intro n z hz v w
      simpa only [ContinuousMultilinearMap.zero_apply] using
        (hasProjectiveLineDerivAt_const (0 : ℕ → ℕ → ℕ → unitStrip → ℝ) z w) }
  exact ⟨J, fun _ _ _ => rfl⟩

end ContinuousFlexibility.Analysis
