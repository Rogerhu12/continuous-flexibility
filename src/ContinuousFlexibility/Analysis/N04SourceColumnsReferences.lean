import ContinuousFlexibility.Analysis.N04SourceColumnsGeometry
import ContinuousFlexibility.Analysis.N04SourceColumnsLinear
import ContinuousFlexibility.Analysis.N04SourceColumnsReferenceProduct
import ContinuousFlexibility.Analysis.N04SourceColumnsReferenceReciprocal
import ContinuousFlexibility.Analysis.N07aCurrentPhysicalGeometry
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient

/-!
# Reference envelopes for the supplied pulled families

The reference inverse chart takes the canonical strip into the stored
reference physical strip.  Its determinant reciprocal is consequently
bounded by the reference Jacobian atom.  The exact source identity then
recovers the pulled height, and the exact column identities recover the
two pulled columns.  No current output jet is used in these estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

namespace N04RealizationGauge

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

theorem sourceColumns_factor_pos {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    0 < G.atomFamily η .sourceFactor z m p := by
  have hg := G.sourceColumns_geometry_of_admissible η hA
  have hc := hg.charts (G.lift η z) (G.sourceColumns_lift_mem η hz)
    (G.sourceColumns_lift_sector η z) m
  have hq := n04SourceColumns_unitPoint_mem (hg.referenceBounds m).2.1 hp
  have hpos := hc.2.2.2.2.2.2.2 _ (hc.2.1 hq)
  change 0 < canonicalSource (G.S η) (G.V η) (G.lift η z) m
    (fun _ => 1) (canonicalUnitPoint (G.V η) m p)
  simp only [canonicalSource, mul_one]
  exact div_pos hpos.1 (abs_pos.mpr hpos.2.1)

theorem sourceColumns_factorRef_pos {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    0 < G.atomRef η .sourceFactor m p := by
  have hg := G.sourceColumns_geometry_of_admissible η hA
  have hc := hg.charts (G.ref η)
    (reference_mem_stateNeighborhood (G.S η) (G.C η) b hA.2.1)
    (G.sourceColumns_referenceStateConditions η).stateSector m
  have hq := n04SourceColumns_unitPoint_mem (hg.referenceBounds m).2.1 hp
  have hpos := hc.2.2.2.2.2.2.2 _ (hc.2.1 hq)
  change 0 < canonicalSource (G.S η) (G.V η) (G.ref η) m
    (fun _ => 1) (canonicalUnitPoint (G.V η) m p)
  simp only [canonicalSource, mul_one]
  exact div_pos hpos.1 (abs_pos.mpr hpos.2.1)

theorem sourceColumns_inverseDeterminantRef_ne_zero {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    G.sourceColumnsInverseDeterminantRef η m p ≠ 0 := by
  have hg := G.sourceColumns_geometry_of_admissible η hA
  have hq := n04SourceColumns_unitPoint_mem (hg.referenceBounds m).2.1 hp
  have hz := reference_mem_stateNeighborhood (G.S η) (G.C η) b hA.2.1
  have hs := (G.sourceColumns_referenceStateConditions η).stateSector
  have hc := hg.charts (G.ref η) hz hs m
  rw [G.sourceColumns_inverseDeterminantRef_eq η hA href m hp]
  apply abs_ne_zero.mp
  rw [n07a_actual_inverseChart_jacobian_abs hg hz hs m hq]
  exact inv_ne_zero (abs_ne_zero.mpr (hc.2.2.2.2.2.2.2 _ (hc.2.1 hq)).2.1)

/-- Only reference geometry is needed to place the inverse point in the
fixed physical strip used by the reference Jacobian atom. -/
theorem sourceColumns_inverseDeterminantRef_reciprocal_bound {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ unitStrip →
      |(|G.sourceColumnsInverseDeterminantRef η m p|)⁻¹| ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  have hg := G.sourceColumns_geometry_of_admissible η hA
  have hz := reference_mem_stateNeighborhood (G.S η) (G.C η) b hA.2.1
  have hs := (G.sourceColumns_referenceStateConditions η).stateSector
  have hzero := href.2 0
  refine ⟨hzero.choose, hzero.choose_spec.1, ?_⟩
  intro m p hp
  have hq := n04SourceColumns_unitPoint_mem (hg.referenceBounds m).2.1 hp
  have hc := hg.charts (G.ref η) hz hs m
  let x := G.pulledPoint η (G.ref η) m p
  have hx : x ∈ referencePhysicalPieceOpen (G.S η) (G.V η) m := by
    rw [← hg.referenceDomain m]
    exact hc.2.1 hq
  let q := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) m x
  have hqu : q ∈ unitStrip :=
    n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData (G.V η))
      (hg.referenceBounds m).1 hx
  have hpoint : physicalUnitPoint (G.V η) m q = x :=
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData (G.V η))
      (hg.referenceBounds m).1 x
  have hb := hzero.choose_spec.2 m .jacobian q hqu 0 0 (by omega)
  have hvalue : |mixedDerivative 0 0
      (atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
        (G.ref η) m .jacobian) q| =
      |planeJacobian ((G.V η).chart (G.ref η) m) x| := by
    simp only [spaces_mixedDerivative_zero, atom, abs_abs, hpoint]
  have hb' : |planeJacobian ((G.V η).chart (G.ref η) m) x| ≤
      hzero.choose * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ hzero.choose :=
    hvalue.symm.trans_le hb
  calc
    |(|G.sourceColumnsInverseDeterminantRef η m p|)⁻¹| =
        |planeJacobian ((G.V η).chart (G.ref η) m) x| := by
      rw [abs_inv, abs_abs, G.sourceColumns_inverseDeterminantRef_eq η hA href m hp,
        n07a_actual_inverseChart_jacobian_abs hg hz hs m hq, inv_inv]
    _ ≤ _ := hb'

/-- The reference pulled height is recovered from the source factor and
the absolute inverse determinant, all at the same canonical unit point. -/
theorem sourceColumns_pulledHeightRef_eq {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    G.atomRef η .sourceFactor m p * (|G.sourceColumnsInverseDeterminantRef η m p|)⁻¹ =
      G.pulledHeightRef η m p := by
  rw [G.sourceColumns_factorRef_eq_absDeterminant η hA href m hp, mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.mpr
      (G.sourceColumns_inverseDeterminantRef_ne_zero η hA href m hp)), mul_one]

theorem sourceColumns_pulledHeightRef_data {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hdet : N04SourceReferenceData G.W.U (G.V η).cell
      (fun m p => |G.sourceColumnsInverseDeterminantRef η m p|)) :
    N04SourceReferenceData G.W.U (G.V η).cell (G.pulledHeightRef η) := by
  have hE := (G.cost_nonneg η).2.2
  have hi := hdet.sourceColumns_inv hE
    (fun m p hp => abs_ne_zero.mpr
      (G.sourceColumns_inverseDeterminantRef_ne_zero η hA href m hp))
    (G.sourceColumns_inverseDeterminantRef_reciprocal_bound η hA href)
  have hf := n04SourceReferenceData_of_referenceJets href .sourceFactor
  exact (hf.sourceColumns_mul hi hE).sourceColumns_congr
    (fun m p hp => G.sourceColumns_pulledHeightRef_eq η hA href m hp)

theorem sourceColumns_pulledLeftRef_eq {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    G.atomRef η .sourceFactorInverse m p * G.atomRef η .leftColumn m p =
      G.pulledRef η (G.leftColumnField η) m p := by
  rw [G.sourceColumns_inverseRef_eq η, G.sourceColumns_leftRef_eq η]
  exact inv_mul_cancel_left₀ (G.sourceColumns_factorRef_pos η hA m hp).ne' _

theorem sourceColumns_pulledNuRef_eq {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :
    G.atomRef η .sourceFactorInverse m p * G.atomRef η .nuColumn m p =
      G.pulledRef η (G.nuField η) m p := by
  rw [G.sourceColumns_inverseRef_eq η, G.sourceColumns_nuRef_eq η]
  exact inv_mul_cancel_left₀ (G.sourceColumns_factorRef_pos η hA m hp).ne' _

theorem sourceColumns_pulledLeftRef_data {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    N04SourceReferenceData G.W.U (G.V η).cell (G.pulledRef η (G.leftColumnField η)) := by
  have hi := n04SourceReferenceData_of_referenceJets href .sourceFactorInverse
  have hf := n04SourceReferenceData_of_referenceJets href .leftColumn
  exact (hi.sourceColumns_mul hf (G.cost_nonneg η).2.2).sourceColumns_congr
    (fun m p hp => G.sourceColumns_pulledLeftRef_eq η hA m hp)

theorem sourceColumns_pulledNuRef_data {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    N04SourceReferenceData G.W.U (G.V η).cell (G.pulledRef η (G.nuField η)) := by
  have hi := n04SourceReferenceData_of_referenceJets href .sourceFactorInverse
  have hf := n04SourceReferenceData_of_referenceJets href .nuColumn
  exact (hi.sourceColumns_mul hf (G.cost_nonneg η).2.2).sourceColumns_congr
    (fun m p hp => G.sourceColumns_pulledNuRef_eq η hA m hp)

end N04RealizationGauge

end ContinuousFlexibility.Analysis
