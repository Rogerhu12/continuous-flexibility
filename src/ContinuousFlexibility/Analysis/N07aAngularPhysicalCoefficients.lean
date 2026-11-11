import ContinuousFlexibility.Analysis.N07aAngularPhysicalMeasure
import ContinuousFlexibility.Analysis.N07aCanonicalScalarColumns

/-!
# Actual physical chart and gauge coefficients with bounded jets

The chart's angular derivative is expressed using its normalized radial
component and its angular defect from the identity. Both are primitive
geometric atoms. This supplies the two actual coefficients in the angular
chain rule, while retaining the original chart and height functions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

namespace N07aCanonicalOpenCoefficient

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def constant (c : ℝ) : N07aCanonicalOpenCoefficient S K m where
  value := fun _ => c
  smooth := contDiffOn_const
  periodic := fun _ _ => rfl
  bounded := by
    intro a b
    refine ⟨|c|, abs_nonneg c, Filter.Eventually.of_forall ?_⟩
    intro p
    simp only [mixedDerivative, iteratedDeriv_const]
    split_ifs <;> simp only [abs_zero, le_refl, abs_nonneg]

def addValue (χ ψ : N07aCanonicalOpenCoefficient S K m) :
    N07aCanonicalOpenCoefficient S K m where
  value := fun p => χ.value p + ψ.value p
  smooth := χ.smooth.add ψ.smooth
  periodic := fun p hp => congrArg₂ (· + ·) (χ.periodic p hp) (ψ.periodic p hp)
  bounded := by
    intro a b
    obtain ⟨A, hA, hbA⟩ := χ.bounded a b
    obtain ⟨B, hB, hbB⟩ := ψ.bounded a b
    refine ⟨A + B, add_nonneg hA hB, ?_⟩
    filter_upwards [hbA, hbB, n07a_canonicalOpen_ae (S := S) (K := K) (m := m)]
      with p hp hq hpU
    rw [n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
      χ.smooth ψ.smooth a b hpU]
    exact (abs_add_le _ _).trans (add_le_add hp hq)

end N07aCanonicalOpenCoefficient

def n07aPhysicalJetAtom (i : Fin 6) : CanonicalGeometry.Atom :=
  ![.chartRadial, .chartAngleDefect, .height, .heightInverse, .jacobian, .jacobianInverse] i

def n07aPhysicalJetField {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (i : Fin 6) : PolarPoint → ℝ :=
  ![fun p => ((K.chart z m p).1 - K.left m) / (K.right m - K.left m),
    fun p => (K.chart z m p).2 - p.2,
    K.height z m, fun p => (K.height z m p)⁻¹,
    fun p => |planeJacobian (K.chart z m) p|,
    fun p => |planeJacobian (K.chart z m) p|⁻¹] i

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07aPhysicalJetField_unit (z : AnnularState S × ℝ) (m : ℕ) (i : Fin 6) :
    n07aPhysicalJetField K z m i ∘
        CanonicalGeometry.canonicalUnitPoint (n07aPhysicalIntervalData K) m =
      CanonicalGeometry.atom D T S C L K z m (n07aPhysicalJetAtom i) := by
  fin_cases i <;> rfl

def n07aCurrentPhysicalOpenCoefficient
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.physicalLeft m < K.physicalRight m) (i : Fin 6) :
    N07aCanonicalOpenCoefficient S (n07aPhysicalIntervalData K) m :=
  n07aCanonicalOpenCoefficientOfUnit hm
    (n07aPhysicalJetField K (liftSectorParameter S C z) m i)
    (by rw [n07aPhysicalJetField_unit]; exact (hcur.1 z hz m (n07aPhysicalJetAtom i)).1)
    (by
      intro p hp
      have h := (hcur.1 z hz m (n07aPhysicalJetAtom i)).2 p hp
      simpa only [← n07aPhysicalJetField_unit, Function.comp_apply] using h)
    (by
      intro a b
      rw [n07aPhysicalJetField_unit]
      exact n07a_currentAtom_bounded href hcur z hz m (n07aPhysicalJetAtom i) a b)

theorem n07aCurrentPhysicalOpenCoefficient_value
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.physicalLeft m < K.physicalRight m) (i : Fin 6) :
    (n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm i).value =
      n07aPhysicalJetField K (liftSectorParameter S C z) m i := rfl

def n07aChartRadialAngularCoefficient
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.physicalLeft m < K.physicalRight m) :
    N07aCanonicalOpenCoefficient S (n07aPhysicalIntervalData K) m :=
  ((n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm 0).jet 0 1).constMul
    (K.right m - K.left m)

def n07aChartAngularAngularCoefficient
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.physicalLeft m < K.physicalRight m) :
    N07aCanonicalOpenCoefficient S (n07aPhysicalIntervalData K) m :=
  ((n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm 1).jet 0 1).addValue
    (N07aCanonicalOpenCoefficient.constant 1)

theorem n07aChartRadialAngularCoefficient_value
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.physicalLeft m < K.physicalRight m)
    (hcan : K.left m < K.right m) :
    (n07aChartRadialAngularCoefficient href hcur z hz m hm).value =
      mixedDerivative 0 1 (fun p => (K.chart (liftSectorParameter S C z) m p).1) := by
  let χ := n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm 0
  have hlen : K.right m - K.left m ≠ 0 := (sub_pos.mpr hcan).ne'
  have he : (fun p => (K.chart (liftSectorParameter S C z) m p).1) =
      fun p => (K.right m - K.left m) * χ.value p + K.left m := by
    funext p
    change (K.chart (liftSectorParameter S C z) m p).1 =
      (K.right m - K.left m) *
        (((K.chart (liftSectorParameter S C z) m p).1 - K.left m) /
          (K.right m - K.left m)) + K.left m
    field_simp [hlen]
    ring
  rw [he]
  funext p
  change (K.right m - K.left m) * mixedDerivative 0 1 χ.value p = _
  simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one,
    deriv_add_const, deriv_const_mul_field]

theorem n07aChartAngularAngularCoefficient_value
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.physicalLeft m < K.physicalRight m) :
    EqOn (n07aChartAngularAngularCoefficient href hcur z hz m hm).value
      (mixedDerivative 0 1 (fun p => (K.chart (liftSectorParameter S C z) m p).2))
      (physicalPieceOpen S K m) := by
  let χ := n07aCurrentPhysicalOpenCoefficient href hcur z hz m hm 1
  have he : (fun p => (K.chart (liftSectorParameter S C z) m p).2) =
      fun p => χ.value p + p.2 := by
    funext p
    exact (sub_add_cancel _ _).symm
  intro p hp
  have hχ : DifferentiableAt ℝ (fun θ : ℝ => χ.value (p.1, θ)) p.2 :=
    ((χ.smooth.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).comp
      p.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  rw [he]
  change mixedDerivative 0 1 χ.value p + 1 = _
  simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one]
  simpa only [id_eq, deriv_id] using (deriv_fun_add hχ differentiableAt_id).symm

end ContinuousFlexibility.Analysis
