import ContinuousFlexibility.Analysis.N07aAngularPhysicalMeasure
import ContinuousFlexibility.Analysis.N07aCanonicalScalarColumns

/-!
# Actual physical chart and gauge coefficients with bounded jets

The current physical domain follows the state. Closed boundary germs,
compactness of the canonical fundamental rectangle, and the actual inverse
chart give finite bounds for every fixed spatial jet. These are qualitative
multipliers for L² pullback; their constants may depend on the state and
piece, and do not assert a uniform tame estimate.
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

/-- A qualitative multiplier on the actual current physical domain.
Its finite constants may depend on the state and piece. -/
structure N07aPhysicalOpenCoefficient (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) where
  value : PolarPoint → ℝ
  openDomain : IsOpen (physicalPieceOpen S K z m)
  smooth : ContDiffOn ℝ ∞ value (physicalPieceOpen S K z m)
  bounded : ∀ a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧
    ∀ᵐ p ∂n07aPhysicalMeasure S K z m, |mixedDerivative a b value p| ≤ B

namespace N07aPhysicalOpenCoefficient

variable {z : AnnularState S × ℝ} {m : ℕ}

def jet (chi : N07aPhysicalOpenCoefficient S K z m) (a b : ℕ) :
    N07aPhysicalOpenCoefficient S K z m where
  value := mixedDerivative a b chi.value
  openDomain := chi.openDomain
  smooth := contDiffOn_mixedDerivative chi.openDomain chi.smooth a b
  bounded := by
    intro c d
    obtain ⟨B, hB, hb⟩ := chi.bounded (c + a) (d + b)
    refine ⟨B, hB, ?_⟩
    have hmem : ∀ᵐ p ∂n07aPhysicalMeasure S K z m,
        p ∈ physicalPieceOpen S K z m :=
      (ae_restrict_mem (chi.openDomain.measurableSet.inter
        (MeasurableSet.univ.prod measurableSet_Ioc))).mono fun _ hp => hp.1
    filter_upwards [hb, hmem] with p hp hpU
    rw [n07a_mixedDerivative_mixedDerivative_on chi.openDomain chi.smooth c d a b hpU]
    exact hp

def bound (chi : N07aPhysicalOpenCoefficient S K z m) : ℝ :=
  (chi.bounded 0 0).choose

theorem bound_nonneg (chi : N07aPhysicalOpenCoefficient S K z m) :
    0 ≤ chi.bound := (chi.bounded 0 0).choose_spec.1

theorem bound_ae (chi : N07aPhysicalOpenCoefficient S K z m) :
    ∀ᵐ p ∂n07aPhysicalMeasure S K z m, |chi.value p| ≤ chi.bound := by
  simpa only [spaces_mixedDerivative_zero] using (chi.bounded 0 0).choose_spec.2

end N07aPhysicalOpenCoefficient

variable {loss : ℕ} {z : AnnularState S × ℝ}

def n07aPhysicalOpenCoefficientOfClosed
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (f : PolarPoint → ℝ)
    (hf : ∀ p ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f p) :
    N07aPhysicalOpenCoefficient S K z m where
  value := f
  openDomain := (h04.1.domains z hz hs m).1
  smooth := fun p hp => (hf p (subset_closure hp)).contDiffWithinAt
  bounded := n07a_physical_mixedDerivative_bound_ae h04 hz hs m hf

theorem n07aPhysicalJetField_contDiffAt_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (i : Fin 6) {p : PolarPoint} (hp : p ∈ physicalPieceClosed S K z m) :
    ContDiffAt ℝ ∞ (n07aPhysicalJetField K z m i) p := by
  have h := (h04.1.boundary z hz hs m).2.2.2.2.1 p hp
  have hJ := ContinuousFlexibility.contDiffAt_planeJacobian h.1
  fin_cases i
  · simpa only [n07aPhysicalJetField, Fin.isValue, Matrix.cons_val_zero, div_eq_mul_inv] using
      (h.1.fst.sub (contDiffAt_const (c := K.left m))).mul
        (contDiffAt_const (c := (K.right m - K.left m)⁻¹))
  · exact h.1.snd.sub contDiffAt_snd
  · exact h.2.1
  · exact h.2.1.inv h.2.2.2.ne'
  · exact hJ.abs h.2.2.1
  · exact (hJ.abs h.2.2.1).inv (abs_ne_zero.mpr h.2.2.1)

def n07aCurrentPhysicalOpenCoefficient
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (i : Fin 6) : N07aPhysicalOpenCoefficient S K z m :=
  n07aPhysicalOpenCoefficientOfClosed h04 hz hs m (n07aPhysicalJetField K z m i)
    (fun _ hp => n07aPhysicalJetField_contDiffAt_closed h04 hz hs m i hp)

theorem n07aCurrentPhysicalOpenCoefficient_value
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (i : Fin 6) :
    (n07aCurrentPhysicalOpenCoefficient h04 hz hs m i).value =
      n07aPhysicalJetField K z m i := rfl

def n07aChartRadialAngularCoefficient
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) : N07aPhysicalOpenCoefficient S K z m :=
  n07aPhysicalOpenCoefficientOfClosed h04 hz hs m
    (mixedDerivative 0 1 (fun p => (K.chart z m p).1))
    (fun p hp => contDiffAt_mixedDerivative
      ((h04.1.boundary z hz hs m).2.2.2.2.1 p hp).1.fst 0 1)

def n07aChartAngularAngularCoefficient
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) : N07aPhysicalOpenCoefficient S K z m :=
  n07aPhysicalOpenCoefficientOfClosed h04 hz hs m
    (mixedDerivative 0 1 (fun p => (K.chart z m p).2))
    (fun p hp => contDiffAt_mixedDerivative
      ((h04.1.boundary z hz hs m).2.2.2.2.1 p hp).1.snd 0 1)

theorem n07aChartRadialAngularCoefficient_value
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) :
    (n07aChartRadialAngularCoefficient h04 hz hs m).value =
      mixedDerivative 0 1 (fun p => (K.chart z m p).1) := rfl

theorem n07aChartAngularAngularCoefficient_value
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) :
    (n07aChartAngularAngularCoefficient h04 hz hs m).value =
      mixedDerivative 0 1 (fun p => (K.chart z m p).2) := rfl

end ContinuousFlexibility.Analysis
