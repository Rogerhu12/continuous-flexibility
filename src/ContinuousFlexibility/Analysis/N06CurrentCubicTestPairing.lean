import ContinuousFlexibility.Analysis.N06OpenCubicPairing
import ContinuousFlexibility.Analysis.N06CurrentShiftedTestLp
import ContinuousFlexibility.Analysis.N06AngularMeanBridge

/-!
# The cubic weak equation paired with actual current physical tests

N04's closed forward-chart bounds supply all actual transformed L2 test
jets. Their cubic graph fields are therefore in the same piece space.
The open-strip cutoff argument applies to the true height transform,
including the half-period average of every full-period physical test.
There is no hypothesis about the totalized inverse at a radial endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Every continuous radial weight is bounded on the actual unit piece. -/
theorem n06_unit_radialWeight_mul_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hl : K.left m = 0) (hr : K.right m = 1)
    {w : ℝ → ℝ} (hw : Continuous w) {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (canonicalMeasure S K m)) :
    MemLp (fun p => w p.1 * f p) 2 (canonicalMeasure S K m) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (show ContinuousOn (fun x : ℝ => ‖w x‖) (Icc (0 : ℝ) 1) from hw.norm.continuousOn)
  apply (hf.const_mul |B|).of_le
    ((hw.comp continuous_fst).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  have hpr : p.1 ∈ Icc (0 : ℝ) 1 := by
    simpa only [hl, hr] using Ioo_subset_Icc_self hp.1
  have hb : ‖w p.1‖ ≤ |B| := (hB ⟨p.1, hpr, rfl⟩).trans (le_abs_self B)
  calc
    ‖w p.1 * f p‖ = ‖w p.1‖ * ‖f p‖ := norm_mul _ _
    _ ≤ |B| * ‖f p‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = ‖|B| * f p‖ := by simp only [norm_mul, Real.norm_eq_abs, abs_abs]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- All five graph fields of the true current test are in the original
piece L2 space. Their integrability is derived from the forward chart. -/
theorem n06_current_cubicGraphTest_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hl : K.left m = 0) (hr : K.right m = 1)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 5) :
    MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1)
      (canonicalHeight S K z m φ) i) 2 (canonicalMeasure S K m) := by
  have hrr := n06_current_canonicalHeight_directionalJets_memLp h04 hz hs m (1, 0) (1, 0) hφ
  have hrt := n06_current_canonicalHeight_directionalJets_memLp h04 hz hs m (1, 0) (0, 1) hφ
  have htt := n06_current_canonicalHeight_directionalJets_memLp h04 hz hs m (0, 1) (0, 1) hφ
  have hd : Continuous cylinderWeight := by
    change Continuous (fun x : ℝ => x * (1 - x))
    exact continuous_id.mul (continuous_const.sub continuous_id)
  fin_cases i
  · exact n06_unit_radialWeight_mul_memLp hl hr (hd.pow 2) hrr.2
  · exact n06_unit_radialWeight_mul_memLp hl hr ((hd.pow 2).mul hd.sqrt) hrt.2
  · exact n06_unit_radialWeight_mul_memLp hl hr (hd.pow 3) htt.2
  · exact n06_unit_radialWeight_mul_memLp hl hr hd hrr.1
  · exact n06_unit_radialWeight_mul_memLp hl hr (hd.mul hd.sqrt) htt.1

theorem n06_current_canonicalHeight_periodic_on
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {φ : PolarPoint → ℝ} (hφp : Function.Periodic φ (0, Real.pi))
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K z m φ (p + (0, Real.pi)) = canonicalHeight S K z m φ p := by
  have he : (fun q => φ (q + (0, Real.pi))) = φ := funext hφp
  simpa only [Nat.cast_one, one_mul, he] using
    (n06_current_canonicalHeight_shift h04 hz hs m φ 1 hp).symm

/-- A genuine compact canonical cubic equation holds against the actual
current height transform of any smooth half-periodic physical test. -/
theorem n06_cubic_pairing_actual_current_test
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hl : K.left m = 0) (hr : K.right m = 1)
    {A B Cc : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ Cc (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |Cc p| ≤ δ ∧
        |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ ∧
        |radialPartial B p| ≤ δ ∧ |angularPartial Cc p| ≤ δ)
    (u g : CanonicalL2 S K m)
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u p * divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) A B Cc) ψ p
            ∂canonicalMeasure S K m)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, g p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) =
      ∫ p, u p * divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B Cc)
          (canonicalHeight S K z m φ) p ∂canonicalMeasure S K m :=
  n06_cubic_pairing_of_openTest hl hr hδ hA hB hC hjet u g hweak
    (n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ)
    (fun _ hp => n06_current_canonicalHeight_periodic_on h04 hz hs m hφp hp)
    (n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn)
    (n06_current_canonicalHeight_directionalJets_memLp h04 hz hs m (1, 0) (1, 0) hφ).1
    (n06_current_canonicalHeight_directionalJets_memLp h04 hz hs m (0, 1) (0, 1) hφ).1
    (n06_current_cubicGraphTest_memLp h04 hz hs m hl hr hφ)

/-- The exact half-period average used in the full physical pairing is
an admissible actual cubic test, even when the original test has only
the full physical angular period. -/
theorem n06_cubic_pairing_actual_fullPhysical_test
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hl : K.left m = 0) (hr : K.right m = 1)
    {A B Cc : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hC : ContDiffOn ℝ ∞ Cc (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |Cc p| ≤ δ ∧
        |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ ∧
        |radialPartial B p| ≤ δ ∧ |angularPartial Cc p| ≤ δ)
    (u g : CanonicalL2 S K m)
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u p * divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) A B Cc) ψ p
            ∂canonicalMeasure S K m)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    (∫ p, g p * canonicalHeight S K z m (n06_radialTestAverage φ) p
      ∂canonicalMeasure S K m) =
      ∫ p, u p * divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B Cc)
          (canonicalHeight S K z m (n06_radialTestAverage φ)) p ∂canonicalMeasure S K m :=
  n06_cubic_pairing_actual_current_test h04 hz hs m hl hr hδ hA hB hC hjet u g hweak
    (n06_radialTestAverage_test hφ).1 (n06_radialTestAverage_periodic hφ.2.1)

end ContinuousFlexibility.Statements
