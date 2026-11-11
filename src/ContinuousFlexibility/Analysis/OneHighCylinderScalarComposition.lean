import ContinuousFlexibility.Analysis.OneHighCylinderScalarCompositionDerivatives
import ContinuousFlexibility.Analysis.OneHighCylinderRealSobolevJets
import ContinuousFlexibility.Analysis.OneHighCylinderRealPureSobolev
import ContinuousFlexibility.Analysis.OneHighPointwiseComposition

/-!
# Uniform scalar smooth composition on the physical cylinder

The actual composed function and every pure derivative through the finite
requested order acquire L² membership from the input estimate. The Fourier
endpoint comparison then supplies output Sobolev membership and its norm
bound. The outer derivative bounds are imposed on a convex region containing
zero and the input range, including at order zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set
open scoped ENNReal BigOperators ContDiff

variable {P : ℝ} [Fact (0 < P)]

/-- The uniform scalar cylinder composition constant. Only the first through
the `max 1 s`-th outer derivatives are used in the estimate. -/
def cylinderScalarCompositionConstant (s : ℕ) (R : ℝ) (B : ℕ → ℝ) : ℝ :=
  if s = 0 then B 1 else
    (3 : ℝ) ^ s * (B 1 + 2 * circleScalarCompositionCoefficient s R B)

/-- The complete scalar cylinder composition estimate. Its two output
membership assertions are conclusions, including on the noncompact radial
axis. The input requires only the stated finite high norm and Fourier L¹. -/
theorem cylinder_scalar_composition_sobolev_le
    (s : ℕ) (u : CylinderSmoothJet P ℝ)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    (hs : u.MemRealSobolev s hu2)
    (hF1 : MemLp
      (cylinderFourier (cylinderComplexify (u.jet 0 0))
        (continuous_cylinderComplexify (u.continuous 0 0))
        (cylinderComplexify_memLp (u.continuous 0 0) hu2))
      1 cylinderFrequencyMeasure)
    (Φ : ℝ → ℝ)
    {S : Set ℝ} (hS : Convex ℝ S) (h0 : (0 : ℝ) ∈ S)
    (huin : ∀ p, u.jet 0 0 p ∈ S)
    (hΦ : ∀ z ∈ S, ContDiffAt ℝ ∞ Φ z)
    {R : ℝ} {B : ℕ → ℝ} (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ z ∈ S, ∀ n, 1 ≤ n → n ≤ max 1 s →
      ‖iteratedDeriv n Φ z‖ ≤ B n)
    (hR : cylinderRealFourierL1Norm (u.jet 0 0) (u.continuous 0 0) hu2 ≤ R) :
    ∃ hw2 : MemLp (cylinderComposition u Φ) 2 (cylinderPhysicalMeasure P),
      MemLp (frequencyWeighted
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
        (cylinderFourier (cylinderComplexify (cylinderComposition u Φ))
          (continuous_cylinderComplexify
            (continuous_cylinderComposition u Φ (fun p => hΦ _ (huin p))))
          (cylinderComplexify_memLp
            (continuous_cylinderComposition u Φ (fun p => hΦ _ (huin p))) hw2)))
        2 cylinderFrequencyMeasure ∧
      cylinderRealSobolevNorm s (cylinderComposition u Φ)
        (continuous_cylinderComposition u Φ (fun p => hΦ _ (huin p))) hw2 ≤
        cylinderScalarCompositionConstant s R B *
          cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 := by
  let w := cylinderComposition u Φ
  let hΦu : ∀ p, ContDiffAt ℝ ∞ Φ (u.jet 0 0 p) :=
    fun p => hΦ _ (huin p)
  have hws : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => w (p.1, (p.2 : AddCircle P))) :=
    cylinderComposition_contDiff_lift u Φ hΦu
  have hwc : Continuous w := continuous_cylinderComposition u Φ hΦu
  have hdiff (z : ℝ) (hz : z ∈ S) : DifferentiableAt ℝ Φ z :=
    (hΦ z hz).differentiableAt (by simp)
  have hfirst (z : ℝ) (hz : z ∈ S) : ‖fderiv ℝ Φ z‖ ≤ B 1 := by
    rw [← norm_iteratedFDeriv_one Φ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hB z hz 1 le_rfl (le_max_left _ _)
  have hw2 : MemLp w 2 (cylinderPhysicalMeasure P) :=
    composition_sub_base_memLp hS h0 (hB0 1) hdiff hfirst
      (u.continuous 0 0) huin hu2
  have hbase : (eLpNorm w 2 (cylinderPhysicalMeasure P)).toReal ≤
      B 1 * (eLpNorm (u.jet 0 0) 2 (cylinderPhysicalMeasure P)).toReal :=
    composition_sub_base_LpNorm_le hS h0 (hB0 1) hdiff hfirst
      (u.continuous 0 0) huin hu2
  have hbase' : (eLpNorm w 2 (cylinderPhysicalMeasure P)).toReal ≤
      B 1 * cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 :=
    hbase.trans (mul_le_mul_of_nonneg_left
      (u.real_derivative_l2_le_sobolev hu2 hs (by omega : 0 + 0 ≤ s)) (hB0 1))
  have hpositive (k : ℕ) (hk : 0 < k) (hks : k ≤ s) (radial : Bool) :
      MemLp (cylinderPureDerivative w radial k) 2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (cylinderPureDerivative w radial k) 2
        (cylinderPhysicalMeasure P)).toReal ≤
        circleScalarCompositionCoefficient k R B *
          cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 :=
    cylinder_scalar_composition_pure_l2_le u hu2 hs hF1 Φ hΦu hk hks radial hB0
      (fun p n hn hnk =>
        hB _ (huin p) n hn (hnk.trans (hks.trans (le_max_right _ _)))) hR
  have hpure (radial : Bool) (k : ℕ) (hks : k ≤ s) :
      MemLp (cylinderPureDerivative w radial k) 2 (cylinderPhysicalMeasure P) := by
    by_cases hk : k = 0
    · subst k
      simpa only [cylinderPureDerivative_zero] using hw2
    · exact (hpositive k (Nat.pos_of_ne_zero hk) hks radial).1
  have hsob := cylinder_real_sobolev_of_pure_derivatives s w hwc hw2
    (cylinderRadialJet w) (cylinderAngularJet w)
    (continuous_cylinderRadialJet hws) (continuous_cylinderAngularJet hws)
    (cylinderRadialJet_zero w) (cylinderAngularJet_zero w)
    (fun k θ x => cylinderRadialJet_hasDerivAt hws k x θ)
    (fun k x y => cylinderAngularJet_hasDerivAt hws k x y)
    (fun k hk => by simpa [cylinderPureDerivative] using hpure true k hk)
    (fun k hk => by simpa [cylinderPureDerivative] using hpure false k hk)
  refine ⟨hw2, hsob.1, ?_⟩
  by_cases hs0 : s = 0
  · subst s
    simpa [cylinderScalarCompositionConstant, cylinder_real_sobolevNorm_zero_eq_l2]
      using hbase
  · have hrhigh :
        (eLpNorm (cylinderRadialJet w s) 2 (cylinderPhysicalMeasure P)).toReal ≤
          circleScalarCompositionCoefficient s R B *
            cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 := by
      simpa [cylinderPureDerivative] using
        (hpositive s (Nat.pos_of_ne_zero hs0) le_rfl true).2
    have hahigh :
        (eLpNorm (cylinderAngularJet w s) 2 (cylinderPhysicalMeasure P)).toReal ≤
          circleScalarCompositionCoefficient s R B *
            cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 := by
      simpa [cylinderPureDerivative] using
        (hpositive s (Nat.pos_of_ne_zero hs0) le_rfl false).2
    calc
      _ ≤ (3 : ℝ) ^ s *
          ((eLpNorm w 2 (cylinderPhysicalMeasure P)).toReal +
            (eLpNorm (cylinderRadialJet w s) 2 (cylinderPhysicalMeasure P)).toReal +
              (eLpNorm (cylinderAngularJet w s) 2 (cylinderPhysicalMeasure P)).toReal) :=
        hsob.2
      _ ≤ (3 : ℝ) ^ s *
          (B 1 * cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 +
            circleScalarCompositionCoefficient s R B *
              cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 +
            circleScalarCompositionCoefficient s R B *
              cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hbase' hrhigh) hahigh)
          (by positivity)
      _ = _ := by
        rw [cylinderScalarCompositionConstant, if_neg hs0]
        ring

end ContinuousFlexibility.Analysis
