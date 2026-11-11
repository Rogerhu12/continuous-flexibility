import ContinuousFlexibility.Analysis.OneHighCylinderVectorCompositionDerivatives
import ContinuousFlexibility.Analysis.OneHighCylinderRealSobolevJets
import ContinuousFlexibility.Analysis.OneHighCylinderRealPureSobolev
import ContinuousFlexibility.Analysis.OneHighPointwiseComposition

/-!
# Uniform multivariable smooth composition on the physical cylinder

The constant depends only on the number of inputs, the requested order,
their prescribed low Fourier bounds, and the outer derivative bounds on a
convex region through zero. The genuine composed function acquires both
L² and finite Sobolev membership from the component input hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set
open scoped ENNReal BigOperators ContDiff

variable {P : ℝ} [Fact (0 < P)] {m : ℕ}

/-- The uniform constant, including the exact order-zero bound. -/
def cylinderVectorCompositionConstant (m s : ℕ) (R : ℝ) (B : ℕ → ℝ) : ℝ :=
  if s = 0 then B 1 else
    (3 : ℝ) ^ s * (B 1 + 2 * circleVectorCompositionCoefficient m s R B)

/-- Multivariable smooth composition with only the stated finite input high
norms. The joint range and zero lie in the same convex derivative-bound
region; all output membership is proved, including on the full radial axis. -/
theorem cylinder_vector_composition_sobolev_le
    (s : ℕ) (u : CylinderSmoothJet P (Fin m → ℝ))
    (hu2 : ∀ i, MemLp ((u.component i).jet 0 0) 2 (cylinderPhysicalMeasure P))
    (hs : ∀ i, (u.component i).MemRealSobolev s (hu2 i))
    (hF1 : ∀ i, MemLp
      (cylinderFourier (cylinderComplexify ((u.component i).jet 0 0))
        (continuous_cylinderComplexify ((u.component i).continuous 0 0))
        (cylinderComplexify_memLp ((u.component i).continuous 0 0) (hu2 i)))
      1 cylinderFrequencyMeasure)
    (Φ : (Fin m → ℝ) → ℝ)
    {S : Set (Fin m → ℝ)} (hS : Convex ℝ S) (h0 : (0 : Fin m → ℝ) ∈ S)
    (huin : ∀ p, u.jet 0 0 p ∈ S)
    (hΦ : ∀ z ∈ S, ContDiffAt ℝ ∞ Φ z)
    {R : ℝ} (hR0 : 0 ≤ R) {B : ℕ → ℝ} (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ z ∈ S, ∀ n, 1 ≤ n → n ≤ max 1 s →
      ‖iteratedFDeriv ℝ n Φ z‖ ≤ B n)
    (hR : ∀ i, cylinderRealFourierL1Norm
      ((u.component i).jet 0 0) ((u.component i).continuous 0 0) (hu2 i) ≤ R) :
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
        cylinderVectorCompositionConstant m s R B *
          ∑ i, cylinderRealSobolevNorm s ((u.component i).jet 0 0)
            ((u.component i).continuous 0 0) (hu2 i) := by
  classical
  let w := cylinderComposition u Φ
  let H := ∑ i, cylinderRealSobolevNorm s ((u.component i).jet 0 0)
    ((u.component i).continuous 0 0) (hu2 i)
  let hΦu : ∀ p, ContDiffAt ℝ ∞ Φ (u.jet 0 0 p) :=
    fun p => hΦ _ (huin p)
  have hws : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => w (p.1, (p.2 : AddCircle P))) :=
    cylinderComposition_contDiff_lift u Φ hΦu
  have hwc : Continuous w := continuous_cylinderComposition u Φ hΦu
  have hdiff (z : Fin m → ℝ) (hz : z ∈ S) : DifferentiableAt ℝ Φ z :=
    (hΦ z hz).differentiableAt (by simp)
  have hfirst (z : Fin m → ℝ) (hz : z ∈ S) : ‖fderiv ℝ Φ z‖ ≤ B 1 := by
    rw [← norm_iteratedFDeriv_one Φ]
    exact hB z hz 1 le_rfl (le_max_left _ _)
  have hv := cylinder_vector_l2_le_components u hu2
  have hinput : (eLpNorm (u.jet 0 0) 2 (cylinderPhysicalMeasure P)).toReal ≤ H := by
    apply hv.2.trans
    exact Finset.sum_le_sum fun i _ =>
      (u.component i).real_derivative_l2_le_sobolev
        (hu2 i) (hs i) (by omega : 0 + 0 ≤ s)
  have hw2 : MemLp w 2 (cylinderPhysicalMeasure P) :=
    composition_sub_base_memLp hS h0 (hB0 1) hdiff hfirst
      (u.continuous 0 0) huin hv.1
  have hbase : (eLpNorm w 2 (cylinderPhysicalMeasure P)).toReal ≤ B 1 * H :=
    (composition_sub_base_LpNorm_le hS h0 (hB0 1) hdiff hfirst
      (u.continuous 0 0) huin hv.1).trans
        (mul_le_mul_of_nonneg_left hinput (hB0 1))
  have hpositive (k : ℕ) (hk : 0 < k) (hks : k ≤ s) (radial : Bool) :
      MemLp (cylinderPureDerivative w radial k) 2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (cylinderPureDerivative w radial k) 2
        (cylinderPhysicalMeasure P)).toReal ≤
        circleVectorCompositionCoefficient m k R B * H :=
    cylinder_vector_composition_pure_l2_le u hu2 hs hF1 Φ hΦu hk hks radial hR0 hB0
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
    simpa only [cylinderVectorCompositionConstant, if_pos rfl, Nat.cast_zero,
      cylinder_real_sobolevNorm_zero_eq_l2, H] using hbase
  · have hrhigh :
        (eLpNorm (cylinderRadialJet w s) 2 (cylinderPhysicalMeasure P)).toReal ≤
          circleVectorCompositionCoefficient m s R B * H := by
      simpa [cylinderPureDerivative] using
        (hpositive s (Nat.pos_of_ne_zero hs0) le_rfl true).2
    have hahigh :
        (eLpNorm (cylinderAngularJet w s) 2 (cylinderPhysicalMeasure P)).toReal ≤
          circleVectorCompositionCoefficient m s R B * H := by
      simpa [cylinderPureDerivative] using
        (hpositive s (Nat.pos_of_ne_zero hs0) le_rfl false).2
    calc
      _ ≤ (3 : ℝ) ^ s *
          ((eLpNorm w 2 (cylinderPhysicalMeasure P)).toReal +
            (eLpNorm (cylinderRadialJet w s) 2 (cylinderPhysicalMeasure P)).toReal +
              (eLpNorm (cylinderAngularJet w s) 2 (cylinderPhysicalMeasure P)).toReal) :=
        hsob.2
      _ ≤ (3 : ℝ) ^ s *
          (B 1 * H + circleVectorCompositionCoefficient m s R B * H +
            circleVectorCompositionCoefficient m s R B * H) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hbase hrhigh) hahigh)
          (by positivity)
      _ = _ := by
        rw [cylinderVectorCompositionConstant, if_neg hs0]
        dsimp only [H]
        ring

end ContinuousFlexibility.Analysis
