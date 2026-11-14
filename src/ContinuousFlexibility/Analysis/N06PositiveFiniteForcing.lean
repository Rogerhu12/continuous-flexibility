module

public import ContinuousFlexibility.Analysis.N06CompactCanonicalTraces
public import ContinuousFlexibility.Analysis.N06CurrentPositiveFiniteGreen
public import ContinuousFlexibility.Analysis.N06CanonicalTestSeparation

/-!
# Finite positive height determines the actual finite forcing

The existing finite H2 Green identity is applied to the true pullback of
a compact canonical test. The true endpoint traces vanish, so it gives
the compact weak equation of the finite modal synthesis. If that finite
synthesis represents the original height, separation of the original L2
test pairings identifies the entire forcing with its finite synthesis.
No finite-support assumption on the raw source or compatibility column
is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss b m : ℕ} {ε κ : ℝ} {z : AnnularState S × ℝ}
  {a c V : ℝ → ℝ}
  {U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)}

/-- The finite modal ODEs imply the actual compact canonical weak
equation, by the already proved closed Green formula and true traces. -/
theorem N06UnitWeakGraphData.finite_reference_weak
    (P : N06UnitWeakGraphData a c V U F κ)
    (hl : K.left m = 0) (hr : K.right m = 1)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V)
    (s : Finset ℕ) {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
      n06UnitReferenceTestOperator a c V φ p ∂canonicalMeasure S K m) =
      ∫ p, r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis p *
        φ p ∂canonicalMeasure S K m := by
  let Φ := n06CanonicalTestPullback S K z m φ
  have hΦ := n06_canonicalTest_transport h04 hz hs hφ
  obtain ⟨Q⟩ := n06_currentHeightTest_exists_traces h04 hz hs m hΦ.1.1
  have htrace := Q.compactPullback_closed h04 hz hs hφ
  have hg := P.current_positive_finite_green Q hl hr h04 hz hs hΦ.1.1 hΦ.2.1 ha hc hV s
  have hvalue :
      (∫ p, r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis p *
        canonicalHeight S K z m Φ p ∂canonicalMeasure S K m) =
      ∫ p, r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis p *
        φ p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [(n06CanonicalTestPullback_height_germ h04 hz hs
      (φ := φ) ⟨hp.1, mem_univ _⟩).eq_of_nhds]
  have hoperator :
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m Φ) p
          ∂canonicalMeasure S K m) =
      ∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
        n06UnitReferenceTestOperator a c V φ p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [n06UnitReferenceTestOperator_input_congr_germ a c V
      (n06CanonicalTestPullback_height_germ h04 hz hs (φ := φ) ⟨hp.1, mem_univ _⟩)]
  have hzero (y : ℝ) (hy : y ∈ Icc (K.left m) (K.right m))
      (hyo : y ∉ Ioo (K.left m) (K.right m)) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
      Q.value (y, θ) = 0 ∧ Q.radial (y, θ) = 0 := by
    rw [htrace.1 ⟨hy, hθ⟩, htrace.2 ⟨hy, hθ⟩]
    exact hφ.n06_value_radial_zero_of_not_mem hyo θ
  have hboundary :
      (∫ θ in (0 : ℝ)..Real.pi,
        a 0 * (Q.value (0, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (0, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (0, θ) * Q.radial (0, θ)) -
        a 1 * (Q.value (1, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (1, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (1, θ) * Q.radial (1, θ))) = 0 := by
    calc
      _ = ∫ _θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        have ht : θ ∈ Icc (0 : ℝ) Real.pi := by
          simpa only [uIcc_of_le Real.pi_pos.le] using hθ
        have h₀ := hzero 0 (by simp only [hl, hr, mem_Icc]; norm_num)
          (by simp only [hl, hr, mem_Ioo]; norm_num) θ ht
        have h₁ := hzero 1 (by simp only [hl, hr, mem_Icc]; norm_num)
          (by simp only [hl, hr, mem_Ioo]; norm_num) θ ht
        simp only [h₀.1, h₀.2, h₁.1, h₁.2, zero_mul, mul_zero, sub_self, sub_zero]
      _ = 0 := by simp
  change
    (∫ p, r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis p *
        canonicalHeight S K z m Φ p ∂canonicalMeasure S K m) -
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
        n06UnitReferenceTestOperator a c V (canonicalHeight S K z m Φ) p
          ∂canonicalMeasure S K m) = _ at hg
  rw [hvalue, hoperator, hboundary] at hg
  exact (sub_eq_zero.mp hg).symm

/-- A finite actual height and the original compact weak equation force
the same finite forcing. This identifies the original L2 class, rather
than merely assuming its angular support. -/
theorem N06UnitWeakGraphData.forcing_eq_finite_of_height
    (P : N06UnitWeakGraphData a c V U F κ)
    (hl : K.left m = 0) (hr : K.right m = 1)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V)
    (s : Finset ℕ)
    (hvalue : (U 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s P.modes referenceAngularBasis)
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, U 0 p * n06UnitReferenceTestOperator a c V φ p ∂canonicalMeasure S K m) =
        ∫ p, F 0 p * φ p ∂canonicalMeasure S K m) :
    (F 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis := by
  have hf : MemLp (r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis)
      2 (canonicalMeasure S K m) := by
    unfold r11bFiniteSynthesis
    exact memLp_finsetSum s (fun i _ => n06_canonical_tensor_memLp
      ((n06_canonical_angularCoefficient_memLp (F 0)
        (memLp_angleMeasure_of_continuous (contDiff_referenceAngularBasis i).continuous)).const_mul
          Real.pi⁻¹) (contDiff_referenceAngularBasis i).continuous)
  let G : CanonicalL2 S K m := hf.toLp
    (r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis)
  have hG : (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis := hf.coeFn_toLp
  have he : F 0 = G := by
    apply n06_canonicalL2_test_ext
    intro φ hφ
    calc
      (∫ p, F 0 p * φ p ∂canonicalMeasure S K m) =
          ∫ p, U 0 p * n06UnitReferenceTestOperator a c V φ p ∂canonicalMeasure S K m :=
        (hweak φ hφ).symm
      _ = ∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
          n06UnitReferenceTestOperator a c V φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hvalue] with p hp
        rw [hp]
      _ = ∫ p, r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis p *
          φ p ∂canonicalMeasure S K m :=
        P.finite_reference_weak hl hr h04 hz hs ha hc hV s hφ
      _ = ∫ p, G p * φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hG] with p hp
        rw [hp]
  have hFG : (F 0 : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] (G : PolarPoint → ℝ) :=
    Eventually.of_forall (fun p => congrArg (fun v : CanonicalL2 S K m => v p) he)
  exact hFG.trans hG

end ContinuousFlexibility.Analysis
