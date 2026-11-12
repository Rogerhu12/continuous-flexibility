import ContinuousFlexibility.Analysis.N06CurrentPositiveOperatorTest
import ContinuousFlexibility.Analysis.N06CurrentPositiveFiniteGreen
import ContinuousFlexibility.Analysis.N06CurrentCubicTestPairing

/-!
# Actual positive relative source pairings

The same compact cubic source equation extends to the actual current
physical test. Combining it with the true potential difference and the
current operator identity gives the physical relative source, with the
signs required by the original equation. For the finite modes of the
existing weak graph package, the remaining term is exactly the reference
Green boundary term. No boundary trace of an infinite sum is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

/-- The actual potential difference multiplies the original L2 field.
Its reference factor is identified by the literal radial coefficient
formula, and its current factor uses the original N04 order-zero bound. -/
theorem n06_positive_potentialDifference_mul_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {V : ℝ → ℝ} (hV : Continuous V)
    (heV : EqOn (K.potential (C.referenceState, 0) m)
      (fun q => V q.1) (canonicalOpen S K m))
    {U : PolarPoint → ℝ} (hU : MemLp U 2 (canonicalMeasure S K m)) :
    MemLp (fun p => (K.potential z m p - K.potential (C.referenceState, 0) m p) * U p)
      2 (canonicalMeasure S K m) := by
  have hcur := n06_actualPotential_mul_memLp h04 hz hs m hU
  have href := n06_canonical_radialWeight_mul_memLp hV hU
  apply (memLp_congr_ae ?_).mpr (hcur.sub href)
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  simp only [Pi.sub_apply, heV ⟨hp.1, mem_univ _⟩]
  ring

/-- The actual compact cubic source identity also applies to a chosen
L2 representative, as required for the literal finite modal synthesis. -/
theorem n06_cubic_pairing_actual_current_test_of_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hl : K.left m = 0) (hr : K.right m = 1)
    {A B Cc : PolarPoint → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ A (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ B (canonicalOpen S K m))
    (hCc : ContDiffOn ℝ ∞ Cc (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |A p| ≤ δ ∧ |B p| ≤ δ ∧ |Cc p| ≤ δ ∧
        |radialPartial A p| ≤ δ ∧ |angularPartial B p| ≤ δ ∧
        |radialPartial B p| ≤ δ ∧ |angularPartial Cc p| ≤ δ)
    {U : PolarPoint → ℝ} (hU : MemLp U 2 (canonicalMeasure S K m))
    (g : CanonicalL2 S K m)
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, U p * divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) A B Cc) ψ p
            ∂canonicalMeasure S K m)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, g p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) =
      ∫ p, U p * divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B Cc)
          (canonicalHeight S K z m φ) p ∂canonicalMeasure S K m := by
  let u : CanonicalL2 S K m := hU.toLp U
  have hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] U := hU.coeFn_toLp
  have hw : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u p * divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) A B Cc) ψ p
            ∂canonicalMeasure S K m := by
    intro ψ hψ
    rw [hweak ψ hψ]
    apply integral_congr_ae
    filter_upwards [hu] with p hp
    rw [hp]
  rw [n06_cubic_pairing_actual_current_test h04 hz hs m hl hr hδ hA hB hCc hjet
    u g hw hφ hφp]
  apply integral_congr_ae
  filter_upwards [hu] with p hp
  rw [hp]

/-- The physical relative source is `-F + cubic - potentialDifference*U`.
Its actual current test pairing leaves precisely the reference Green
expression, with no imposed endpoint vanishing or matching condition. -/
theorem n06_positive_current_relative_pairing
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true) (hl : K.left m = 0) (hr : K.right m = 1)
    {a c V : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V)
    (hcd : ∀ y ∈ Ioo (K.left m) (K.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun q => a q.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun q => c q.1) (canonicalOpen S K m))
    (heV : EqOn (K.potential (C.referenceState, 0) m)
      (fun q => V q.1) (canonicalOpen S K m))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ (K.dividedDifference z m).a (canonicalOpen S K m))
    (hB : ContDiffOn ℝ ∞ (K.dividedDifference z m).b (canonicalOpen S K m))
    (hCc : ContDiffOn ℝ ∞ (K.dividedDifference z m).c (canonicalOpen S K m))
    (hjet : ∀ p ∈ canonicalOpen S K m,
      |(K.dividedDifference z m).a p| ≤ δ ∧ |(K.dividedDifference z m).b p| ≤ δ ∧
        |(K.dividedDifference z m).c p| ≤ δ ∧
        |radialPartial (K.dividedDifference z m).a p| ≤ δ ∧
        |angularPartial (K.dividedDifference z m).b p| ≤ δ ∧
        |radialPartial (K.dividedDifference z m).b p| ≤ δ ∧
        |angularPartial (K.dividedDifference z m).c p| ≤ δ)
    {U F : PolarPoint → ℝ} (hU : MemLp U 2 (canonicalMeasure S K m))
    (hF : MemLp F 2 (canonicalMeasure S K m)) (g : CanonicalL2 S K m)
    (hweak : ∀ ψ, CanonicalTest S K m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, U p * divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) (K.dividedDifference z m).a
            (K.dividedDifference z m).b (K.dividedDifference z m).c) ψ p
              ∂canonicalMeasure S K m)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, (-F p + g p -
        (K.potential z m p - K.potential (C.referenceState, 0) m p) * U p) *
          canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      (∫ p, U p * canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p
        ∂canonicalMeasure S K m) =
      (∫ p, U p * n06UnitReferenceTestOperator a c V (canonicalHeight S K z m φ) p
        ∂canonicalMeasure S K m) -
        ∫ p, F p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m := by
  let W := canonicalHeight S K z m φ
  let A := n06CubicCoefficients (fun q => cylinderWeight q.1) (K.dividedDifference z m).a
    (K.dividedDifference z m).b (K.dividedDifference z m).c
  let ΔV : PolarPoint → ℝ := fun p => K.potential z m p - K.potential (C.referenceState, 0) m p
  have hW : MemLp W 2 (canonicalMeasure S K m) :=
    n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hPW := n06_currentHeight_positiveOperator_memLp h04 hz hs hφ ha hc hV (m := m)
  have hDW : MemLp (divergenceOperator A W) 2 (canonicalMeasure S K m) :=
    n06_cubic_openTest_memLp_of_graph hl hr hδ hA hB hCc hjet
      (n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ)
      (n06_current_cubicGraphTest_memLp h04 hz hs m hl hr hφ)
  have hDU : MemLp (fun p => ΔV p * U p) 2 (canonicalMeasure S K m) :=
    n06_positive_potentialDifference_mul_memLp h04 hz hs hV heV hU
  have hDW₀ : MemLp (fun p => ΔV p * W p) 2 (canonicalMeasure S K m) :=
    n06_positive_potentialDifference_mul_memLp h04 hz hs hV heV hW
  have hEq : canonicalSource S K z m (divergenceOperator (L.coefficients z) φ)
      =ᵐ[canonicalMeasure S K m] fun p =>
        -n06UnitReferenceTestOperator a c V W p + divergenceOperator A W p - ΔV p * W p := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hpU : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    have hn := (isOpen_Ioo.prod isOpen_univ).mem_nhds hpU
    exact n06_positive_current_operatorTest_difference h04 hz hs hm hl hr ha hea heb hec heV
      hφ hpU (hcd p.1 hp.1) ((hA.contDiffAt hn).differentiableAt (by simp))
      ((hB.contDiffAt hn).differentiableAt (by simp))
      ((hCc.contDiffAt hn).differentiableAt (by simp))
  have hLW : MemLp (canonicalSource S K z m (divergenceOperator (L.coefficients z) φ))
      2 (canonicalMeasure S K m) :=
    (memLp_congr_ae hEq).mpr ((hPW.neg.add hDW).sub hDW₀)
  have hsource : MemLp (fun p => -F p + g p - ΔV p * U p)
      2 (canonicalMeasure S K m) := (hF.neg.add (Lp.memLp g)).sub hDU
  have hI : Integrable (fun p => (-F p + g p - ΔV p * U p) * W p)
      (canonicalMeasure S K m) := hsource.integrable_mul hW
  have hJ : Integrable (fun p => U p *
      canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p)
      (canonicalMeasure S K m) := hU.integrable_mul hLW
  have hUP : Integrable (fun p => U p * n06UnitReferenceTestOperator a c V W p)
      (canonicalMeasure S K m) := hU.integrable_mul hPW
  have hFW : Integrable (fun p => F p * W p) (canonicalMeasure S K m) := hF.integrable_mul hW
  have hgW : Integrable (fun p => g p * W p) (canonicalMeasure S K m) :=
    (Lp.memLp g).integrable_mul hW
  have hUC : Integrable (fun p => U p * divergenceOperator A W p)
      (canonicalMeasure S K m) := hU.integrable_mul hDW
  have hcubic : (∫ p, g p * W p ∂canonicalMeasure S K m) =
      ∫ p, U p * divergenceOperator A W p ∂canonicalMeasure S K m :=
    n06_cubic_pairing_actual_current_test_of_memLp h04 hz hs hl hr hδ hA hB hCc hjet
      hU g hweak hφ hφp
  calc
    _ = ∫ p, ((U p * n06UnitReferenceTestOperator a c V W p - F p * W p) +
        (g p * W p - U p * divergenceOperator A W p)) ∂canonicalMeasure S K m := by
      rw [← integral_sub hI hJ]
      apply integral_congr_ae
      filter_upwards [hEq] with p hp
      rw [hp]
      ring
    _ = ((∫ p, U p * n06UnitReferenceTestOperator a c V W p ∂canonicalMeasure S K m) -
        ∫ p, F p * W p ∂canonicalMeasure S K m) +
        ((∫ p, g p * W p ∂canonicalMeasure S K m) -
          ∫ p, U p * divergenceOperator A W p ∂canonicalMeasure S K m) := by
      have hleft : Integrable (fun p => U p * n06UnitReferenceTestOperator a c V W p -
          F p * W p) (canonicalMeasure S K m) := hUP.sub hFW
      have hright : Integrable (fun p => g p * W p - U p * divergenceOperator A W p)
          (canonicalMeasure S K m) := hgW.sub hUC
      rw [integral_add hleft hright, integral_sub hUP hFW,
        integral_sub hgW hUC]
    _ = _ := by rw [hcubic, sub_self, add_zero]

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The same weak graph package and the actual cubic source give finite
current physical Green. The boundary sign is now right minus left,
matching the physical divergence convention on negative pieces. -/
theorem N06UnitWeakGraphData.current_positive_relative_finite_green
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {Kc : CanonicalData S}
    {base loss b m : ℕ} {ε κ : ℝ} {z : AnnularState S × ℝ}
    {a c V : ℝ → ℝ} {φ : PolarPoint → ℝ}
    {U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m)}
    (P : N06UnitWeakGraphData a c V U F κ)
    (Q : N06CurrentHeightTestTraces S Kc z m φ)
    (h04 : N04Properties D T S C L Kc base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : Kc.positive m = true) (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V)
    (hcd : ∀ y ∈ Ioo (Kc.left m) (Kc.right m), DifferentiableAt ℝ c y)
    (hea : EqOn (Kc.coefficients (C.referenceState, 0) m).a
      (fun q => a q.1) (canonicalOpen S Kc m))
    (heb : EqOn (Kc.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S Kc m))
    (hec : EqOn (Kc.coefficients (C.referenceState, 0) m).c
      (fun q => c q.1) (canonicalOpen S Kc m))
    (heV : EqOn (Kc.potential (C.referenceState, 0) m)
      (fun q => V q.1) (canonicalOpen S Kc m))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ContDiffOn ℝ ∞ (Kc.dividedDifference z m).a (canonicalOpen S Kc m))
    (hB : ContDiffOn ℝ ∞ (Kc.dividedDifference z m).b (canonicalOpen S Kc m))
    (hCc : ContDiffOn ℝ ∞ (Kc.dividedDifference z m).c (canonicalOpen S Kc m))
    (hjet : ∀ p ∈ canonicalOpen S Kc m,
      |(Kc.dividedDifference z m).a p| ≤ δ ∧ |(Kc.dividedDifference z m).b p| ≤ δ ∧
        |(Kc.dividedDifference z m).c p| ≤ δ ∧
        |radialPartial (Kc.dividedDifference z m).a p| ≤ δ ∧
        |angularPartial (Kc.dividedDifference z m).b p| ≤ δ ∧
        |radialPartial (Kc.dividedDifference z m).b p| ≤ δ ∧
        |angularPartial (Kc.dividedDifference z m).c p| ≤ δ)
    (s : Finset ℕ) (g : CanonicalL2 S Kc m)
    (hweak : ∀ ψ, CanonicalTest S Kc m ψ →
      (∫ p, g p * ψ p ∂canonicalMeasure S Kc m) =
        ∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p * divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) (Kc.dividedDifference z m).a
            (Kc.dividedDifference z m).b (Kc.dividedDifference z m).c) ψ p
              ∂canonicalMeasure S Kc m)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, (-r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis p +
        g p - (Kc.potential z m p - Kc.potential (C.referenceState, 0) m p) *
          r11bFiniteSynthesis s P.modes referenceAngularBasis p) * canonicalHeight S Kc z m φ p
            ∂canonicalMeasure S Kc m) -
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
        canonicalSource S Kc z m (divergenceOperator (L.coefficients z) φ) p
          ∂canonicalMeasure S Kc m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a 1 * (Q.value (1, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (1, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (1, θ) * Q.radial (1, θ)) -
        a 0 * (Q.value (0, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (0, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (0, θ) * Q.radial (0, θ)) := by
  have hU : MemLp (r11bFiniteSynthesis s P.modes referenceAngularBasis)
      2 (canonicalMeasure S Kc m) := by
    apply memLp_finsetSum s
    intro i _
    have hv : MemLp (P.modes i) 2 (volume.restrict (Ioo (Kc.left m) (Kc.right m))) := by
      simpa only [hl, hr] using (P.representative i).memLp
    exact n06_canonical_tensor_memLp hv (contDiff_referenceAngularBasis i).continuous
  have hF : MemLp (r11bFiniteSynthesis s (n06HalfCosineCoefficient (F 0)) referenceAngularBasis)
      2 (canonicalMeasure S Kc m) := by
    apply memLp_finsetSum s
    intro i _
    have hf := (n06_canonical_angularCoefficient_memLp (F 0)
      (memLp_angleMeasure_of_continuous (contDiff_referenceAngularBasis i).continuous)).const_mul
        Real.pi⁻¹
    exact n06_canonical_tensor_memLp hf (contDiff_referenceAngularBasis i).continuous
  rw [n06_positive_current_relative_pairing h04 hz hs hm hl hr ha hc hV hcd hea heb hec heV
    hδ hA hB hCc hjet hU hF g hweak hφ hφp]
  have hg := P.current_positive_finite_green Q hl hr h04 hz hs hφ hφp ha hc hV s
  have hsign : (∫ θ in (0 : ℝ)..Real.pi,
      a 1 * (Q.value (1, θ) *
        radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (1, θ) -
          r11bFiniteSynthesis s P.modes referenceAngularBasis (1, θ) * Q.radial (1, θ)) -
      a 0 * (Q.value (0, θ) *
        radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (0, θ) -
          r11bFiniteSynthesis s P.modes referenceAngularBasis (0, θ) * Q.radial (0, θ))) =
      -(∫ θ in (0 : ℝ)..Real.pi,
        a 0 * (Q.value (0, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (0, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (0, θ) * Q.radial (0, θ)) -
        a 1 * (Q.value (1, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (1, θ) -
            r11bFiniteSynthesis s P.modes referenceAngularBasis (1, θ) * Q.radial (1, θ))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [hsign]
  linarith only [hg]

end ContinuousFlexibility.Analysis
