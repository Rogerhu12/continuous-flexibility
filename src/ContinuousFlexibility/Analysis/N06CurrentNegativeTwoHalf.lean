module

public import ContinuousFlexibility.Analysis.N06CurrentNegativePairing
public import ContinuousFlexibility.Analysis.N06FullCanonicalPairing

/-!
# The true two-half negative Green identity

An arbitrary original full-period radial test is averaged only after the
two actual source transforms have been retained. The difference between
averaging `L phi` and applying `L` to the averaged test is exactly the
actual potential translation defect. This file keeps that term explicitly;
it does not assume periodicity of the bare physical operator or potential.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem halfSum_fderiv {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (v : PolarPoint) :
    fderiv ℝ (fun q => (f q + g q) / 2) p v =
      (fderiv ℝ f p v + fderiv ℝ g p v) / 2 := by
  have he : (fun q => (f q + g q) / 2) =
      fun q => (1 / 2 : ℝ) * (f q + g q) := by
    funext q
    ring
  have hsum : DifferentiableAt ℝ (fun q => f q + g q) p := hf.add hg
  rw [he, fderiv_const_mul hsum (1 / 2), fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  ring

private theorem halfSum_second_on {Ω : Set PolarPoint} (hΩ : IsOpen Ω)
    {f g : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    {p : PolarPoint} (hp : p ∈ Ω) (v w : PolarPoint) :
    fderiv ℝ (fun q => fderiv ℝ (fun t => (f t + g t) / 2) q v) p w =
      (fderiv ℝ (fun q => fderiv ℝ f q v) p w +
        fderiv ℝ (fun q => fderiv ℝ g q v) p w) / 2 := by
  have he : (fun q => fderiv ℝ (fun t => (f t + g t) / 2) q v) =ᶠ[𝓝 p]
      fun q => (fderiv ℝ f q v + fderiv ℝ g q v) / 2 := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact halfSum_fderiv ((hf.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp))
      ((hg.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp)) v
  have hf₁ : DifferentiableAt ℝ (fun q => fderiv ℝ f q v) p :=
    (((hf.contDiffAt (hΩ.mem_nhds hp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  have hg₁ : DifferentiableAt ℝ (fun q => fderiv ℝ g q v) p :=
    (((hg.contDiffAt (hΩ.mem_nhds hp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  exact (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A w) (he.fderiv_eq (𝕜 := ℝ))).trans
    (halfSum_fderiv hf₁ hg₁ w)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The negative principal expression commutes with the actual physical
test average on the open canonical strip. Only local derivatives occur. -/
theorem n06_currentHeight_negativePrincipal_average
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    n06NegativePrincipalTest (canonicalHeight S K z m (n06_radialTestAverage φ)) p =
      (n06NegativePrincipalTest (canonicalHeight S K z m φ) p +
        n06NegativePrincipalTest (canonicalHeight S K z m
          (fun q => φ (q + (0, Real.pi)))) p) / 2 := by
  have h₀ := n06_current_canonicalHeight_contDiffOn h04 hz hs m hφ
  have h₁ : ContDiffOn ℝ ∞
      (canonicalHeight S K z m (fun q => φ (q + (0, Real.pi)))) (canonicalOpen S K m) :=
    n06_current_canonicalHeight_contDiffOn h04 hz hs m
      (hφ.comp (contDiff_id.add contDiff_const))
  rw [n06_canonicalHeight_average]
  unfold n06NegativePrincipalTest radialPartial angularPartial
  rw [halfSum_second_on (isOpen_Ioo.prod isOpen_univ) h₀ h₁ hp (1, 0) (1, 0),
    halfSum_second_on (isOpen_Ioo.prod isOpen_univ) h₀ h₁ hp (0, 1) (0, 1)]
  ring

/-- The literal translation defect, with its sign chosen for Green's
pairing. It vanishes if the actual potential is pi-periodic on the strip. -/
def n06NegativeHalfPeriodDefect (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (φ : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  (K.potential z m p - K.potential z m (p + (0, Real.pi))) *
    canonicalHeight S K z m (fun q => φ (q + (0, Real.pi))) p / 2

/-- The two true physical half-period source transforms differ from
the operator on the averaged test by exactly the displayed potential
defect. Neither the test nor the physical operator is assumed pi-periodic. -/
theorem n06_negative_current_twoHalf_source
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : RadialTest D φ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p =
      canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p -
      n06NegativeHalfPeriodDefect S K z m φ p := by
  have h₀ : canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p =
      n06NegativePrincipalTest (canonicalHeight S K z m φ) p +
        K.potential z m p * canonicalHeight S K z m φ p :=
    n06_negative_current_operatorTest_eq h04 hz hs m hm hφ.1 hp
  have h₁ : canonicalSource S K z m
      (fun q => divergenceOperator (L.coefficients z) φ (q + (0, Real.pi))) p =
      n06NegativePrincipalTest (canonicalHeight S K z m
        (fun q => φ (q + (0, Real.pi)))) p +
      K.potential z m (p + (0, Real.pi)) *
        canonicalHeight S K z m (fun q => φ (q + (0, Real.pi))) p := by
    simpa only [Nat.cast_one, one_mul, n06NegativePrincipalTest] using
      n06_negative_current_shifted_operatorTest_eq h04 hz hs m 1 hm hφ.1 hp
  have ha : canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p =
      n06NegativePrincipalTest (canonicalHeight S K z m (n06_radialTestAverage φ)) p +
      K.potential z m p * canonicalHeight S K z m (n06_radialTestAverage φ) p :=
    n06_negative_current_operatorTest_eq h04 hz hs m hm (n06_radialTestAverage_test hφ).1 hp
  rw [n06_canonicalSource_average]
  change (canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p +
    canonicalSource S K z m (fun q => divergenceOperator (L.coefficients z) φ
      (q + (0, Real.pi))) p) / 2 = _
  rw [h₀, h₁, ha, n06_currentHeight_negativePrincipal_average h04 hz hs hφ.1 hp,
    n06_canonicalHeight_average]
  unfold n06NegativeHalfPeriodDefect
  ring

/-- The actual potential translation defect is L2. This follows from
the two genuine operator tests, so no unproved shifted measurability of
the potential is introduced. -/
theorem n06_negativeHalfPeriodDefect_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : RadialTest D φ) :
    MemLp (n06NegativeHalfPeriodDefect S K z m φ) 2 (canonicalMeasure S K m) := by
  have h₀ := n06_negative_current_operatorTest_memLp h04 hz hs m hm hφ.1
  have h₁ : MemLp (canonicalSource S K z m
      (fun q => divergenceOperator (L.coefficients z) φ (q + (0, Real.pi))))
      2 (canonicalMeasure S K m) := by
    simpa only [Nat.cast_one, one_mul] using
      n06_negative_current_shifted_operatorTest_memLp h04 hz hs m 1 hm hφ.1
  have hsavg := n06_canonicalSource_average_memLp m h₀ h₁
  have havg := n06_negative_current_operatorTest_memLp h04 hz hs m hm
    (n06_radialTestAverage_test hφ).1
  apply (memLp_congr_ae ?_).mpr (havg.sub hsavg)
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  change n06NegativeHalfPeriodDefect S K z m φ p =
    canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p -
      canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
  rw [n06_negative_current_twoHalf_source h04 hz hs hm hφ ⟨hp.1, mem_univ _⟩]
  ring

/-- The actual two-half bulk pairing retains the potential defect with
the correct sign. All terms paired with the L2 field are integrable. -/
theorem n06_negative_twoHalf_pairing_rewrite
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : RadialTest D φ)
    {U Q : PolarPoint → ℝ} (hU : MemLp U 2 (canonicalMeasure S K m)) :
    (∫ p, (Q p + K.potential z m p * U p) *
      canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, U p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ((∫ p, (Q p + K.potential z m p * U p) *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, U p * canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p
          ∂canonicalMeasure S K m)) +
      ∫ p, U p * n06NegativeHalfPeriodDefect S K z m φ p ∂canonicalMeasure S K m := by
  have hI : Integrable (fun p => U p * canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p)
      (canonicalMeasure S K m) := hU.integrable_mul
    (n06_negative_current_operatorTest_memLp h04 hz hs m hm (n06_radialTestAverage_test hφ).1)
  have hD : Integrable (fun p => U p * n06NegativeHalfPeriodDefect S K z m φ p)
      (canonicalMeasure S K m) :=
    hU.integrable_mul (n06_negativeHalfPeriodDefect_memLp h04 hz hs hm hφ)
  have he : (∫ p, U p * canonicalSource S K z m
      (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
        ∂canonicalMeasure S K m) =
      (∫ p, U p * canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n06_radialTestAverage φ)) p
          ∂canonicalMeasure S K m) -
      ∫ p, U p * n06NegativeHalfPeriodDefect S K z m φ p ∂canonicalMeasure S K m := by
    rw [← integral_sub hI hD]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [n06_negative_current_twoHalf_source h04 hz hs hm hφ ⟨hp.1, mem_univ _⟩]
    ring
  rw [he]
  ring

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The genuine finite negative Green formula for every original
full-period radial test. The explicit actual potential defect records
precisely the remaining half-period covariance issue. -/
theorem N06NegativeGraphApproximation.current_twoHalf_green
    {U G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation U G)
    (Q : N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ))
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : RadialTest D φ) (N : ℕ) :
    (∫ p, (n06NegativeFinitePrincipal P.modes N p +
        K.potential z m p * n06NegativeFiniteValue P.modes N p) *
      canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, n06NegativeFiniteValue P.modes N p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      (∫ θ in (0 : ℝ)..Real.pi,
        (Q.value (K.right m, θ) *
            radialPartial (n06NegativeFiniteValue P.modes N) (K.right m, θ) -
          n06NegativeFiniteValue P.modes N (K.right m, θ) * Q.radial (K.right m, θ)) -
        (Q.value (K.left m, θ) *
            radialPartial (n06NegativeFiniteValue P.modes N) (K.left m, θ) -
          n06NegativeFiniteValue P.modes N (K.left m, θ) * Q.radial (K.left m, θ))) +
      ∫ p, n06NegativeFiniteValue P.modes N p * n06NegativeHalfPeriodDefect S K z m φ p
        ∂canonicalMeasure S K m := by
  rw [n06_negative_twoHalf_pairing_rewrite h04 hz hs hm hφ (P.value_memLp N)]
  rw [P.current_green Q h04 hz hs hm (n06_radialTestAverage_test hφ).1
    (n06_radialTestAverage_periodic hφ.2.1) N]

end ContinuousFlexibility.Analysis
