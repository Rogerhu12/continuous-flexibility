module

public import ContinuousFlexibility.Analysis.N06CurrentShiftedTestLp

/-!
# Actual tests for the current physical weak residual

The original compact radial support of a RadialTest also supports its
actual corrected differential expression. The same Through04 witnesses
give all four transformed L2 tests used in the two half-period pairings.
Neither their support nor their square integrability is supplied as an
extra hypothesis to the final physical residual.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual divergence preserves an existing closed radial support,
without any coefficient regularity or periodicity assumption. -/
theorem n06_divergenceOperator_zero_off_radial_support
    (A : SymmetricCoefficients) {φ : PolarPoint → ℝ} {J : Set ℝ}
    (hJ : IsClosed J) (hzero : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0)
    {r : ℝ} (hr : r ∉ J) (θ : ℝ) : divergenceOperator A φ (r, θ) = 0 := by
  have he : φ =ᶠ[𝓝 (r, θ)] (0 : PolarPoint → ℝ) := by
    filter_upwards [(continuous_fst.tendsto (r, θ)).eventually
      (hJ.isOpen_compl.mem_nhds hr)] with q hq
    exact hzero q.1 hq q.2
  exact (n06_divergenceOperator_eventually_zero A he).eq_of_nhds

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Every genuine full-period physical test has the same original
compact radial support for both phi and L phi, and all four actual
canonical L2 transforms needed by the current physical weak residual.
The same material, physical, nonlinear, correction and coordinate data
are used throughout. -/
theorem n06_current_physical_tests
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hThrough : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ radialCore D ∧
      (∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) ∧
      (∀ r, r ∉ J → ∀ θ, divergenceOperator (L.coefficients z) φ (r, θ) = 0) ∧
      ∀ m : ℕ,
        MemLp (canonicalSource S K z m (divergenceOperator (L.coefficients z) φ))
          2 (canonicalMeasure S K m) ∧
        MemLp (canonicalSource S K z m
          (fun p => divergenceOperator (L.coefficients z) φ (p + (0, Real.pi))))
          2 (canonicalMeasure S K m) ∧
        MemLp (canonicalHeight S K z m φ) 2 (canonicalMeasure S K m) ∧
        MemLp (canonicalHeight S K z m (fun p => φ (p + (0, Real.pi))))
          2 (canonicalMeasure S K m) := by
  have h01 : N01Properties D T S C base loss ε := hThrough.1.1.1
  have h03 : N03Properties D T S C R L base ε := hThrough.1.2
  have h04 : N04Properties D T S C L K base loss ε := hThrough.2.2.2.2.1
  obtain ⟨J, hJ, hJcore, hzero⟩ := hφ.2.2
  refine ⟨J, hJ, hJcore, hzero,
    fun r hr θ => n06_divergenceOperator_zero_off_radial_support
      (L.coefficients z) hJ.isClosed hzero hr θ, fun m => ?_⟩
  have hshift : ContDiff ℝ ∞ (fun p : PolarPoint => φ (p + (0, Real.pi))) :=
    hφ.1.comp (contDiff_id.add contDiff_const)
  refine ⟨n06_current_operatorTest_memLp hT hS h01 h03 h04 hz hs m hφ, ?_,
    n06_current_canonicalHeight_memLp h04 hz hs m hφ.1.continuous.continuousOn,
    n06_current_canonicalHeight_memLp h04 hz hs m hshift.continuous.continuousOn⟩
  simpa only [Nat.cast_one, one_mul] using
    n06_current_shifted_operatorTest_memLp hT hS h01 h03 h04 hz hs m 1 hφ

end ContinuousFlexibility.Statements
