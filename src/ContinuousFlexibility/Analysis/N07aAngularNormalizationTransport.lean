import ContinuousFlexibility.Analysis.N07aAngularPhysicalAEPairing
import ContinuousFlexibility.Analysis.N07aAngularPhysicalRepresentative
import ContinuousFlexibility.Analysis.N07aAngularPhysicalSource
import ContinuousFlexibility.Analysis.N07aReferenceReturn

/-!
# The actual fixed row survives current-to-reference coordinate transport

The charts and height gauges agree on the prescribed normalization region,
which contains the support of the true reference column. Therefore two
physical fields representing the same canonical unknown at the current
and reference parameters have exactly the same original row integral.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_canonical_transport_referenceRow
    (hab : D.a ≤ D.b) (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {U : CanonicalUnknown S K} {F F₀ : CanonicalSequence S K}
    {η η₀ f f₀ : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    (hrep₀ : HasCanonicalRepresentation D S C K (C.referenceState, 0) U F₀ η₀ f₀)
    (hη : Function.Periodic η (0, Real.pi))
    (hη₀ : Function.Periodic η₀ (0, Real.pi)) :
    referenceRow D η = referenceRow D η₀ := by
  have hz₀ := n07a_reference_mem_stateNeighborhood h01
  have hs₀ := h01.2.2.1.stateSector
  apply n07a_referenceRow_congr_weighted_ae (S := S) (K := K) hab hη hη₀
  apply n07a_physical_piecewise_ae_eq h04 Subset.rfl
  intro m
  have he := n07aPhysicalHeightRepresentative_ae h04 hz hs hrep m
    (Filter.EventuallyEq.rfl : (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] U.1 m)
  have he₀ := n07aPhysicalHeightRepresentative_ae h04 hz₀ hs₀ hrep₀ m
    (Filter.EventuallyEq.rfl : (U.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] U.1 m)
  filter_upwards [he, he₀, n07a_canonicalOpen_ae
    (S := S) (K := n07aPhysicalIntervalData K) (m := m)] with p hp hp₀ hpU
  by_cases hcol : referenceColumn D p.1 = 0
  · simp only [hcol, zero_mul]
  · have hregion := h04.2.1 hcol
    obtain ⟨hc, hh⟩ := h04.2.2.1 z hz hs m p hpU hregion
    have heq : n07aPhysicalHeightRepresentative K z m (U.1 m) p =
        n07aPhysicalHeightRepresentative K (C.referenceState, 0) m (U.1 m) p := by
      simp only [n07aPhysicalHeightRepresentative, hc, hh]
    have hηeq : η p = η₀ p := by linarith only [hp, hp₀, heq]
    exact congrArg (referenceColumn D p.1 * ·) hηeq

end ContinuousFlexibility.Analysis
