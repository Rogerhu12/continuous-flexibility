import ContinuousFlexibility.Analysis.N07bCanonicalSourceEnergy

/-!
# Positive piecewise constant height rescaling

Multiplying the height on each piece by a state-independent positive
constant preserves the qualitative geometry in Part A. The source,
normalized height, and source-energy density obey the exact formulas below.

Only the height field is changed. This module makes no preservation claim
for Part B, the canonical operator, N05, or N06, and does not assert a
counterexample to the existential N07b statement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Rescale the actual height, leaving the given charts and all other
fields unchanged. The scaling does not depend on the nonlinear state. -/
def n07bCanonicalHeightRescale {S : PhysicalSpacesData}
    (K : CanonicalData S) (a : ℕ → ℝ) : CanonicalData S :=
  { K with height := fun z m p => a m * K.height z m p }

variable {S : PhysicalSpacesData} (K : CanonicalData S) (a : ℕ → ℝ)

/-- The actual source conversion gains exactly one scaling factor. -/
theorem n07bCanonicalHeightRescale_source
    (z : AnnularState S × ℝ) (m : ℕ) (f : PolarPoint → ℝ) (p : PolarPoint) :
    canonicalSource S (n07bCanonicalHeightRescale K a) z m f p =
      a m * canonicalSource S K z m f p := by
  dsimp only [canonicalSource, n07bCanonicalHeightRescale]
  ring

/-- The normalized unknown loses exactly one scaling factor. The identity
also respects the totalized real division convention when a factor is zero. -/
theorem n07bCanonicalHeightRescale_height
    (z : AnnularState S × ℝ) (m : ℕ) (u : PolarPoint → ℝ) (p : PolarPoint) :
    canonicalHeight S (n07bCanonicalHeightRescale K a) z m u p =
      (a m)⁻¹ * canonicalHeight S K z m u p := by
  dsimp only [canonicalHeight, n07bCanonicalHeightRescale]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The physical source-energy density gains the square of the factor. -/
theorem n07bCanonicalHeightRescale_density
    (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint) :
    n07bCanonicalSourceDensity S (n07bCanonicalHeightRescale K a) z m p =
      a m ^ 2 * n07bCanonicalSourceDensity S K z m p := by
  dsimp only [n07bCanonicalSourceDensity, n07bCanonicalHeightRescale]
  ring

/-- The actual canonical measure is unchanged by a height rescaling. -/
theorem n07bCanonicalHeightRescale_measure (m : ℕ) :
    canonicalMeasure S (n07bCanonicalHeightRescale K a) m = canonicalMeasure S K m := rfl

/-- The exact raw square-integral scaling. This is an algebraic identity
of totalized integrals and does not infer integrability. -/
theorem n07bCanonicalHeightRescale_source_square_integral
    (z : AnnularState S × ℝ) (m : ℕ) (f : PolarPoint → ℝ) :
    (∫ p, canonicalSource S (n07bCanonicalHeightRescale K a) z m f p ^ 2
      ∂canonicalMeasure S (n07bCanonicalHeightRescale K a) m) =
      a m ^ 2 * ∫ p, canonicalSource S K z m f p ^ 2 ∂canonicalMeasure S K m := by
  rw [n07bCanonicalHeightRescale_measure]
  simp_rw [n07bCanonicalHeightRescale_source, mul_pow]
  exact integral_const_mul _ _

/-- Arbitrary positive factors preserve all qualitative Part A clauses,
including the fixed normalization region, closed-endpoint regularity,
and the actual angular symmetries. -/
theorem n07bCanonicalHeightRescale_partA
    {D : ReferenceData} {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε) (ha : ∀ m, 0 < a m) :
    N04PartA D S C (n07bCanonicalHeightRescale K a) base ε := by
  refine {
    normalizationOpen := hK.normalizationOpen
    normalizationSupport := hK.normalizationSupport
    normalization := ?_
    referenceBounds := hK.referenceBounds
    referencePositive := hK.referencePositive
    referenceNegative := hK.referenceNegative
    referencePartition := hK.referencePartition
    referenceDomain := hK.referenceDomain
    domains := hK.domains
    partition := hK.partition
    charts := ?_
    boundary := ?_
    reflection := ?_
    inverseReflection := hK.inverseReflection }
  · intro z hz hs m
    have hn := hK.normalization z hz hs m
    refine ⟨hn.1, ?_⟩
    intro p hp hpn
    obtain ⟨hc, hh⟩ := hn.2 p hp hpn
    exact ⟨hc, congrArg (fun t : ℝ => a m * t) hh⟩
  · intro z hz hs m
    obtain ⟨hmap, himap, hleft, hright, hchart, hinverse, hheight, hregular⟩ :=
      hK.charts z hz hs m
    refine ⟨hmap, himap, hleft, hright, hchart, hinverse,
      (contDiffOn_const (c := a m)).mul hheight, ?_⟩
    intro p hp
    obtain ⟨hpos, hJ, hchartPeriod, hheightPeriod⟩ := hregular p hp
    exact ⟨mul_pos (ha m) hpos, hJ, hchartPeriod,
      congrArg (fun t : ℝ => a m * t) hheightPeriod⟩
  · intro z hz hs m
    obtain ⟨hmap, himap, hleft, hright, hregular, hgerm⟩ := hK.boundary z hz hs m
    refine ⟨hmap, himap, hleft, hright, ?_, hgerm⟩
    intro p hp
    obtain ⟨hchart, hheight, hJ, hpos⟩ := hregular p hp
    exact ⟨hchart, (contDiffAt_const (c := a m)).mul hheight,
      hJ, mul_pos (ha m) hpos⟩
  · intro z hz hs m p hp
    obtain ⟨hchart, hheight, hJ⟩ := hK.reflection z hz hs m p hp
    exact ⟨hchart, congrArg (fun t : ℝ => a m * t) hheight, hJ⟩

end ContinuousFlexibility.Analysis
