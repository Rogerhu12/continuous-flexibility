import ContinuousFlexibility.Analysis.N06PrincipalDensitySymmetry
import ContinuousFlexibility.Analysis.N06CurrentOperatorPeriodicity

/-!
# The actual positive canonical coefficients have the required symmetries

On a positive physical piece the true corrected coefficients equal the
original ones. Their periodicity and the original N03 reflection signs
pass through the genuine forward density. The inverse chart is used only
to choose an interior physical preimage of an interior canonical point.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n06_correctedCoefficients_periodic_on_positive
    (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ annularOpen D) (hpos : 0 < deriv D.w p.1) :
    (L.coefficients z).a (p + (0, Real.pi)) = (L.coefficients z).a p ∧
      (L.coefficients z).b (p + (0, Real.pi)) = (L.coefficients z).b p ∧
      (L.coefficients z).c (p + (0, Real.pi)) = (L.coefficients z).c p := by
  have hp' : p + (0, Real.pi) ∈ annularOpen D :=
    ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  have hpos' : 0 < deriv D.w (p + (0, Real.pi)).1 := by
    simpa only [Prod.fst_add, add_zero] using hpos
  have hbc := h03.2.1 z hz hs p hp hpos
  have hbc' := h03.2.1 z hz hs _ hp' hpos'
  have hper := n06_originalCoefficients_periodic (C := C) hS z
  exact ⟨(h03.1 z hz hs _).trans ((hper.1 p).trans (h03.1 z hz hs p).symm),
    hbc'.1.eq_of_nhds.trans ((hper.2.1 p).trans hbc.1.eq_of_nhds.symm),
    hbc'.2.eq_of_nhds.trans ((hper.2.2 p).trans hbc.2.eq_of_nhds.symm)⟩

/-- The period of the original actual positive coefficient fields is a
consequence of their true density formula. -/
theorem n06_positive_canonical_coefficients_periodicOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true)
    (hreg : ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    (K.coefficients z m).a (p + (0, Real.pi)) = (K.coefficients z m).a p ∧
      (K.coefficients z m).b (p + (0, Real.pi)) = (K.coefficients z m).b p ∧
      (K.coefficients z m).c (p + (0, Real.pi)) = (K.coefficients z m).c p := by
  have hA := (n06_N04_qualitative_parts h04).1
  have hc := hA.2.2.2.2.2.2.2.1 z hz hs m
  let x := K.inverseChart z m p
  have hx : x ∈ physicalPieceOpen S K m := hc.2.1 hp
  have hx' : x + (0, Real.pi) ∈ physicalPieceOpen S K m :=
    ⟨by simpa only [Prod.fst_add, add_zero] using hx.1, mem_univ _⟩
  have hFx : K.chart z m x = p := hc.2.2.2.1 p hp
  have hgood := hc.2.2.2.2.2.2.2
  have hFshift : K.chart z m (x + (0, Real.pi)) = p + (0, Real.pi) :=
    (hgood x hx).2.2.1.trans (congrArg (fun q => q + (0, Real.pi)) hFx)
  have hden := n06_positive_physical_density_of_regular_coefficients
    hT hS h01 h03 h04 hz hs m hm hreg hx
  have hden' := n06_positive_physical_density_of_regular_coefficients
    hT hS h01 h03 h04 hz hs m hm hreg hx'
  have hper := n06_correctedCoefficients_periodic_on_positive hS h03 hz hs
    (show x ∈ annularOpen D from ⟨(h04.2.2.2.1 m).2.2 hx.1, mem_univ _⟩)
    (h04.2.2.2.2.1 m hm x.1 hx.1)
  have hdp := n06_coordinatePrincipalDensity_periodicOn hc.2.2.2.2.1
    (fun q hq => (hgood q hq).2.2.1) hx hper.1 hper.2.1 hper.2.2
    (hgood x hx).2.2.2
  rw [hFx] at hden
  rw [hFshift] at hden'
  exact ⟨hden'.1.trans (hdp.1.trans hden.1.symm),
    hden'.2.1.trans (hdp.2.1.trans hden.2.1.symm),
    hden'.2.2.trans (hdp.2.2.trans hden.2.2.symm)⟩

/-- Even/odd/even reflection is forced by the genuine N03 signs and N04
forward chart symmetry, rather than stipulated for canonical coefficients. -/
theorem n06_positive_canonical_coefficients_evenOddOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true)
    (hreg : ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    (K.coefficients z m).a (p.1, -p.2) = (K.coefficients z m).a p ∧
      (K.coefficients z m).b (p.1, -p.2) = -(K.coefficients z m).b p ∧
      (K.coefficients z m).c (p.1, -p.2) = (K.coefficients z m).c p := by
  have hA := (n06_N04_qualitative_parts h04).1
  obtain ⟨_, _, _, _, _, _, _, hcharts, _, hparity, _⟩ := hA
  have hc := hcharts z hz hs m
  let x := K.inverseChart z m p
  have hx : x ∈ physicalPieceOpen S K m := hc.2.1 hp
  have hx' : (x.1, -x.2) ∈ physicalPieceOpen S K m := ⟨hx.1, mem_univ _⟩
  have hFx : K.chart z m x = p := hc.2.2.2.1 p hp
  have hFsym : K.chart z m (x.1, -x.2) = (p.1, -p.2) := by
    rw [(hparity z hz hs m x hx).1, hFx]
  have hden := n06_positive_physical_density_of_regular_coefficients
    hT hS h01 h03 h04 hz hs m hm hreg hx
  have hden' := n06_positive_physical_density_of_regular_coefficients
    hT hS h01 h03 h04 hz hs m hm hreg hx'
  have hsign := h03.2.2.2.1 z hz hs x.1 x.2
  have hdp := n06_coordinatePrincipalDensity_reflectionOn hc.2.2.2.2.1
    (fun q hq => (hparity z hz hs m q hq).1) hx hsign.1 hsign.2.1 hsign.2.2
    (hparity z hz hs m x hx).2.1 (hparity z hz hs m x hx).2.2
  rw [hFx] at hden
  rw [hFsym] at hden'
  exact ⟨hden'.1.trans (hdp.1.trans hden.1.symm),
    hden'.2.1.trans (hdp.2.1.trans (congrArg Neg.neg hden.2.1.symm)),
    hden'.2.2.trans (hdp.2.2.trans hden.2.2.symm)⟩

/-- Combining the actual half period and reflection gives the literal
half-cylinder reflection required by the original cubic source map. -/
theorem n06_positive_canonical_coefficients_reflectionOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hm : K.positive m = true)
    (hreg : ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    (K.coefficients z m).a (p.1, Real.pi - p.2) = (K.coefficients z m).a p ∧
      (K.coefficients z m).b (p.1, Real.pi - p.2) = -(K.coefficients z m).b p ∧
      (K.coefficients z m).c (p.1, Real.pi - p.2) = (K.coefficients z m).c p := by
  have hn : (p.1, -p.2) ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  have hper := n06_positive_canonical_coefficients_periodicOn hT hS h01 h03 h04 hz hs m hm hreg hn
  have hsym := n06_positive_canonical_coefficients_evenOddOn hT hS h01 h03 h04 hz hs m hm hreg hp
  have hshift : (p.1, -p.2) + (0, Real.pi) = (p.1, Real.pi - p.2) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
  rw [hshift] at hper
  exact ⟨hper.1.trans hsym.1, hper.2.1.trans hsym.2.1, hper.2.2.trans hsym.2.2⟩

end ContinuousFlexibility.Statements
