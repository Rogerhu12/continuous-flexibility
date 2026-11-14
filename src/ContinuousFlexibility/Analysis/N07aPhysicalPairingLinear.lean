module

public import ContinuousFlexibility.Analysis.N07aPhysicalCanonicalPairing
public import ContinuousFlexibility.Analysis.N07aCanonicalDifference

/-!
# Linear source pairings with their actual integrability

The physical functions may be rough. Their source transforms paired with
one compact canonical test are integrable, so the true chart formula
proves linearity of the full-period physical pairing.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

theorem n07a_pulledTest_source_sub
    (hab : D.a ≤ D.b) (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {W f g : PolarPoint → ℝ} (hW : CanonicalTest S K m W)
    (hfp : ∀ p ∈ physicalPieceOpen S K z m, f (p + (0, Real.pi)) = f p)
    (hgp : ∀ p ∈ physicalPieceOpen S K z m, g (p + (0, Real.pi)) = g p)
    (hif : Integrable (fun p => canonicalSource S K z m f p * W p) (canonicalMeasure S K m))
    (hig : Integrable (fun p => canonicalSource S K z m g p * W p) (canonicalMeasure S K m))
    (c : ℝ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      (f (r, θ) - c * g (r, θ)) * n07aPhysicalTestPullback S K z m W (r, θ))) =
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        f (r, θ) * n07aPhysicalTestPullback S K z m W (r, θ))) -
      c * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        g (r, θ) * n07aPhysicalTestPullback S K z m W (r, θ))) := by
  have he : (fun p => canonicalSource S K z m (fun q => f q - c * g q) p * W p) =
      fun p => canonicalSource S K z m f p * W p -
        c * (canonicalSource S K z m g p * W p) := by
    funext p
    rw [n07a_canonicalSource_sub, n07a_canonicalSource_const_mul]
    ring
  have hi : Integrable (fun p => canonicalSource S K z m
      (fun q => f q - c * g q) p * W p) (canonicalMeasure S K m) := by
    rw [he]
    exact hif.sub (hig.const_mul c)
  have hp : ∀ p ∈ physicalPieceOpen S K z m,
      (f (p + (0, Real.pi)) - c * g (p + (0, Real.pi))) = f p - c * g p := by
    intro p hp
    rw [hfp p hp, hgp p hp]
  rw [n07a_pulledTest_source_pairing hab h04 hz hs hW hp hi,
    n07a_pulledTest_source_pairing hab h04 hz hs hW hfp hif,
    n07a_pulledTest_source_pairing hab h04 hz hs hW hgp hig,
    he, integral_sub hif (hig.const_mul c), integral_const_mul]
  ring

end ContinuousFlexibility.Analysis
