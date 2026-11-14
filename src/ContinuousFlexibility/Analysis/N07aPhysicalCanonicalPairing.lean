module

public import ContinuousFlexibility.Analysis.N07aLocalizedRoughPairing
public import ContinuousFlexibility.Analysis.N07aPhysicalTestSupport
public import ContinuousFlexibility.Analysis.N07aCanonicalRepresentationPairing

/-!
# Exact physical pairings against a pulled canonical test

Each integral is justified from its actual canonical representative.
These two change-of-variable lemmas handle the source terms and the
distributional operator term, retaining the cutoff scalar and the factor π.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

theorem n07a_pulledTest_source_pairing
    (hab : D.a ≤ D.b) (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {W f : PolarPoint → ℝ} (hW : CanonicalTest S K m W)
    (hfp : ∀ p ∈ physicalPieceOpen S K z m, f (p + (0, Real.pi)) = f p)
    (hi : Integrable (fun p => canonicalSource S K z m f p * W p)
      (canonicalMeasure S K m)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      f (r, θ) * n07aPhysicalTestPullback S K z m W (r, θ))) =
      Real.pi⁻¹ * ∫ p, canonicalSource S K z m f p * W p ∂canonicalMeasure S K m := by
  let ψ := n07aPhysicalTestPullback S K z m W
  have hψp := (n07aPhysicalTestPullback_test h04 hz hs hW).2.1
  have he : (fun p => canonicalHeight S K z m ψ p * canonicalSource S K z m f p)
      =ᵐ[canonicalMeasure S K m] fun p => canonicalSource S K z m f p * W p := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    rw [n07aPhysicalTestPullback_height h04 hz hs W hp]
    exact mul_comm _ _
  have hip := (integrable_congr he).mpr hi
  have hzero : ∀ p ∉ physicalPieceOpen S K z m, ψ p * f p = 0 := by
    intro p hp
    dsimp only [ψ]
    rw [n07aPhysicalTestPullback_zero (K := K) z m W hp, zero_mul]
  have hperiod : ∀ p ∈ physicalPieceOpen S K z m,
      ψ (p + (0, Real.pi)) * f (p + (0, Real.pi)) = ψ p * f p := by
    intro p hp
    exact congrArg₂ (· * ·) (hψp p) (hfp p hp)
  have h := n07a_localized_rough_pairing hab h04 hz hs ψ f hip hzero hperiod
  rw [integral_congr_ae he] at h
  simpa only [mul_comm] using h

theorem n07a_pulledTest_operator_pairing
    (hab : D.a ≤ D.b) (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hχ : ContDiff ℝ ∞ S.chiLeft)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    (hηp : Function.Periodic η (0, Real.pi))
    {W g : PolarPoint → ℝ} (hW : CanonicalTest S K m W) (hg : CanonicalTest S K m g)
    (he : EqOn (canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (n07aPhysicalTestPullback S K z m W))) g
        (canonicalOpen S K m)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => η (r, θ) *
      divergenceOperator (L.coefficients z) (n07aPhysicalTestPullback S K z m W) (r, θ))) =
      Real.pi⁻¹ * ((∫ p, U.1 m p * g p ∂canonicalMeasure S K m) +
        U.2.1 * ∫ p, n07aCanonicalCutoffHeight S K z m p * g p
          ∂canonicalMeasure S K m) := by
  let ψ := n07aPhysicalTestPullback S K z m W
  let Aψ := divergenceOperator (L.coefficients z) ψ
  have heAE : (fun p => canonicalHeight S K z m η p * canonicalSource S K z m Aψ p)
      =ᵐ[canonicalMeasure S K m] fun p => canonicalHeight S K z m η p * g p :=
    n07a_canonicalOpen_ae.mono fun p hp => congrArg (canonicalHeight S K z m η p * ·) (he hp)
  have hi := (integrable_congr heAE).mpr
    (n07a_canonicalRepresentation_height_integrable h04 hz hs hχ hrep hg)
  have hAp : ∀ p ∈ physicalPieceOpen S K z m, Aψ (p + (0, Real.pi)) = Aψ p := by
    apply n07a_physical_periodic_of_canonicalSource h04 hz hs
    intro p hp
    have hps : p + (0, Real.pi) ∈ canonicalOpen S K m :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
    exact (he hps).trans ((hg.2.1 p).trans (he hp).symm)
  have hzero : ∀ p ∉ physicalPieceOpen S K z m, η p * Aψ p = 0 := by
    intro p hp
    dsimp only [Aψ, ψ]
    rw [n07aPhysicalTestPullback_divergence_zero
      h04 hz hs hW (L.coefficients z) hp, mul_zero]
  have hperiod : ∀ p ∈ physicalPieceOpen S K z m,
      η (p + (0, Real.pi)) * Aψ (p + (0, Real.pi)) = η p * Aψ p := by
    intro p hp
    exact congrArg₂ (· * ·) (hηp p) (hAp p hp)
  have h := n07a_localized_rough_pairing hab h04 hz hs η Aψ hi hzero hperiod
  rw [integral_congr_ae heAE,
    n07a_canonicalRepresentation_height_pairing h04 hz hs hχ hrep hg] at h
  exact h

end ContinuousFlexibility.Analysis
