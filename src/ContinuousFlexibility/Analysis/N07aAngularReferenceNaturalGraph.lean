module

public import ContinuousFlexibility.Analysis.N07aAngularReferenceGreen
public import ContinuousFlexibility.Analysis.N07aAngularReferenceMean
public import ContinuousFlexibility.Analysis.N07aAngularReferenceIntegrable
public import ContinuousFlexibility.Analysis.N07aAngularCutoffChange
public import ContinuousFlexibility.Analysis.N07aAngularReferenceCompatibleSource

/-!
# The transported candidate belongs to the genuine reference graph

The inputs are bounds on its displayed physical derivatives and remainder.
Natural source membership, conserved mean, and the full weak equation are
proved here, rather than required as certificates of the candidate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped Topology ContDiff

theorem n07a_referenceGraph_of_piecewise_material_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hborder : RadialTrueBorder D) (hχ : CutoffConditions D S.chiLeft)
    {v : PolarPoint → ℝ} (hv : ContDiffOn ℝ 1 v (annularOpen D))
    (hpiece : ∀ m, ContDiffOn ℝ ∞ v (referencePhysicalPieceOpen S K m))
    (hvp : Function.Periodic v (0, Real.pi)) (hve : ∀ r θ, v (r, -θ) = v (r, θ))
    (hzero : ∀ p, p ∉ annularOpen D → v p = 0)
    (hright : ∀ p ∈ annularOpen D, ∃ u : PolarPoint → ℝ,
      ContDiffAt ℝ ∞ u p ∧ ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → v q = u q)
    {γ β M₀ M₁ aL μ A₀ A₁ B : ℝ} (hβ : 0 < β) (hγ : γ < β)
    (q₀ q₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hB0 : 0 ≤ B)
    (hrem : ∀ p ∈ annularOpen D,
      |v p - aL * S.chiLeft p.1| ≤ A₁ * T.H p.1 ^ β * T.M p.1 ^ q₁)
    (hsource : ∀ p ∈ annularOpen D,
      |n07aReferenceInteriorDifferential D K v p| ≤ A₀ * T.H p.1 ^ β * T.M p.1 ^ q₀)
    (hjets : ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      |radialPartial v p| ≤ B ∧ |radialPartial (radialPartial v) p| ≤ B ∧
        |angularPartial (angularPartial v) p| ≤ B)
    (hrow : referenceRow D v = 0) :
    ReferenceGraph D γ M₀ M₁ (v, μ) (n07aReferenceCompatibleSource D K v μ, 0) := by
  have hgeom := hD.choose_spec.1
  have hab := hgeom.2.1.le
  have hvM : Measurable v := n07a_referenceField_measurable hv.continuousOn hzero
  have hremM : AEStronglyMeasurable (fun p => v p - aL * S.chiLeft p.1)
      (radialPhysicalMeasure D) :=
    (hvM.sub (measurable_const.mul (hχ.1.continuous.measurable.comp measurable_fst))).aestronglyMeasurable
  have hOut : OutputMember D γ M₁ (v, μ) :=
    ⟨aL, n07a_outputRealization_of_material_decay hD hT hχ hborder hβ hγ q₁
      hremM hA₁ hrem hvp hve⟩
  obtain ⟨hN, hF⟩ := n07a_referenceSources_integrable_of_jet_bounds h04 hgeom hB0 hjets
  have hvr := n07a_reference_firstJet_bound_on_core h04 hv
    (fun m p hp => (hjets m p hp).1)
  obtain ⟨hmeanInt, hmeanZero⟩ := n07a_referenceInteriorDifferential_compatible_mean
    h04 hab hgeom.2.2.1 hv hpiece hvp hright hvr hN hF
  have hSource : SourceMember D γ M₀ (n07aReferenceInteriorDifferential D K v, 0) :=
    n07a_sourceMember_of_material_decay hD hT hβ hγ q₀
      (n07aReferenceInteriorDifferential_measurable K
        hgeom.2.2.1.1.continuous.measurable v).aestronglyMeasurable hA₀ hsource
      (n07aReferenceInteriorDifferential_periodic D K hvp)
      (n07aReferenceInteriorDifferential_even D K hve) hmeanInt hmeanZero
  have hBorder := n07a_referenceBorder_sourceMember hD hborder γ M₀
  have hTotal : SourceMember D γ M₀ (n07aReferenceCompatibleSource D K v μ, 0) := by
    have he : (n07aReferenceInteriorDifferential D K v, (0 : ℝ)) +
        μ • ((fun p : PolarPoint => referenceColumn D p.1 * cosineMode 2 p.2), (0 : ℝ)) =
        (n07aReferenceCompatibleSource D K v μ, 0) := by
      apply Prod.ext
      · funext p
        simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, n07aReferenceCompatibleSource]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero]
    exact Eq.mp (congrArg (SourceMember D γ M₀) he)
      (hSource.add hab hD.choose_spec.2.1 (hBorder.smul μ))
  refine ⟨hOut, hTotal, hrow, ?_⟩
  intro φ hφ
  have hG := n07a_referenceInteriorDifferential_green hD hborder hv hpiece hvp hright
    (n07a_referencePieceInterior_ae h04) hOut hN hF hφ
  have hFφ := n07a_physical_integrable_mul_continuous hF hφ.1.continuous
  have hBφ := r11b_source_radialTest_pairing_integrable hD hBorder hφ
  have hMφ : Integrable (fun p : PolarPoint =>
      (μ * (referenceColumn D p.1 * cosineMode 2 p.2)) * φ p) (radialPhysicalMeasure D) := by
    simpa only [mul_assoc] using hBφ.const_mul μ
  have hTφ : Integrable (fun p => n07aReferenceCompatibleSource D K v μ p * φ p)
      (radialPhysicalMeasure D) := by
    exact (hFφ.add hMφ).congr (Eventually.of_forall fun p => by
      simp only [Pi.add_apply, n07aReferenceCompatibleSource, add_mul])
  rw [hG, r11b_integral_angularMean_eq hab hFφ,
    r11b_integral_angularMean_eq hab hBφ,
    r11b_integral_angularMean_eq hab hTφ]
  have he : (fun p => n07aReferenceCompatibleSource D K v μ p * φ p) =
      fun p => n07aReferenceInteriorDifferential D K v p * φ p +
        μ * ((referenceColumn D p.1 * cosineMode 2 p.2) * φ p) := by
    funext p
    dsimp only [n07aReferenceCompatibleSource]
    ring
  rw [he, integral_add hFφ (hBφ.const_mul μ), integral_const_mul]
  ring

end ContinuousFlexibility.Analysis
