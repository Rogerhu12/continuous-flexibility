import ContinuousFlexibility.Analysis.N06NormalizerRetype
import ContinuousFlexibility.Analysis.N06PhysicalSourceUniqueness
import ContinuousFlexibility.Analysis.N06PhysicalPairingCongruence
import ContinuousFlexibility.Analysis.N06AngularMeanBridge

/-!
# The actual compatibility coordinate of the original N05 inverse

For a source represented by an element of the original physical height
space, the lambda coordinate is exactly its unchanged functional Q.
This follows from the literal zero-mean clause of SourceMember and the
proved injectivity of the actual canonical source transformation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

theorem n06_height_full_source_integral
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : (S.height (3 / 4 : ℝ)).Space) :
    (∫ r in D.a..D.b, radialAngularMean
      (fun θ => (S.height (3 / 4 : ℝ)).decode u (r, θ))) = S.Q u := by
  have hc : Continuous ((S.height (3 / 4 : ℝ)).decode u) :=
    (physical_height_contDiff_and_flatJets hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) u).1.continuous
  have hp : Function.Periodic ((S.height (3 / 4 : ℝ)).decode u) (0, Real.pi) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 u).2.2.1
  have he : (∫ r in D.a..D.b, radialAngularMean
      (fun θ => (S.height (3 / 4 : ℝ)).decode u (r, θ))) =
      physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode u) := by
    apply intervalIntegral.integral_congr
    intro r _hr
    apply n06_radialAngularMean_eq_angularMean_of_continuous
    · intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hp (r, θ)
    · exact hc.comp (continuous_const.prodMk continuous_id)
  exact he.trans (hS.2.2.2.2.2.2.2.1 u).symm

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

/-- The graph's compatibility scalar is determined by a genuine physical
source, independently of the representative chosen in its definition. -/
theorem n06_referenceRelation_lambda_eq_Q
    (hab : D.a ≤ D.b) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    {γ M₀ M₁ l : ℝ} {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (hrel : ReferenceCanonicalRelation D T S C K V γ M₀ M₁ l U F)
    (u : (S.height (3 / 4 : ℝ)).Space)
    (hsource : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m ((S.height (3 / 4 : ℝ)).decode u)) :
    U.2.2.2 = S.Q u := by
  obtain ⟨_hmember, η, f, hrep, hgraph⟩ := hrel
  have hψperiod : Function.Periodic ((S.height (3 / 4 : ℝ)).decode S.psi)
      (0, Real.pi) := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.2.1
  have hfperiod : Function.Periodic f (0, Real.pi) := by
    intro p
    have he := hgraph.2.1.2.2.1 p
    change f (p + (0, Real.pi)) - U.2.2.2 *
        (S.height (3 / 4 : ℝ)).decode S.psi (p + (0, Real.pi)) =
      f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p at he
    rw [hψperiod p] at he
    exact sub_left_inj.mp he
  have huperiod : Function.Periodic ((S.height (3 / 4 : ℝ)).decode u) (0, Real.pi) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 u).2.2.1
  have hfae : f =ᵐ[volume.restrict (annularOpen D)]
      (S.height (3 / 4 : ℝ)).decode u :=
    n06_canonicalSource_ae_injective h04 href hsector hfperiod huperiod
      (fun m => (hrep.2 m).symm.trans (hsource m))
  have hredae : (fun p => f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p)
      =ᵐ[volume.restrict (annularOpen D)]
        (S.height (3 / 4 : ℝ)).decode (u - U.2.2.2 • S.psi) := by
    filter_upwards [hfae] with p hp
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun a : ℝ => a - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p) hp
  have hzero : (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      (S.height (3 / 4 : ℝ)).decode (u - U.2.2.2 • S.psi) (r, θ))) = 0 :=
    (n06_radialAngularIntegral_congr_ae hab hredae).symm.trans hgraph.2.1.2.2.2.2.2
  have hQzero : S.Q (u - U.2.2.2 • S.psi) = 0 :=
    (n06_height_full_source_integral hT hS (u - U.2.2.2 • S.psi)).symm.trans hzero
  rw [map_sub, map_smul, hS.2.2.2.2.2.2.2.2.2.1, smul_eq_mul, mul_one] at hQzero
  exact (sub_eq_zero.mp hQzero).symm

theorem n06N05_inverse_lambda_eq_Q
    {b : ℕ} {B : CanonicalDomainData S K V b}
    (hab : D.a ≤ D.b) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S C.referenceState)
    (F : V.level (3 / 4 : ℝ) 0 b) (u : (S.height (3 / 4 : ℝ)).Space)
    (hsource : ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m ((S.height (3 / 4 : ℝ)).decode u)) :
    (B.inverse F).val.1.2.2.2 = S.Q u := by
  have hgraph := h05.2.2.2.2.2.2.1
  have hrel := (hgraph (B.inverse F).val).mp (B.inverse F).property
  have hright : (B.inverse F).val.2 = F := h05.2.2.2.2.2.2.2.1 F
  apply n06_referenceRelation_lambda_eq_Q hab hT hS h04 href hsector hrel u
  intro m
  simpa only [hright] using hsource m

end ContinuousFlexibility.Statements
