import ContinuousFlexibility.Radial.ReferenceSmoothCoefficientExtensions
import ContinuousFlexibility.Radial.ReferenceGraphRepresentative
import ContinuousFlexibility.Radial.ReferencePhiRapid

/-!
# Smooth inverse images of the actual finite-source core

The given inverse is first shown to have finite angular spectrum by its
actual graph uniqueness. Each coefficient has a smooth interior
representative, its genuine derivative has positive attenuation by the
first-normal estimate, and the original Jacobi equation propagates that
attenuation to every jet. The zero mode retains its actual left constant.
The final finite sum is therefore a global smooth admissible field and
represents the same frozen weak graph.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open ContinuousFlexibility.Analysis

noncomputable section

theorem reference_smooth_inverse_image {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hφ : ∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0)
    (hmodes : ∃ Gmode : RadialModePair D →L[ℝ] RadialModePair D,
      ModeInverseProperties D 2 Gmode)
    {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hNormal : FirstNormalInverseEstimate D γ M₀ M₁ G)
    (hγ : 0 < γ) {F : RadialSource} (hF : SourceMember D γ M₀ F)
    (hfinite : ReferenceSmoothFiniteSource D F) :
    ∃ V : RadialUnknown, ReferenceGraph D γ M₀ M₁ V F ∧ SmoothAdmissibleField D V := by
  classical
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hp : RadialPartition D := hD.choose_spec.2.1
  obtain ⟨Gmode, hmode⟩ := hmodes
  obtain ⟨hφW, hφ'W⟩ := referencePhi_rapid_of_inverse hD hborder hφ hγ hmode hG hNormal
  have hcolumn (k : ℕ) : ReferenceRapid D (iteratedDeriv k (referenceColumn D)) :=
    referenceColumn_jets_rapid hD hborder hφ hφW hφ'W k
  let U : RadialUnknown := G F
  have hgraph : ReferenceGraph D γ M₀ M₁ U F := hG.1 F hF
  obtain ⟨aL, hU⟩ := hgraph.1
  obtain ⟨ur, hur, hurW⟩ := hfinite.exists_normal hD hNormal
  choose v hv hae heq using
    (fun n : ℕ => referenceGraph_exists_smooth_coefficient hD hborder hγ hgraph hfinite.contDiff n)
  have hdW (n : ℕ) : ReferenceRapid D (deriv (v n)) := by
    have hw := referenceRadialCoefficient_output_zero_weighted hgeom.2.1.le hurW n
    have hdI : LocallyIntegrableOn (referenceRadialCoefficient ur n) (radialCore D) volume :=
      (hw.integrable hp hγ).locallyIntegrableOn
    have hder := reference_coefficient_normal_eq_deriv hgeom.2.1 hur n (hv n) (hae n) hdI
    exact ⟨γ, -2 * M₁, hγ, hw.congr_ae hder⟩
  have huW (n : ℕ) (hn : n ≠ 0) : ReferenceRapid D (v n) := by
    have hw := referenceRadialCoefficient_output_weighted hgeom.2.1.le hp hU hn
    exact ⟨γ, -2 * M₁, hγ, hw.congr_ae (hae n)⟩
  have hforcing (n k : ℕ) :
      ReferenceRapid D (iteratedDeriv k (referenceCoefficientForcing D U F n)) :=
    referenceCoefficientForcing_jets_rapid hD hborder hfinite hcolumn n k
  have hmeanW : ReferenceRapid D (fun r => v 0 r - aL * D.chiLeft r) := by
    have hw := referenceRadialCoefficient_output_weighted_remainder hgeom.2.1.le hU 0
    have hrem := referenceRadialCoefficient_output_mean_remainder_ae hp hU
    have he : referenceRadialCoefficient (outputRemainder D aL U) 0 =ᵐ[volume.restrict (radialCore D)] (fun r => v 0 r - aL * D.chiLeft r) :=
      hrem.trans ((hae 0).mono fun r hr => congrArg (fun z : ℝ => z - aL * D.chiLeft r) hr)
    exact ⟨γ, -2 * M₁, hγ, hw.congr_ae he⟩
  have hzero : ∀ r ∈ radialCore D,
      radialJacobi 0 D.w (v 0) r = referenceRadialCoefficient F.1 0 r := by
    intro r hr
    simpa [referenceCoefficientForcing] using heq 0 r hr
  obtain ⟨v₀, hv₀, he₀, hleft₀, hright₀⟩ :=
    reference_smooth_zeroMode_extension hD hborder (hv 0)
      (contDiff_referenceRadialCoefficient hfinite.contDiff 0) hzero hmeanW (hdW 0)
      (hfinite.coefficient_jets_rapid hD 0)
  let ve : ℕ → ℝ → ℝ := fun n =>
    if n = 0 then v₀ else extendZeroOutside D.a D.b (v n)
  have hve (n : ℕ) : ContDiff ℝ ∞ (ve n) := by
    by_cases hn : n = 0
    · simpa only [ve, if_pos hn] using hv₀
    · change ContDiff ℝ ∞ (if n = 0 then v₀ else extendZeroOutside D.a D.b (v n))
      rw [if_neg hn]
      exact reference_contDiff_zero_extension_of_weighted_jets hD (hv n)
        (reference_radial_jets_rapid hD (hv n)
          (referenceCoefficientForcing_contDiff hgeom hborder hfinite.contDiff n).contDiffOn
          (heq n) (huW n hn) (hdW n) (hforcing n))
  have hext (n : ℕ) : EqOn (ve n) (v n) (radialCore D) := by
    by_cases hn : n = 0
    · subst n
      simpa only [ve, ite_true] using he₀
    · intro r hr
      simp only [ve, if_neg hn, extendZeroOutside_of_mem hr]
  have hleft (n : ℕ) (r : ℝ) (hr : r ≤ D.a) :
      ve n r = if n = 0 then aL else 0 := by
    by_cases hn : n = 0
    · simpa only [ve, if_pos hn] using hleft₀ r hr
    · simp only [ve, if_neg hn, extendZeroOutside_of_notMem
        (fun hmem => (not_lt.mpr hr) hmem.1)]
  have hright (n : ℕ) (r : ℝ) (hr : D.b ≤ r) : ve n r = 0 := by
    by_cases hn : n = 0
    · simpa only [ve, if_pos hn] using hright₀ r hr
    · simp only [ve, if_neg hn, extendZeroOutside_of_notMem
        (fun hmem => (not_lt.mpr hr) hmem.2)]
  obtain ⟨I, h0, h1, hfix⟩ := hfinite.exists_fixed_projection
  let V : PolarPoint → ℝ := fun x =>
    ∑ n ∈ I, ve n x.1 * referenceAngularBasis n x.2
  have hVs : ContDiff ℝ ∞ V := by
    apply ContDiff.sum
    intro n _hn
    exact ((hve n).comp contDiff_fst).mul ((contDiff_referenceAngularBasis n).comp contDiff_snd)
  have hVp : Function.Periodic V (0, Real.pi) := by
    intro x
    change (∑ n ∈ I, ve n (x.1 + 0) * referenceAngularBasis n (x.2 + Real.pi)) =
      ∑ n ∈ I, ve n x.1 * referenceAngularBasis n x.2
    simp only [add_zero]
    exact Finset.sum_congr rfl (fun n _ => by rw [referenceAngularBasis_periodic n x.2])
  have hVe : ∀ r θ, V (r, -θ) = V (r, θ) := by
    intro r θ
    apply Finset.sum_congr rfl
    intro n _hn
    rw [referenceAngularBasis_even n θ]
  have hVL (r : ℝ) (hr : r ≤ D.a) (θ : ℝ) : V (r, θ) = aL := by
    change (∑ n ∈ I, ve n r * referenceAngularBasis n θ) = aL
    rw [Finset.sum_eq_single 0]
    · rw [hleft 0 r hr]
      simp only [ite_true, referenceAngularBasis, mul_one]
    · intro n _hn hn0
      rw [hleft n r hr, if_neg hn0, zero_mul]
    · exact fun hn => (hn h0).elim
  have hVR (r : ℝ) (hr : D.b ≤ r) (θ : ℝ) : V (r, θ) = 0 := by
    change (∑ n ∈ I, ve n r * referenceAngularBasis n θ) = 0
    exact Finset.sum_eq_zero (fun n _ => by rw [hright n r hr, zero_mul])
  have hcoef (n : ℕ) :
      referenceRadialCoefficient U.1 n =ᵐ[volume.restrict (radialCore D)] ve n := by
    apply (hae n).trans
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hext n hr).symm
  have hPV : referenceBasisProjection I U.1 =ᵐ[radialPhysicalMeasure D] V := by
    rw [radialPhysicalMeasure_eq_prod]
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (radialCore D))
      (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))).ae (ae_all_iff.mpr hcoef)]
      with x hx
    change (∑ n ∈ I, referenceRadialCoefficient U.1 n x.1 * referenceAngularBasis n x.2) =
      ∑ n ∈ I, ve n x.1 * referenceAngularBasis n x.2
    exact Finset.sum_congr rfl (fun n _ => congrArg
      (fun z : ℝ => z * referenceAngularBasis n x.2) (hx n))
  have hUV : U.1 =ᵐ[radialPhysicalMeasure D] V :=
    (referenceGraph_eq_basisProjection hD hborder hγ hG hgraph h0 h1 hfix).trans hPV
  refine ⟨(V, U.2), referenceGraph_congr_ae hD hborder hγ hgraph hUV hVp hVe, ?_⟩
  exact ⟨hVs, hVp, aL, hVL, hVR⟩

end

end ContinuousFlexibility.Radial
