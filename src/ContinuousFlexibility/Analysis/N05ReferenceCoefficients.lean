import ContinuousFlexibility.Analysis.N05CoefficientRigidity
import ContinuousFlexibility.Analysis.N05LocalEvenTests

/-!
# Identifying the corrected reference coefficients on genuine local tests

N01 determines the original radial coefficients.  The actual N02 residual is
zero, and the actual physical decoder realizes every smooth germ away from
the reflection circles.  Polynomial probes therefore force the corrected
mixed and angular coefficients to be the radial ones; their regularity is
a conclusion, not an extra frozen hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def n05RadialReferenceCoefficients (D : ReferenceData) : SymmetricCoefficients where
  a := fun p => D.w p.1
  b := fun _ => 0
  c := fun p => deriv D.w p.1 / p.1

theorem n05_originalReference_divergence_eq
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : IsAccumulatingProfile D) (hC : referenceStateConditions D S C)
    (f : PolarPoint → ℝ) (p : PolarPoint) :
    divergenceOperator (originalCoefficients D S C (C.referenceState, 0)) f p =
      divergenceOperator (n05RadialReferenceCoefficients D) f p := by
  have ha : (originalCoefficients D S C (C.referenceState, 0)).a = fun q => D.w q.1 :=
    funext (fun q => (n05_originalCoefficients_reference hD hC q).1)
  have hb : (originalCoefficients D S C (C.referenceState, 0)).b = fun _ => 0 :=
    funext (fun q => (n05_originalCoefficients_reference hD hC q).2.1)
  have hc : (originalCoefficients D S C (C.referenceState, 0)).c =
      fun q => deriv D.w q.1 / q.1 :=
    funext (fun q => (n05_originalCoefficients_reference hD hC q).2.2)
  simp only [divergenceOperator, ha, hb, hc, n05RadialReferenceCoefficients]

theorem n05_radialReference_regular
    {D : ReferenceData} (hD : IsAccumulatingProfile D) {p : PolarPoint}
    (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (n05RadialReferenceCoefficients D).a p ∧
      ContDiffAt ℝ ∞ (n05RadialReferenceCoefficients D).b p ∧
      ContDiffAt ℝ ∞ (n05RadialReferenceCoefficients D).c p ∧
      angularPartial (n05RadialReferenceCoefficients D).c p = 0 := by
  obtain ⟨B, hB⟩ := hD
  have hw : ContDiff ℝ ∞ D.w := hB.1.2.2.1.1
  have hwr : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hr : p.1 ≠ 0 := (hB.1.1.trans hp.1.1).ne'
  refine ⟨hw.contDiffAt.comp p contDiffAt_fst, contDiffAt_const,
    (hwr.contDiffAt.comp p contDiffAt_fst).div contDiffAt_fst hr, ?_⟩
  exact Radial.angularPartial_radialHeightField
    ((hwr.differentiable (by simp) p.1).div differentiableAt_id hr)

/-- The corrected reference coefficients are identified from actual N01--N03
data at every non-root, non-reflection point. -/
theorem n05_reference_coefficients_nonreflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) (hd : deriv D.w p.1 ≠ 0)
    (hθ : p.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))) :
    DifferentiableAt ℝ (L.coefficients (C.referenceState, 0)).b p ∧
      DifferentiableAt ℝ (L.coefficients (C.referenceState, 0)).c p ∧
      (L.coefficients (C.referenceState, 0)).b p = 0 ∧
      (L.coefficients (C.referenceState, 0)).c p = deriv D.w p.1 / p.1 := by
  let P := L.coefficients (C.referenceState, 0)
  let A := n05RadialReferenceCoefficients D
  have h01 := h.1.1
  have hD := h01.1.1
  have hC := h01.2.2.1
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector hC
  have hAeq : P.a = A.a := by
    funext q
    exact (h.2.1 (C.referenceState, 0) hmem hsector q).trans
      (n05_originalCoefficients_reference hD hC q).1
  obtain ⟨haA, hbA, hcA, hAcθ⟩ := n05_radialReference_regular hD hp
  have daA := haA.differentiableAt (by simp)
  have dbA := hbA.differentiableAt (by simp)
  have dcA := hcA.differentiableAt (by simp)
  have daP : DifferentiableAt ℝ P.a p := by rw [hAeq]; exact daA
  obtain ⟨B, hB⟩ := hD
  have hr : p.1 ≠ 0 := (hB.1.1.trans hp.1.1).ne'
  have ha0 : P.a p ≠ 0 := by
    rw [hAeq]
    exact (hB.1.2.2.2.2.1 p.1 hp.1).ne'
  have hc0 : deriv D.w p.1 / p.1 ≠ 0 := div_ne_zero hd hr
  have hop (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u) :
      divergenceOperator P u p = divergenceOperator A u p :=
    (n05_reference_correctionOperator_eq_local hT hS h isOpen_univ hu.contDiffOn
      (mem_univ p) hp hθ).symm.trans
        (n05_originalReference_divergence_eq ⟨B, hB⟩ hC u p)
  have hR (s : ℝ) : divergenceOperator P (n05RadialProbe p s) p = 2 * s * P.a p := by
    rw [hop _ (n05RadialProbe_contDiff p s),
      n05_divergence_radialProbe daA dbA dcA, hAcθ]
    simp only [A, n05RadialReferenceCoefficients, radialPartial_const, add_zero, hAeq]
  have hTprobe (s : ℝ) :
      divergenceOperator P (n05AngularProbe p s) p = 2 * s * (deriv D.w p.1 / p.1) := by
    rw [hop _ (n05AngularProbe_contDiff p s),
      n05_divergence_angularProbe dbA dcA, hAcθ]
    simp only [A, n05RadialReferenceCoefficients, radialPartial_const, zero_add]
  have hRT : divergenceOperator P (n05MixedProbe p) p = 0 := by
    rw [hop _ (n05MixedProbe_contDiff p), n05_divergence_mixedProbe daA dbA dcA]
    simp only [A, n05RadialReferenceCoefficients, mul_zero]
  exact n05_coefficients_rigid_at daP ha0 hc0 hR hTprobe hRT

private theorem n05_chamber_not_reflection {n : ℤ} {θ : ℝ}
    (hθ : θ ∈ Ioo ((n : ℝ) * (Real.pi / 2)) (((n : ℝ) + 1) * (Real.pi / 2))) :
    θ ∉ Set.range (fun k : ℤ => (k : ℝ) * (Real.pi / 2)) := by
  rintro ⟨k, rfl⟩
  have hπ : 0 ≤ Real.pi / 2 := (half_pos Real.pi_pos).le
  have hlo : (n : ℝ) < (k : ℝ) := lt_of_mul_lt_mul_right hθ.1 hπ
  have hhi : (k : ℝ) < (n : ℝ) + 1 := lt_of_mul_lt_mul_right hθ.2 hπ
  have hlo' : n < k := by exact_mod_cast hlo
  have hhi' : k < n + 1 := by exact_mod_cast hhi
  omega

/-- The pointwise coefficient identification holds on a whole neighborhood.
Consequently all smoothness premises for the true symbol formula are now
proved from the frozen input at non-reflection points. -/
theorem n05_reference_coefficients_contDiffAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) (hd : deriv D.w p.1 ≠ 0)
    (hθ : p.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))) :
    ContDiffAt ℝ ∞ (L.coefficients (C.referenceState, 0)).a p ∧
      ContDiffAt ℝ ∞ (L.coefficients (C.referenceState, 0)).b p ∧
      ContDiffAt ℝ ∞ (L.coefficients (C.referenceState, 0)).c p := by
  have h01 := h.1.1
  have hD := h01.1.1
  obtain ⟨B, hB⟩ := hD
  have hw : ContDiff ℝ ∞ D.w := hB.1.2.2.1.1
  obtain ⟨n, hn⟩ := n05_exists_angular_chamber hθ
  have hnearD : ∀ᶠ q : PolarPoint in 𝓝 p, q ∈ annularOpen D :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hnearSlope : ∀ᶠ q : PolarPoint in 𝓝 p, deriv D.w q.1 ≠ 0 :=
    (isOpen_ne_fun ((hw.continuous_deriv (by simp)).comp continuous_fst)
      continuous_const).mem_nhds hd
  have hnearAngle : ∀ᶠ q : PolarPoint in 𝓝 p,
      q.2 ∈ Ioo ((n : ℝ) * (Real.pi / 2)) (((n : ℝ) + 1) * (Real.pi / 2)) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hn
  have hBgerm : (L.coefficients (C.referenceState, 0)).b =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hnearD, hnearSlope, hnearAngle] with q hq hqd hqθ
    exact (n05_reference_coefficients_nonreflection hT hS h hq hqd
      (n05_chamber_not_reflection hqθ)).2.2.1
  have hCgerm : (L.coefficients (C.referenceState, 0)).c =ᶠ[𝓝 p]
      (n05RadialReferenceCoefficients D).c := by
    filter_upwards [hnearD, hnearSlope, hnearAngle] with q hq hqd hqθ
    exact (n05_reference_coefficients_nonreflection hT hS h hq hqd
      (n05_chamber_not_reflection hqθ)).2.2.2
  have hAeq : (L.coefficients (C.referenceState, 0)).a =
      (n05RadialReferenceCoefficients D).a := by
    funext q
    exact (h.2.1 (C.referenceState, 0) (n05_referenceState_mem h01.2.1)
      (n05_referenceState_sector h01.2.2.1) q).trans
      (n05_originalCoefficients_reference ⟨B, hB⟩ h01.2.2.1 q).1
  obtain ⟨ha, _, hc, _⟩ := n05_radialReference_regular ⟨B, hB⟩ hp
  refine ⟨?_, contDiffAt_const.congr_of_eventuallyEq hBgerm,
    hc.congr_of_eventuallyEq hCgerm⟩
  rw [hAeq]
  exact ha

end ContinuousFlexibility.Statements

