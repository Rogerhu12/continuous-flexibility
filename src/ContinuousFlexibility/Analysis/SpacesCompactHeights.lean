import ContinuousFlexibility.Analysis.SpacesCutoff
import ContinuousFlexibility.Analysis.CylinderTestPairing

/-!
# Compact radial functions in every physical height space

A smooth radial function supported in a compact subinterval belongs to
every weighted height class. The actual material coordinate sends its
support into a bounded interval; all material jets are therefore genuine
cylinder tests. In particular the derivative of the endpoint cutoff
supplies a compatible-source normalizer with integral one.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem spaces_cylinderTest_weight {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {φ : PolarPoint → ℝ} (hφ : IsCylinderTest φ) (c : ℕ) :
    IsCylinderTest (fun p : PolarPoint => T.M (T.radius p.1) ^ c * φ p) := by
  obtain ⟨hs, hp, _, _, _, _, hr, hinv, _⟩ := hT
  have hM : ContDiff ℝ ∞ (fun p : PolarPoint => T.M (T.radius p.1)) :=
    (hs T.M (by simp)).comp_contDiff (hr.comp contDiff_fst) (fun p => (hinv p.1).1)
  obtain ⟨R, hR, hzero⟩ := hφ.2.2
  refine ⟨(hM.pow c).mul hφ.1, ?_, R, hR, ?_⟩
  · intro p
    change T.M (T.radius (p.1 + 0)) ^ c * φ (p + (0, Real.pi)) = _
    rw [add_zero, hφ.2.1 p]
  · intro p hp
    change T.M (T.radius p.1) ^ c * φ p = 0
    rw [hzero p hp, mul_zero]

/-- Compact radial support remains bounded after the actual material
coordinate change, even though the cylinder itself is noncompact. -/
theorem spaces_radial_pullback_isCylinderTest {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hKD : K ⊆ Ioo D.a D.b)
    (hzero : ∀ r, r ∉ K → g r = 0) (γ : ℝ) :
    IsCylinderTest (materialPullback T γ (fun p : PolarPoint => g p.1)) := by
  have hρ : ContinuousOn T.rho K := (hT.1 T.rho (by simp)).continuousOn.mono hKD
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hρ
  have hinv := hT.2.2.2.2.2.2.2.1
  refine ⟨contDiff_materialPullback hT (hg.comp contDiff_fst).contDiffOn, ?_,
    max B 0 + 1, by positivity, ?_⟩
  · intro p
    simp only [materialPullback, Prod.fst_add, add_zero]
  · intro p hp
    have hout : T.radius p.1 ∉ K := by
      intro hr
      have hb := hB (T.radius p.1) hr
      rw [(hinv p.1).2, Real.norm_eq_abs] at hb
      have hmax : B ≤ max B 0 := le_max_left _ _
      linarith
    simp only [materialPullback, hzero _ hout, mul_zero]

theorem spaces_heightMember_of_compact_radial {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hKD : K ⊆ Ioo D.a D.b)
    (hzero : ∀ r, r ∉ K → g r = 0) (γ : ℝ) :
    HeightMember D T γ (fun p : PolarPoint => g p.1) := by
  have htest := spaces_radial_pullback_isCylinderTest hT hg hK hKD hzero γ
  refine ⟨(hg.comp contDiff_fst).contDiffOn, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro p
    simp only [Prod.fst_add, add_zero]
  · intro p hp
    apply hzero
    intro hKp
    exact hp ⟨hKD hKp, mem_univ _⟩
  · intro a b c
    exact (spaces_cylinderTest_weight hT (htest.mixedDerivative a b) c).memLp

theorem spaces_angularMean_const (c : ℝ) : angularMean (fun _ : ℝ => c) = c := by
  simp only [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

theorem spaces_physicalSourceIntegral_radial (D : ReferenceData) (g : ℝ → ℝ) :
    physicalSourceIntegral D (fun p : PolarPoint => g p.1) = ∫ r in D.a..D.b, g r := by
  simp only [physicalSourceIntegral, spaces_angularMean_const]

/-- The cutoff derivative is a concrete compactly supported source with
normalized physical integral. The construction works at every exponent. -/
theorem spaces_exists_compact_normalizer {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) (γ : ℝ) :
    ∃ ψ : PolarPoint → ℝ, HeightMember D T γ ψ ∧
      HasCompactRadialSupport D ψ ∧ physicalSourceIntegral D ψ = 1 := by
  obtain ⟨hsmooth, ⟨δ, hd, hdb, hleft, hright⟩, K, hK, hKD, hpos, hzero⟩ := hχ
  have hg : ContDiff ℝ ∞ (fun r => -deriv χ r) :=
    (contDiff_infty_iff_deriv.mp hsmooth).2.neg
  have hzero' : ∀ r, r ∉ K → -deriv χ r = 0 := by
    intro r hr
    rw [hzero r hr, neg_zero]
  refine ⟨fun p => -deriv χ p.1,
    spaces_heightMember_of_compact_radial hT hg hK hKD hzero' γ,
    ⟨K, hK, hKD, fun r hr _ => hzero' r hr⟩, ?_⟩
  rw [spaces_physicalSourceIntegral_radial D (fun r => -deriv χ r),
    intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun r _ => hsmooth.differentiable (by simp) r)
    ((contDiff_infty_iff_deriv.mp hsmooth).2.continuous.intervalIntegrable D.a D.b)]
  rw [hleft D.a (by linarith), hright D.b (by linarith)]
  norm_num

end ContinuousFlexibility.Statements
