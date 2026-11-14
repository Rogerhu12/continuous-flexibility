module

public import ContinuousFlexibility.Analysis.CompactEvenHeightTests
public import ContinuousFlexibility.Geometry.RotatedCoframe

/-!
# Actual even periodic coefficient probes

The radial linear test and the doubled-angle cosine test are multiplied
by one genuine smooth radial cutoff. They, their product, and the square
of the cosine test are actual height fields with zero endpoint constant.
On the open region where the cutoff is one their actual partials are the
coordinate partials needed to recover the mixed and angular coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def radialLinearProbe (χ : ℝ → ℝ) (p : PolarPoint) : ℝ := χ p.1 * p.1

def radialCosineProbe (χ : ℝ → ℝ) (p : PolarPoint) : ℝ :=
  χ p.1 * Real.cos (2 * p.2)

theorem contDiff_radialLinearProbe {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (radialLinearProbe χ) :=
  (hχ.comp contDiff_fst).mul contDiff_fst

theorem contDiff_radialCosineProbe {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (radialCosineProbe χ) :=
  (hχ.comp contDiff_fst).mul (contDiff_const.mul contDiff_snd).cos

theorem radialLinearProbe_even (χ : ℝ → ℝ) (r θ : ℝ) :
    radialLinearProbe χ (r, -θ) = radialLinearProbe χ (r, θ) := rfl

theorem radialCosineProbe_even (χ : ℝ → ℝ) (r θ : ℝ) :
    radialCosineProbe χ (r, -θ) = radialCosineProbe χ (r, θ) := by
  simp only [radialCosineProbe, mul_neg, Real.cos_neg]

theorem radialLinearProbe_periodic (χ : ℝ → ℝ) :
    Function.Periodic (radialLinearProbe χ) (0, Real.pi) := by
  intro p
  simp only [radialLinearProbe, Prod.fst_add, add_zero]

theorem radialCosineProbe_periodic (χ : ℝ → ℝ) :
    Function.Periodic (radialCosineProbe χ) (0, Real.pi) := by
  intro p
  simp only [radialCosineProbe, Prod.fst_add, Prod.snd_add, add_zero]
  rw [mul_add, Real.cos_add_two_pi]

theorem coefficientProbes_compactRadialSupport
    {D : ReferenceData} {χ : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hKD : K ⊆ Ioo D.a D.b)
    (hsupp : Function.support χ ⊆ K) :
    HasCompactRadialSupport D (radialLinearProbe χ) ∧
      HasCompactRadialSupport D (radialCosineProbe χ) := by
  have hzero (r : ℝ) (hr : r ∉ K) : χ r = 0 := by
    by_contra h
    exact hr (hsupp (Function.mem_support.mpr h))
  constructor
  · refine ⟨K, hK, hKD, ?_⟩
    intro r hr θ
    simp only [radialLinearProbe, hzero r hr, zero_mul]
  · refine ⟨K, hK, hKD, ?_⟩
    intro r hr θ
    simp only [radialCosineProbe, hzero r hr, zero_mul]

theorem hasCompactRadialSupport_mul_left
    {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : HasCompactRadialSupport D f) :
    HasCompactRadialSupport D (fun p => f p * g p) := by
  obtain ⟨K, hK, hKD, hzero⟩ := hf
  refine ⟨K, hK, hKD, ?_⟩
  intro r hr θ
  change f (r, θ) * g (r, θ) = 0
  rw [hzero r hr θ, zero_mul]

/-- Four actual height elements suffice for the two product-defect
identities. The same cutoff is used in all four fields. -/
theorem exists_heightPair_coefficientProbes
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {K : Set ℝ}
    (hK : IsCompact K) (hKD : K ⊆ Ioo D.a D.b)
    (hsupp : Function.support χ ⊆ K) :
    ∃ ηr ηc ηrc ηcc : HeightPair S,
      (ηr.2 = 0 ∧ heightPairField S ηr = radialLinearProbe χ) ∧
      (ηc.2 = 0 ∧ heightPairField S ηc = radialCosineProbe χ) ∧
      (ηrc.2 = 0 ∧ heightPairField S ηrc =
        fun p => radialLinearProbe χ p * radialCosineProbe χ p) ∧
      (ηcc.2 = 0 ∧ heightPairField S ηcc =
        fun p => radialCosineProbe χ p * radialCosineProbe χ p) := by
  have hr := contDiff_radialLinearProbe hχ
  have hc := contDiff_radialCosineProbe hχ
  have hs := coefficientProbes_compactRadialSupport hK hKD hsupp
  obtain ⟨ηr, hηr⟩ := exists_heightPair_of_compact_even_periodic hT hS
    hr.contDiffOn (radialLinearProbe_even χ) (radialLinearProbe_periodic χ) hs.1
  obtain ⟨ηc, hηc⟩ := exists_heightPair_of_compact_even_periodic hT hS
    hc.contDiffOn (radialCosineProbe_even χ) (radialCosineProbe_periodic χ) hs.2
  have hrc_even : ∀ r θ, radialLinearProbe χ (r, -θ) * radialCosineProbe χ (r, -θ) =
      radialLinearProbe χ (r, θ) * radialCosineProbe χ (r, θ) := by
    intro r θ
    rw [radialLinearProbe_even, radialCosineProbe_even]
  have hcc_even : ∀ r θ, radialCosineProbe χ (r, -θ) * radialCosineProbe χ (r, -θ) =
      radialCosineProbe χ (r, θ) * radialCosineProbe χ (r, θ) := by
    intro r θ
    rw [radialCosineProbe_even]
  have hrc_period : Function.Periodic
      (fun p => radialLinearProbe χ p * radialCosineProbe χ p) (0, Real.pi) := by
    intro p
    change radialLinearProbe χ (p + (0, Real.pi)) * radialCosineProbe χ (p + (0, Real.pi)) =
      radialLinearProbe χ p * radialCosineProbe χ p
    rw [radialLinearProbe_periodic χ p, radialCosineProbe_periodic χ p]
  have hcc_period : Function.Periodic
      (fun p => radialCosineProbe χ p * radialCosineProbe χ p) (0, Real.pi) := by
    intro p
    change radialCosineProbe χ (p + (0, Real.pi)) * radialCosineProbe χ (p + (0, Real.pi)) =
      radialCosineProbe χ p * radialCosineProbe χ p
    rw [radialCosineProbe_periodic χ p]
  obtain ⟨ηrc, hηrc⟩ := exists_heightPair_of_compact_even_periodic hT hS
    (hr.mul hc).contDiffOn hrc_even hrc_period (hasCompactRadialSupport_mul_left hs.1)
  obtain ⟨ηcc, hηcc⟩ := exists_heightPair_of_compact_even_periodic hT hS
    (hc.mul hc).contDiffOn hcc_even hcc_period (hasCompactRadialSupport_mul_left hs.2)
  exact ⟨ηr, ηc, ηrc, ηcc, hηr, hηc, hηrc, hηcc⟩

/-- These are equalities of actual germs, not prescribed derivatives of
the probes. No coefficient field appears in this localization step. -/
theorem coefficientProbes_germs {χ : ℝ → ℝ} {p : PolarPoint}
    (hχ : χ =ᶠ[𝓝 p.1] (fun _ : ℝ => 1)) :
    radialLinearProbe χ =ᶠ[𝓝 p] Prod.fst ∧
      radialCosineProbe χ =ᶠ[𝓝 p] (fun q => Real.cos (2 * q.2)) := by
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, χ q.1 = 1 :=
    continuous_fst.continuousAt.eventually hχ
  constructor
  · filter_upwards [hnear] with q hq
    simp only [radialLinearProbe, hq, one_mul]
  · filter_upwards [hnear] with q hq
    simp only [radialCosineProbe, hq, one_mul]

/-- Actual radial and angular partials on the region where the genuine
radial cutoff is one. The double-angle factor is responsible for the
single and double sine zeros in coefficient recovery. -/
theorem coefficientProbes_partials {χ : ℝ → ℝ} {p : PolarPoint}
    (hχ : χ =ᶠ[𝓝 p.1] (fun _ : ℝ => 1)) :
    radialPartial (radialLinearProbe χ) p = 1 ∧
      angularPartial (radialLinearProbe χ) p = 0 ∧
      radialPartial (radialCosineProbe χ) p = 0 ∧
      angularPartial (radialCosineProbe χ) p = -2 * Real.sin (2 * p.2) := by
  have hg := coefficientProbes_germs hχ
  have hrad := hg.1.fderiv_eq (𝕜 := ℝ)
  have hcos := hg.2.fderiv_eq (𝕜 := ℝ)
  have hphase : DifferentiableAt ℝ (fun q : PolarPoint => (2 : ℝ) * q.2) p :=
    (differentiableAt_const (2 : ℝ)).mul differentiableAt_snd
  have hpr : radialPartial (fun q : PolarPoint => (2 : ℝ) * q.2) p = 0 := by
    rw [radialPartial_mul (differentiableAt_const (2 : ℝ)) differentiableAt_snd]
    simp only [radialPartial_const, radialPartial_snd, zero_mul, mul_zero, add_zero]
  have hpt : angularPartial (fun q : PolarPoint => (2 : ℝ) * q.2) p = 2 := by
    rw [angularPartial_mul (differentiableAt_const (2 : ℝ)) differentiableAt_snd]
    simp only [angularPartial_const, angularPartial_snd, zero_mul, mul_one, zero_add]
  have hr1 : radialPartial (radialLinearProbe χ) p = radialPartial Prod.fst p :=
    congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hrad
  have ht1 : angularPartial (radialLinearProbe χ) p = angularPartial Prod.fst p :=
    congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hrad
  have hr2 : radialPartial (radialCosineProbe χ) p =
      radialPartial (fun q => Real.cos (2 * q.2)) p :=
    congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hcos
  have ht2 : angularPartial (radialCosineProbe χ) p =
      angularPartial (fun q => Real.cos (2 * q.2)) p :=
    congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hcos
  refine ⟨hr1.trans radialPartial_fst, ht1.trans angularPartial_fst, ?_, ?_⟩
  · rw [hr2, radialPartial_cos hphase, hpr, mul_zero]
  · rw [ht2, angularPartial_cos hphase, hpt]
    ring

end ContinuousFlexibility.Analysis
