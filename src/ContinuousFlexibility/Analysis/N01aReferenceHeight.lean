import ContinuousFlexibility.Analysis.N01aReferenceHeightRadial
import ContinuousFlexibility.Analysis.N01aReferenceWeightedRealizations
import ContinuousFlexibility.Analysis.CylinderTestPairing
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# The actual reference eigenfield belongs to the physical height space

Both initial radial moments follow from the reference inverse and its
first-normal estimate. The actual Jacobi equation supplies higher jets,
and the proved affine coordinate transfers their integrals. This proves
the frozen height membership without an extra regularity premise.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n01a_material_memLp_separated {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : Continuous g) :
    MemLp (fun p : PolarPoint => f p.1 * g p.2) 2 materialCylinderMeasure := by
  letI : IsFiniteMeasure angleMeasure := by unfold angleMeasure; infer_instance
  have hfst : MemLp (fun p : PolarPoint => f p.1) 2 materialCylinderMeasure := by
    rw [materialCylinderMeasure_eq_prod]
    exact hf.comp_fst angleMeasure
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) Real.pi)).exists_bound_of_continuousOn
    hg.continuousOn
  have hmajor : MemLp (fun p : PolarPoint => max B 0 * ‖f p.1‖) 2 materialCylinderMeasure :=
    hfst.norm.const_mul (max B 0)
  have hmeas : AEStronglyMeasurable (fun p : PolarPoint => f p.1 * g p.2)
      materialCylinderMeasure :=
    hfst.aestronglyMeasurable.mul (hg.comp continuous_snd).aestronglyMeasurable
  apply hmajor.mono' hmeas
  have hangle : ∀ᵐ p ∂materialCylinderMeasure, p.2 ∈ Icc (0 : ℝ) Real.pi :=
    (ae_restrict_mem (μ := (volume : Measure PolarPoint))
      (measurableSet_univ.prod measurableSet_Ioc)).mono
      (fun p hp => ⟨hp.2.1.le, hp.2.2⟩)
  filter_upwards [hangle] with p hp
  rw [norm_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    ((hB p.2 hp).trans (le_max_left B 0)) (norm_nonneg (f p.1))

theorem n01a_mixedDerivative_separated (f g : ℝ → ℝ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q : PolarPoint => f q.1 * g q.2) p =
      iteratedDeriv a f p.1 * iteratedDeriv b g p.2 := by
  unfold mixedDerivative
  have heq : (fun r => iteratedDeriv b (fun θ => f r * g θ) p.2) =
      (fun r => f r * iteratedDeriv b g p.2) := by
    funext r
    exact iteratedDeriv_const_mul_field (f r) g
  rw [heq, iteratedDeriv_mul_const_field]

/-- The actual second cosine eigenfield has every weighted physical jet
required by the height model, for any choice of affine samples. -/
theorem n01a_reference_heightMember {D : ReferenceData} (hD : IsRadialReference D)
    (sample : ℕ → ℝ) :
    HeightMember D (affineMaterialData D sample) referenceBeta
      (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) := by
  obtain ⟨C, hprofile⟩ := hD.1
  have hgeom := hprofile.1
  have hcos : ContDiff ℝ ∞ (Radial.cosineMode 2) := by
    unfold Radial.cosineMode
    exact contDiff_const.mul ((contDiff_const.mul contDiff_id).cos)
  have hfield : ContDiff ℝ ∞ (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) :=
    (hgeom.2.2.2.1.1.comp contDiff_fst).mul (hcos.comp contDiff_snd)
  refine ⟨hfield.contDiffOn, ?_, ?_, ?_, ?_⟩
  · intro r θ
    change D.phi r * Radial.cosineMode 2 (-θ) = D.phi r * Radial.cosineMode 2 θ
    rw [Radial.cosineMode_even 2 θ]
  · rintro ⟨r, θ⟩
    change D.phi (r + 0) * Radial.cosineMode 2 (θ + Real.pi) = D.phi r * Radial.cosineMode 2 θ
    have hp : Radial.cosineMode 2 (θ + Real.pi) = Radial.cosineMode 2 θ := by
      simpa only [Nat.mul_one] using Radial.cosineMode_even_frequency_periodic 1 θ
    rw [add_zero, hp]
  · intro p hp
    have hr : p.1 ≤ D.a ∨ D.b ≤ p.1 := by
      by_cases hl : p.1 ≤ D.a
      · exact Or.inl hl
      · right
        by_contra hr
        exact hp ⟨⟨lt_of_not_ge hl, lt_of_not_ge hr⟩, mem_univ _⟩
    change D.phi p.1 * Radial.cosineMode 2 p.2 = 0
    rw [hgeom.2.2.2.1.2 p.1 hr, zero_mul]
  · intro a b c
    obtain ⟨ε, M, hε, hεsmall, hphi, hphi'⟩ :=
      exists_reference_eigenfield_weighted_realizations hD
    have hradial := n01a_reference_weighted_radial_jets_memLp (sample := sample) hD
      (show 0 ≤ referenceBeta by norm_num [referenceBeta]) hε hphi hphi' a c
    have hsep := n01a_material_memLp_separated hradial
      (hcos.continuous_iteratedDeriv b (by simp))
    let T := affineMaterialData D sample
    have hpull : materialPullback T referenceBeta
        (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) =
        (fun p : PolarPoint => n01aReferenceWeightedRadial D sample referenceBeta p.1 *
          Radial.cosineMode 2 p.2) := by
      funext p
      dsimp only [materialPullback, n01aReferenceWeightedRadial, T]
      ring
    have hjet : weightedPhysicalJet T referenceBeta a b c
        (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) =
        (fun p : PolarPoint =>
          (T.M (T.radius p.1) ^ c *
            iteratedDeriv a (n01aReferenceWeightedRadial D sample referenceBeta) p.1) *
          iteratedDeriv b (Radial.cosineMode 2) p.2) := by
      funext p
      rw [weightedPhysicalJet, hpull, n01a_mixedDerivative_separated]
      ring
    rw [hjet]
    exact hsep

end ContinuousFlexibility.Statements
