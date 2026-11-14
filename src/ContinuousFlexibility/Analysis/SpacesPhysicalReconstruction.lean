module

public import ContinuousFlexibility.Analysis.SpacesJetLimits
public import ContinuousFlexibility.Analysis.SpacesPhysicalUniqueness

/-!
# Smooth representatives of the physical weak jet limit

The actual compatible weak jets determine a smooth periodic function on
material coordinates. Normalized compact bump convolutions converge in
local integral norm; the cylinder estimate promotes the complete mixed
jet tower to classical smoothness. Lebesgue differentiation identifies
every resulting classical jet with its original weak `L²` class.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology Convolution

set_option backward.isDefEq.respectTransparency false

/-- A fixed smooth approximation to the identity, with bounded ratio of
outer and inner radii. -/
def spacesMollifierBump (n : ℕ) : ContDiffBump (0 : PolarPoint) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

theorem spacesMollifierBump_tendsto :
    Tendsto (fun n => (spacesMollifierBump n).rOut) atTop (𝓝 0) := by
  simpa only [spacesMollifierBump, div_eq_mul_inv, one_mul, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

theorem spacesMollifierBump_ratio (n : ℕ) :
    (spacesMollifierBump n).rOut ≤ 2 * (spacesMollifierBump n).rIn := by
  simp only [spacesMollifierBump, div_eq_mul_inv, one_mul, le_refl]

/-- Swap the scalar convolution to put its compact kernel first. -/
theorem spaces_planarConvolution_eq_left (f κ : PolarPoint → ℝ) :
    planarConvolution f κ = κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  funext p
  rw [planarConvolution_apply, convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

/-- One fixed mollification sequence for a compatible physical weak jet. -/
def spacesPhysicalMollification (u : PhysicalJetProjectiveLimit hT) (n : ℕ) :
    PolarPoint → ℝ :=
  physicalJetMollification hT u ((spacesMollifierBump n).normed volume)

theorem spacesPhysicalMollification_contDiff (u : PhysicalJetProjectiveLimit hT) (n : ℕ) :
    ContDiff ℝ ∞ (spacesPhysicalMollification hT u n) :=
  contDiff_physicalJetMollification hT u (spacesMollifierBump n).contDiff_normed
    (spacesMollifierBump n).hasCompactSupport_normed

theorem spacesPhysicalMollification_periodic (u : PhysicalJetProjectiveLimit hT) (n : ℕ) :
    Function.Periodic (spacesPhysicalMollification hT u n) (0, Real.pi) :=
  physicalJetMollification_periodic hT u _

/-- Every mixed derivative is the same fixed convolution of the matching
pure weak derivative class. -/
theorem spacesPhysicalMollification_mixedDerivative
    (u : PhysicalJetProjectiveLimit hT) (n a b : ℕ) :
    mixedDerivative a b (spacesPhysicalMollification hT u n) =
      (spacesMollifierBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        cylinderPeriodicExtension (physicalJetMixedDerivative u a b) := by
  rw [spacesPhysicalMollification, physicalJetMollification,
    (physicalJetMixedDerivative_spec u a b).periodicConvolution
      (spacesMollifierBump n).contDiff_normed (spacesMollifierBump n).hasCompactSupport_normed,
    spaces_planarConvolution_eq_left]

/-- Existence of the genuine smooth periodic material representative,
with all classical mixed derivatives equal almost everywhere to their
prescribed weak derivative classes. -/
theorem spaces_exists_smooth_physicalRepresentative (u : PhysicalJetProjectiveLimit hT) :
    ∃ v : PolarPoint → ℝ, ContDiff ℝ ∞ v ∧ Function.Periodic v (0, Real.pi) ∧
      (∀ a b, mixedDerivative a b v =ᵐ[volume]
        cylinderPeriodicExtension (physicalJetMixedDerivative u a b)) ∧
      ∀ a b, TendstoLocallyUniformly (fun n => mixedDerivative a b (spacesPhysicalMollification hT u n))
        (mixedDerivative a b v) atTop := by
  have hlim (a b : ℕ) (K : Set PolarPoint) (hK : IsCompact K) :
      Tendsto (fun n => ∫ p in K,
        |mixedDerivative a b (spacesPhysicalMollification hT u n) p -
          cylinderPeriodicExtension (physicalJetMixedDerivative u a b) p|) atTop (𝓝 0) := by
    simp_rw [spacesPhysicalMollification_mixedDerivative]
    exact spaces_tendsto_setIntegral_abs_bump_convolution_sub spacesMollifierBump_tendsto
      (locallyIntegrable_cylinderPeriodicExtension _) hK
  have hp (n : ℕ) (x : ℝ) :
      Function.Periodic (fun θ => spacesPhysicalMollification hT u n (x, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using
      spacesPhysicalMollification_periodic hT u n (x, θ)
  obtain ⟨v, hv, hvp, hvl⟩ := spaces_exists_smooth_periodic_of_local_L1_jets
    (spacesPhysicalMollification hT u)
    (fun a b => cylinderPeriodicExtension (physicalJetMixedDerivative u a b))
    (spacesPhysicalMollification_contDiff hT u) hp
    (fun _ _ => locallyIntegrable_cylinderPeriodicExtension _) hlim
  refine ⟨v, hv, hvp, ?_, hvl⟩
  intro a b
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    spacesMollifierBump_tendsto (Eventually.of_forall spacesMollifierBump_ratio)
    (locallyIntegrable_cylinderPeriodicExtension (physicalJetMixedDerivative u a b))
  filter_upwards [hae] with p hp
  have hvpoint := (hvl a b).tendstoLocallyUniformlyOn.tendsto_at (mem_univ p)
  simp_rw [spacesPhysicalMollification_mixedDerivative] at hvpoint
  exact tendsto_nhds_unique hvpoint hp

/-- The canonical choice of the smooth material representative. All
subsequent identities follow from uniqueness, independently of this choice. -/
def spacesPhysicalRepresentative (u : PhysicalJetProjectiveLimit hT) : PolarPoint → ℝ :=
  (spaces_exists_smooth_physicalRepresentative hT u).choose

theorem spacesPhysicalRepresentative_contDiff (u : PhysicalJetProjectiveLimit hT) :
    ContDiff ℝ ∞ (spacesPhysicalRepresentative hT u) :=
  (spaces_exists_smooth_physicalRepresentative hT u).choose_spec.1

theorem spacesPhysicalRepresentative_periodic (u : PhysicalJetProjectiveLimit hT) :
    Function.Periodic (spacesPhysicalRepresentative hT u) (0, Real.pi) :=
  (spaces_exists_smooth_physicalRepresentative hT u).choose_spec.2.1

theorem spacesPhysicalRepresentative_mixedDerivative_ae (u : PhysicalJetProjectiveLimit hT)
    (a b : ℕ) : mixedDerivative a b (spacesPhysicalRepresentative hT u) =ᵐ[volume]
      cylinderPeriodicExtension (physicalJetMixedDerivative u a b) :=
  (spaces_exists_smooth_physicalRepresentative hT u).choose_spec.2.2.1 a b

theorem spacesPhysicalRepresentative_mixedDerivative_cylinder_ae
    (u : PhysicalJetProjectiveLimit hT) (a b : ℕ) :
    mixedDerivative a b (spacesPhysicalRepresentative hT u) =ᵐ[materialCylinderMeasure]
      physicalJetMixedDerivative u a b :=
  ((spacesPhysicalRepresentative_mixedDerivative_ae hT u a b).filter_mono
    (ae_mono Measure.restrict_le_self)).trans (cylinderPeriodicExtension_ae _)

theorem spacesPhysicalRepresentative_locallyUniform (u : PhysicalJetProjectiveLimit hT)
    (a b : ℕ) :
    TendstoLocallyUniformly (fun n => mixedDerivative a b (spacesPhysicalMollification hT u n))
      (mixedDerivative a b (spacesPhysicalRepresentative hT u)) atTop :=
  (spaces_exists_smooth_physicalRepresentative hT u).choose_spec.2.2.2 a b

end ContinuousFlexibility.Statements
