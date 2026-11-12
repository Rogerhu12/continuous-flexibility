import ContinuousFlexibility.Analysis.N06NuPhysicalSmooth
import ContinuousFlexibility.Analysis.NeighborhoodCharacteristicSpeedExtension
import ContinuousFlexibility.Analysis.RootCharacteristicFactor

/-!
# The actual root fields as finite functions of the original state

The N01 root germ fixes the entire radial profile. The drift and the
speed divided by its reference factor then depend only on the genuine
height packet already used for the physical nu column. These are exact
germ identities for the original state height, so they identify every
ordinary spatial derivative at the root.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

def n06RootFiniteQ (v : N06NuJetCoordinates) : ℝ :=
  v 1 + v 10 * (v 5 + (1 + v 1 ^ 2) * v 9)

def n06RootFiniteDiscriminant (v : N06NuJetCoordinates) : ℝ :=
  (1 + v 1 ^ 2) * (1 - (v 10 * v 7) ^ 2) - (v 1 + v 10 * v 5) ^ 2

def n06RootFiniteFields (v : N06NuJetCoordinates) : PolarPoint :=
  (-(1 + v 1 ^ 2) * v 10 * v 8 / n06RootFiniteQ v,
    v 1 * Real.sqrt (n06RootFiniteDiscriminant v) / n06RootFiniteQ v)

theorem n06RootFiniteQ_contDiff : ContDiff ℝ ∞ n06RootFiniteQ := by
  have hc (i : Fin 12) : ContDiff ℝ ∞ (fun v : N06NuJetCoordinates => v i) :=
    contDiff_apply ℝ ℝ i
  exact (hc 1).add ((hc 10).mul ((hc 5).add
    ((contDiff_const.add ((hc 1).pow 2)).mul (hc 9))))

theorem n06RootFiniteDiscriminant_contDiff : ContDiff ℝ ∞ n06RootFiniteDiscriminant := by
  have hc (i : Fin 12) : ContDiff ℝ ∞ (fun v : N06NuJetCoordinates => v i) :=
    contDiff_apply ℝ ℝ i
  exact ((contDiff_const.add ((hc 1).pow 2)).mul
    (contDiff_const.sub (((hc 10).mul (hc 7)).pow 2))).sub
      (((hc 1).add ((hc 10).mul (hc 5))).pow 2)

theorem n06RootFiniteFields_contDiffAt {v : N06NuJetCoordinates}
    (hQ : n06RootFiniteQ v ≠ 0) (hD : 0 < n06RootFiniteDiscriminant v) :
    ContDiffAt ℝ ∞ n06RootFiniteFields v := by
  have hc (i : Fin 12) : ContDiffAt ℝ ∞ (fun w : N06NuJetCoordinates => w i) v :=
    (contDiff_apply ℝ ℝ i).contDiffAt
  have hE : ContDiffAt ℝ ∞ (fun w : N06NuJetCoordinates => 1 + w 1 ^ 2) v :=
    contDiffAt_const.add ((hc 1).pow 2)
  exact (((hE.neg.mul (hc 10)).mul (hc 8)).div n06RootFiniteQ_contDiff.contDiffAt hQ).prodMk
    (((hc 1).mul (n06RootFiniteDiscriminant_contDiff.contDiffAt.sqrt hD.ne')).div
      n06RootFiniteQ_contDiff.contDiffAt hQ)

theorem n06RootFiniteFields_parameter_zero {v : N06NuJetCoordinates}
    (hq : v 10 = 0) (hw : v 1 ≠ 0) : n06RootFiniteFields v = (0, 1) := by
  have hQ : n06RootFiniteQ v = v 1 := by simp only [n06RootFiniteQ, hq, zero_mul, add_zero]
  have hDisc : n06RootFiniteDiscriminant v = 1 := by
    simp only [n06RootFiniteDiscriminant, hq, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      sub_zero, mul_one, add_zero]
    ring
  rw [n06RootFiniteFields, hQ, hDisc]
  simp only [hq, mul_zero, zero_mul, zero_div, Real.sqrt_one, mul_one, div_self hw]

theorem n06_characteristicDrift_eq_polarJets
    {w : ℝ → ℝ} {Z : PolarPoint → ℝ} {p : PolarPoint}
    (hZ : ContDiffAt ℝ 2 Z p) (hr : p.1 ≠ 0) :
    characteristicDrift w Z p =
      -profileEnergy w p * radialPartial (heightAngular Z) p /
        heightQ (profileEnergy w p) (heightRadial Z p)
          (angularPartial (heightAngular Z) p) := by
  have hcompat := height_compatibility hZ hr
  have hdiff : heightAngular Z p - angularPartial (heightRadial Z) p =
      -(p.1 * radialPartial (heightAngular Z) p) := by linarith only [hcompat]
  rw [characteristicDrift, hdiff]
  calc
    _ = (p.1 * (-profileEnergy w p * radialPartial (heightAngular Z) p)) /
        (p.1 * heightQ (profileEnergy w p) (heightRadial Z p)
          (angularPartial (heightAngular Z) p)) := by congr 1; ring
    _ = _ := mul_div_mul_left _ _ hr

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The second coordinate is the actual characteristic speed divided by
its fixed reference root factor. -/
def n06PhysicalRootFields (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (p : PolarPoint) : PolarPoint :=
  (characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) p,
    D.w p.1 * Real.sqrt (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p) /
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p))

/-- These are the actual two coefficients passed to the regular root
flow after orienting the physical radial coordinate. -/
theorem n06_factoredRootFields_eq_physical
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (g : ℝ → ℝ) (r σ : ℝ) (p : PolarPoint)
    (hw : D.w (rootProfileShift r σ p).1 ≠ 0) :
    orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ p =
        σ * (n06PhysicalRootFields D S C z (rootProfileShift r σ p)).1 ∧
      factoredCharacteristicSpeed D.w g (stateProfile D S C z.1) (stateHeight D S C z) r σ p =
        referenceRootSpeedFactor D.w g r σ p.1 *
          (n06PhysicalRootFields D S C z (rootProfileShift r σ p)).2 := by
  refine ⟨rfl, ?_⟩
  simp only [factoredCharacteristicSpeed, referenceRootSpeedFactor,
    n06PhysicalRootFields, rootProfileShift, div_eq_mul_inv]
  have hcancel : (D.w (r + σ * p.1))⁻¹ * D.w (r + σ * p.1) = 1 :=
    inv_mul_cancel₀ hw
  calc
    _ = Real.sqrt (rootProfileRadicand D.w g r σ p.1) *
        ((D.w (r + σ * p.1))⁻¹ * D.w (r + σ * p.1)) *
        Real.sqrt (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z)
          (r + σ * p.1, p.2)) *
        (heightQ (profileEnergy (stateProfile D S C z.1) (r + σ * p.1, p.2))
          (heightRadial (stateHeight D S C z) (r + σ * p.1, p.2))
          (angularPartial (heightAngular (stateHeight D S C z)) (r + σ * p.1, p.2)))⁻¹ := by
      rw [hcancel, mul_one]
    _ = _ := by ring

private theorem n06_stateHeight_radialAngular_of_profile
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {z : AnnularState S × ℝ} (hw : ContDiff ℝ ∞ (stateProfile D S C z.1))
    {p : PolarPoint} (hr : p.1 ≠ 0) :
    radialPartial (heightAngular (stateHeight D S C z)) p =
      z.2 * radialPartial (heightAngular (stateU S z.1)) p := by
  have hh := contDiff_radialHeightField (stateRadialHeight_contDiff_of_contDiff hw)
  have hu := neighborhood_stateU_contDiff hT hS z.1
  change radialPartial (heightAngular (heightFamily
    (radialHeightField (stateRadialHeight D S C z.1)) (stateU S z.1) z.2)) p = _
  rw [radialPartial_heightAngular_heightFamily hh hu hr,
    heightAngular_radialHeightField (stateRadialHeight_hasDerivAt_of_contDiff hw),
    radialPartial_const, zero_add]

theorem n06_rootFinite_denominators_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hr : p.1 ≠ 0)
    (hprofile : stateProfile D S C z.1 p.1 = D.w p.1) :
    n06RootFiniteQ (n06ActualNuJetCoordinates D S z p) =
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) ∧
    n06RootFiniteDiscriminant (n06ActualNuJetCoordinates D S z p) =
      polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
  constructor
  · change D.w p.1 + z.2 * (radialPartial (stateU S z.1) p +
      (1 + D.w p.1 ^ 2) * angularPartial (heightAngular (stateU S z.1)) p) = _
    simp only [heightQ, stateHeight_heightRadial_of_contDiff_profile hT hS hw,
      stateHeight_angularPartial_heightAngular_of_contDiff_profile hT hS hw hr,
      profileEnergy, radialEnergy, hprofile]
    ring
  · change (1 + D.w p.1 ^ 2) * (1 - (z.2 * heightAngular (stateU S z.1) p) ^ 2) -
      (D.w p.1 + z.2 * radialPartial (stateU S z.1) p) ^ 2 = _
    simp only [polarDiscriminant, stateHeight_heightRadial_of_contDiff_profile hT hS hw,
      stateHeight_heightAngular_of_contDiff_profile hT hS hw,
      profileEnergy, radialEnergy, heightDiscriminant, hprofile]

theorem n06_physicalRootFields_eq_finite
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hr : p.1 ≠ 0)
    (hprofile : stateProfile D S C z.1 p.1 = D.w p.1) :
    n06PhysicalRootFields D S C z p = n06RootFiniteFields (n06ActualNuJetCoordinates D S z p) := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
  have hZ := neighborhood_stateHeight_contDiff hT hS hw
  obtain ⟨hQ, hDisc⟩ := n06_rootFinite_denominators_eq hT hS hN01 z hr hprofile
  apply Prod.ext
  · change characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) p =
      -(1 + D.w p.1 ^ 2) * z.2 * radialPartial (heightAngular (stateU S z.1)) p /
        n06RootFiniteQ (n06ActualNuJetCoordinates D S z p)
    rw [n06_characteristicDrift_eq_polarJets (hZ.contDiffAt.of_le (by simp)) hr,
      n06_stateHeight_radialAngular_of_profile hT hS hw hr, hQ]
    simp only [profileEnergy, radialEnergy, hprofile]
    ring
  · change D.w p.1 * Real.sqrt (polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) p) / _ =
      D.w p.1 * Real.sqrt (n06RootFiniteDiscriminant (n06ActualNuJetCoordinates D S z p)) /
        n06RootFiniteQ (n06ActualNuJetCoordinates D S z p)
    rw [hQ, hDisc]

/-- The original N01 clause supplies the whole profile germ. Thus this
identity contains all radial and angular jets, rather than just values. -/
theorem n06_physicalRootFields_germ_eq_finite
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {r : ℝ} (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0) (θ : ℝ) :
    n06PhysicalRootFields D S C z =ᶠ[𝓝 (r, θ)]
      n06RootFiniteFields ∘ n06ActualNuJetCoordinates D S z := by
  have hprofile := hN01.2.2.2.2.2.2.2.2.2.2.1 z hz r hr hroot
  have hrpos : 0 < r := hN01.1.1.choose_spec.1.1.trans hr.1
  have hprofile' := hprofile.comp_tendsto (continuous_fst.tendsto (r, θ))
  have hpositive : ∀ᶠ p : PolarPoint in 𝓝 (r, θ), 0 < p.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hrpos
  filter_upwards [hprofile', hpositive] with p hp hpos
  exact n06_physicalRootFields_eq_finite hT hS hN01 z hpos.ne' hp

theorem n06_physicalRootFields_iteratedFDeriv_eq_finite
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {r : ℝ} (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0) (θ : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (n06PhysicalRootFields D S C z) (r, θ) =
      iteratedFDeriv ℝ n (n06RootFiniteFields ∘ n06ActualNuJetCoordinates D S z) (r, θ) :=
  ((n06_physicalRootFields_germ_eq_finite hT hS hN01 hz hr hroot θ).iteratedFDeriv ℝ n).eq_of_nhds

end ContinuousFlexibility.Statements
