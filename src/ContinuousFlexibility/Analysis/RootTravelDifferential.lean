import ContinuousFlexibility.Analysis.RootPhysicalTransport
import ContinuousFlexibility.Analysis.RootChartExtensionGeometry
import ContinuousFlexibility.Analysis.CharacteristicPrincipalDensity
import ContinuousFlexibility.Analysis.ScaledRadialPrincipalDensity
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The true differential from travel time to the root coordinate

The two actual characteristic first integrals give travel time
τ = x^(3/2) χ and angle φ. Where x and χ are positive, the genuine
extended root chart is locally the composition
(τ,φ) ↦ (((3/2)τ)^(2/3),φ).
The scalar chain rule gives radial differential scale 1/sqrt(ξ).
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def rootTravelPower (τ : ℝ) : ℝ := (((3 : ℝ) / 2) * τ) ^ (2 / 3 : ℝ)

def extendedRootScale (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Real.sqrt ((extendedRootEvenOddChart G p).1))⁻¹

theorem characteristicTravelChart_rootCharacteristicCoordinate
    (G : ℝ × ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    characteristicTravelChart (rootCharacteristicCoordinate G 1)
        (rootCharacteristicCoordinate G (-1)) p =
      (p.1 ^ (3 / 2 : ℝ) * rootOddCoefficient G p, rootEven G p) := by
  have hpow : p.1 ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  apply Prod.ext
  · simp only [characteristicTravelChart, rootCharacteristicCoordinate,
      rootOddCoefficient, rootOdd_of_ne_zero G (p := p) hp.ne', one_mul, neg_one_mul]
    field_simp [hpow]
    <;> ring
  · simp only [characteristicTravelChart, rootCharacteristicCoordinate, rootEven,
      one_mul, neg_one_mul]
    ring

/-- The two first integrals are the smooth even coordinate minus or plus
the actual root power times the smooth extended odd coefficient. -/
theorem rootCharacteristicCoordinate_eq_extended_even_odd
    (G : ℝ × ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    rootCharacteristicCoordinate G 1 p =
        extendedRootEven G p - p.1 ^ (3 / 2 : ℝ) * extendedRootOddCoefficient G p ∧
      rootCharacteristicCoordinate G (-1) p =
        extendedRootEven G p + p.1 ^ (3 / 2 : ℝ) * extendedRootOddCoefficient G p := by
  have ht := congrArg Prod.fst (characteristicTravelChart_rootCharacteristicCoordinate G hp)
  have ha := congrArg Prod.snd (characteristicTravelChart_rootCharacteristicCoordinate G hp)
  dsimp only [characteristicTravelChart] at ht ha
  simp only [extendedRootEven_of_nonneg G hp.le,
    extendedRootOddCoefficient_of_nonneg G hp.le]
  constructor <;> linarith

theorem extendedRootEvenOddChart_eq_rootTravelPower
    (G : ℝ × ℝ × ℝ → ℝ) {p : ℝ × ℝ}
    (hp : 0 < p.1) (hχ : 0 ≤ rootOddCoefficient G p) :
    extendedRootEvenOddChart G p =
      (rootTravelPower
        ((characteristicTravelChart (rootCharacteristicCoordinate G 1)
          (rootCharacteristicCoordinate G (-1)) p).1),
        (characteristicTravelChart (rootCharacteristicCoordinate G 1)
          (rootCharacteristicCoordinate G (-1)) p).2) := by
  have ht := characteristicTravelChart_rootCharacteristicCoordinate G hp
  simp only [extendedRootEvenOddChart_of_nonneg G hp.le, ht,
    rootEvenOddChart, rootTravelPower]
  apply Prod.ext
  · dsimp only [rootRadialCoordinate, rootRadialFactor]
    rw [show ((3 : ℝ) / 2) * (p.1 ^ (3 / 2 : ℝ) * rootOddCoefficient G p) =
        p.1 ^ (3 / 2 : ℝ) * (((3 : ℝ) / 2) * rootOddCoefficient G p) by ring,
      Real.mul_rpow (Real.rpow_nonneg hp.le _)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hχ),
      ← Real.rpow_mul hp.le,
      show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
  · rfl

theorem hasDerivAt_rootTravelPower {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt rootTravelPower (Real.sqrt (rootTravelPower τ))⁻¹ τ := by
  have hb : 0 < ((3 : ℝ) / 2) * τ := mul_pos (by norm_num) hτ
  have hd := ((hasDerivAt_id τ).const_mul ((3 : ℝ) / 2)).rpow_const
    (p := (2 / 3 : ℝ)) (Or.inl hb.ne')
  have he : (Real.sqrt (rootTravelPower τ))⁻¹ =
      (((3 : ℝ) / 2) * τ) ^ (-(1 / 3 : ℝ)) := by
    rw [rootTravelPower, Real.sqrt_eq_rpow, ← Real.rpow_mul hb.le,
      show (2 / 3 : ℝ) * (1 / 2 : ℝ) = 1 / 3 by norm_num,
      ← Real.rpow_neg hb.le (1 / 3 : ℝ)]
  apply hd.congr_deriv
  rw [he]
  norm_num

theorem extendedRootScale_pos_and_normalization
    (G : ℝ × ℝ × ℝ → ℝ) {p : ℝ × ℝ}
    (hp : 0 < p.1) (hχ : 0 < rootOddCoefficient G p) :
    0 < extendedRootScale G p ∧
      extendedRootScale G p ^ 2 * (extendedRootEvenOddChart G p).1 = 1 := by
  have hξ : 0 < (extendedRootEvenOddChart G p).1 := by
    rw [extendedRootEvenOddChart_of_nonneg G hp.le]
    exact mul_pos hp (rootRadialFactor_pos hχ)
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr hξ), ?_⟩
  rw [extendedRootScale, inv_pow, Real.sq_sqrt hξ.le]
  exact inv_mul_cancel₀ hξ.ne'

/-- The two basis instances of this theorem are exactly the inputs to
the existing principal-density theorem for a scaled radial differential. -/
theorem fderiv_extendedRootEvenOddChart_scaled_travel
    {G : ℝ × ℝ × ℝ → ℝ} {T : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    {p : ℝ × ℝ} (hp : 0 < p.1) (hχ : 0 < rootOddCoefficient G p)
    (v : ℝ × ℝ) :
    fderiv ℝ (extendedRootEvenOddChart G) p v =
      (extendedRootScale G p *
        (fderiv ℝ (characteristicTravelChart (rootCharacteristicCoordinate G 1)
          (rootCharacteristicCoordinate G (-1))) p v).1,
        (fderiv ℝ (characteristicTravelChart (rootCharacteristicCoordinate G 1)
          (rootCharacteristicCoordinate G (-1))) p v).2) := by
  let F := characteristicTravelChart (rootCharacteristicCoordinate G 1)
    (rootCharacteristicCoordinate G (-1))
  have hU : DifferentiableAt ℝ (rootCharacteristicCoordinate G 1) p :=
    (contDiffAt_rootCharacteristicCoordinate (σ := 1) (θ := p.2) hG hp).differentiableAt (by simp)
  have hV : DifferentiableAt ℝ (rootCharacteristicCoordinate G (-1)) p :=
    (contDiffAt_rootCharacteristicCoordinate (σ := -1) (θ := p.2) hG hp).differentiableAt (by simp)
  have hF : DifferentiableAt ℝ F p :=
    (((hV.hasFDerivAt.fun_sub hU.hasFDerivAt).const_mul (1 / 2 : ℝ)).prodMk
      ((hU.hasFDerivAt.fun_add hV.hasFDerivAt).const_mul (1 / 2 : ℝ))).differentiableAt
  have hτ : 0 < (F p).1 := by
    rw [characteristicTravelChart_rootCharacteristicCoordinate G hp]
    exact mul_pos (Real.rpow_pos_of_pos hp _) hχ
  have hcoord : rootTravelPower ((F p).1) = (extendedRootEvenOddChart G p).1 :=
    (congrArg Prod.fst (extendedRootEvenOddChart_eq_rootTravelPower G hp hχ.le)).symm
  have ha : HasDerivAt rootTravelPower (extendedRootScale G p) ((F p).1) := by
    simpa only [hcoord, extendedRootScale] using hasDerivAt_rootTravelPower hτ
  have hd := (ha.comp_hasFDerivAt p hF.hasFDerivAt.fst).prodMk hF.hasFDerivAt.snd
  have hefun : (fun q : ℝ × ℝ =>
      ((rootTravelPower ∘ (fun y => (F y).1)) q, (F q).2)) =
      (fun q : ℝ × ℝ => (rootTravelPower ((F q).1), (F q).2)) := by
    funext q
    simp only [Function.comp_apply]
  rw [hefun] at hd
  have hxp : ∀ᶠ q in 𝓝 p, 0 < q.1 :=
    continuous_fst.continuousAt.tendsto.eventually (Ioi_mem_nhds hp)
  have hχext : 0 < extendedRootOddCoefficient G p := by
    rwa [extendedRootOddCoefficient_of_nonneg G hp.le]
  have hχp : ∀ᶠ q in 𝓝 p, 0 < extendedRootOddCoefficient G q :=
    (contDiff_extendedRootOddCoefficient hG hT hχperiod).continuous.continuousAt.tendsto.eventually
      (Ioi_mem_nhds hχext)
  have he : extendedRootEvenOddChart G =ᶠ[𝓝 p]
      (fun q => (rootTravelPower ((F q).1), (F q).2)) := by
    filter_upwards [hxp, hχp] with q hq hqχ
    have hraw : 0 < rootOddCoefficient G q := by
      rwa [extendedRootOddCoefficient_of_nonneg G hq.le] at hqχ
    exact extendedRootEvenOddChart_eq_rootTravelPower G hq hraw.le
  have hB := hd.congr_of_eventuallyEq he
  rw [hB.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]

end ContinuousFlexibility.Analysis
