import ContinuousFlexibility.Analysis.N06RootRegularTransport
import ContinuousFlexibility.Analysis.N06RelativeBoundarySymmetry
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The exact logarithmic height of a genuine root coordinate

The two actual transport equations remove the angular-product quotient
from the height factor. The resulting logarithm involves only the odd
root field and the product of the two actual scalar coefficients. The
identities hold on the physical side and determine every ordinary
boundary jet of the smooth extensions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- An identity on a positive germ determines the ordinary jets at zero
of two functions smooth there. No extension identity on the negative
half-line is asserted. -/
theorem n06_iteratedDeriv_eq_of_positive_germ
    {f g : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0)
    (heq : ∀ᶠ x : ℝ in 𝓝 0, 0 < x → f x = g x) (n : ℕ) :
    iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
  have heq' : f =ᶠ[𝓝[>] (0 : ℝ)] g := by
    filter_upwards [heq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxpos
    exact hx hxpos
  have hfLim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgLim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
    hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : f 0 = g 0 := tendsto_nhds_unique hfLim ((tendsto_congr' heq').mpr hgLim)
  have hclosed : ∀ᶠ x : ℝ in 𝓝 0, 0 ≤ x → f x = g x := by
    filter_upwards [heq] with x hx hxnonneg
    rcases eq_or_lt_of_le hxnonneg with hxzero | hxpos
    · subst x
      exact hzero
    · exact hx hxpos
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hclosed
  apply n06_iteratedDeriv_congr_closed_interval (half_pos hε)
    (show (0 : ℝ) ∈ Icc 0 (ε / 2) from ⟨le_rfl, (half_pos hε).le⟩) hf hg
    (n := n)
  intro x hx
  apply hball ?_ hx.1
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1] using
    hx.2.trans_lt (half_lt_self hε)

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (P : N04bRootCoordinateProperties d c₀ β Φ R σ G)

include P

/-- The genuine characteristic transport cancels the angular-product
denominator. The remaining factor is regular at the root. -/
theorem n06_rootHeightFactor_eq_regular
    (a : PolarPoint → ℝ) {p : PolarPoint} (hp : 0 < p.1)
    (hO : 0 < extendedRootOddCoefficient G p) :
    rootHeightFactor a G p =
      a p * c₀ p / Real.sqrt (extendedRootRadialFactor G p) := by
  have hOraw : 0 < rootOddCoefficient G p := by
    simpa only [extendedRootOddCoefficient_of_nonneg G hp.le] using hO
  have hUr : radialPartial (rootCharacteristicCoordinate G 1) p =
      -(d p + Real.sqrt p.1 * c₀ p) *
        angularPartial (rootCharacteristicCoordinate G 1) p := by
    simpa only [rootPhysicalSpeed, one_mul] using P.transport 1 p.1 p.2 hp
  have hVr : radialPartial (rootCharacteristicCoordinate G (-1)) p =
      -(d p - Real.sqrt p.1 * c₀ p) *
        angularPartial (rootCharacteristicCoordinate G (-1)) p := by
    simpa only [rootPhysicalSpeed, neg_one_mul, neg_mul, sub_eq_add_neg] using
      P.transport (-1) p.1 p.2 hp
  have he := rootHeightFactor_eq_characteristicFactor (p := p) a P.smooth Real.pi_ne_zero
    (fun r _ => P.odd_period r) (fun r _ => P.even_period r) hp hOraw hUr hVr
    (P.angular_positive 1 p.1 p.2 hp).ne' (P.angular_positive (-1) p.1 p.2 hp).ne'
  have hF : 0 < extendedRootRadialFactor G p :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hO) _
  have hs : Real.sqrt ((extendedRootEvenOddChart G p).1) =
      Real.sqrt p.1 * Real.sqrt (extendedRootRadialFactor G p) := by
    change Real.sqrt (p.1 * extendedRootRadialFactor G p) = _
    exact Real.sqrt_mul hp.le _
  rw [extendedRootScale, hs] at he
  exact he.trans (by
    field_simp [(Real.sqrt_pos.mpr hp).ne', (Real.sqrt_pos.mpr hF).ne']
    <;> ring)

/-- Only the odd root field and the coefficient product occur in the
actual logarithmic height. -/
theorem n06_logHeight_eq_regular
    (a : PolarPoint → ℝ) {p : PolarPoint} (hp : 0 < p.1)
    (hO : 0 < extendedRootOddCoefficient G p) (hac : 0 < a p * c₀ p) :
    Real.log (rootSmoothHeight a G p) =
      (1 / 6 : ℝ) * Real.log (((3 : ℝ) / 2) * extendedRootOddCoefficient G p) -
        (1 / 2 : ℝ) * Real.log (a p * c₀ p) := by
  have hbase : 0 < ((3 : ℝ) / 2) * extendedRootOddCoefficient G p :=
    mul_pos (by norm_num) hO
  have hF : 0 < extendedRootRadialFactor G p := Real.rpow_pos_of_pos hbase _
  have he := P.n06_rootHeightFactor_eq_regular (p := p) a hp hO
  have hh : 0 < rootHeightFactor a G p := by
    rw [he]
    exact div_pos hac (Real.sqrt_pos.mpr hF)
  rw [rootSmoothHeight, Real.log_inv, Real.log_sqrt hh.le, he,
    Real.log_div hac.ne' (Real.sqrt_pos.mpr hF).ne', Real.log_sqrt hF.le]
  change -((Real.log (a p * c₀ p) -
    Real.log ((((3 : ℝ) / 2) * extendedRootOddCoefficient G p) ^ (2 / 3 : ℝ)) / 2) / 2) = _
  rw [Real.log_rpow hbase]
  ring

/-- Positivity of the actual divided odd field and of the actual label
already forces the physical speed factor to be positive at the root. -/
theorem n06_speedFactor_positive_zero (θ : ℝ) : 0 < c₀ (0, θ) := by
  have h := P.odd_positive θ
  rw [P.odd_zero θ] at h
  have h' : 0 < ((2 : ℝ) / 3) * c₀ (0, θ) :=
    (mul_pos_iff_of_pos_right (P.label_positive θ)).mp h
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2 / 3)).mp h'

/-- Every true radial boundary jet, in particular orders zero through
three, is obtained from the regular logarithmic formula. Local smoothness
of the actual coefficients is sufficient. -/
theorem n06_logHeight_boundary_jets
    {a : PolarPoint → ℝ} (θ : ℝ)
    (ha : ContDiffAt ℝ ∞ a (0, θ)) (hc : ContDiffAt ℝ ∞ c₀ (0, θ))
    (ha0 : 0 < a (0, θ)) (n : ℕ) :
    radialBoundaryJet (fun p => Real.log (rootSmoothHeight a G p)) 0 n θ =
      radialBoundaryJet (fun p =>
        (1 / 6 : ℝ) * Real.log (((3 : ℝ) / 2) * extendedRootOddCoefficient G p) -
          (1 / 2 : ℝ) * Real.log (a p * c₀ p)) 0 n θ := by
  have hO : 0 < extendedRootOddCoefficient G (0, θ) := by
    simpa only [extendedRootOddCoefficient_of_nonneg G (p := (0, θ))
      (le_refl (0 : ℝ))] using
      P.odd_positive θ
  have hac : 0 < a (0, θ) * c₀ (0, θ) :=
    mul_pos ha0 (P.n06_speedFactor_positive_zero θ)
  have hh := P.height_boundary θ ha ha0
  have hleft : ContDiffAt ℝ ∞ (fun p => Real.log (rootSmoothHeight a G p)) (0, θ) :=
    hh.2.1.log hh.2.2.1.ne'
  have hlogO : ContDiffAt ℝ ∞
      (fun p => Real.log (((3 : ℝ) / 2) * extendedRootOddCoefficient G p)) (0, θ) :=
    (contDiffAt_const.mul P.n06_extendedOdd_smooth.contDiffAt).log
      (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hO).ne'
  have hright : ContDiffAt ℝ ∞ (fun p =>
      (1 / 6 : ℝ) * Real.log (((3 : ℝ) / 2) * extendedRootOddCoefficient G p) -
        (1 / 2 : ℝ) * Real.log (a p * c₀ p)) (0, θ) :=
    (contDiffAt_const.mul hlogO).sub
      (contDiffAt_const.mul ((ha.mul hc).log hac.ne'))
  have hline : ContDiffAt ℝ ∞ (fun x : ℝ => (x, θ)) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hOnear : ∀ᶠ x : ℝ in 𝓝 0, 0 < extendedRootOddCoefficient G (x, θ) :=
    (P.n06_extendedOdd_smooth.contDiffAt.comp 0 hline).continuousAt.tendsto.eventually
      (Ioi_mem_nhds hO)
  have hacnear : ∀ᶠ x : ℝ in 𝓝 0, 0 < a (x, θ) * c₀ (x, θ) :=
    ((ha.mul hc).comp 0 hline).continuousAt.tendsto.eventually (Ioi_mem_nhds hac)
  apply n06_iteratedDeriv_eq_of_positive_germ (hleft.comp 0 hline)
    (hright.comp 0 hline) (n := n)
  filter_upwards [hOnear, hacnear] with x hxO hxac hx
  exact P.n06_logHeight_eq_regular (p := (x, θ)) a hx hxO hxac

end N04bRootCoordinateProperties

end ContinuousFlexibility.Analysis
