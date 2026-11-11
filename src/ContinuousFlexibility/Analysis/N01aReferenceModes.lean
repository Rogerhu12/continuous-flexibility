import ContinuousFlexibility.Analysis.N01aReferenceNormalization
import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Smooth radial modes of the actual reference core

Angular integration over the fixed compact circle commutes with every radial
derivative.  A positive mode of a smooth admissible field vanishes outside
the radial core, including the end circles.  It is therefore a legitimate
test in the natural radial kernel identity.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology Interval

private theorem n01a_hasDerivAt_fixed_intervalIntegral
    {f df : ℝ × ℝ → ℝ} (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x θ : ℝ, HasDerivAt (fun y => f (y, θ)) (df (x, θ)) x)
    (a b x : ℝ) :
    HasDerivAt (fun y => ∫ θ in a..b, f (y, θ))
      (∫ θ in a..b, df (x, θ)) x := by
  have hcompact : IsCompact (Icc (x - 1) (x + 1) ×ˢ uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hdf.continuousOn
  have hs : Ioo (x - 1) (x + 1) ∈ 𝓝 x :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hsection (y : ℝ) : Continuous (fun θ => f (y, θ)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hdsection (y : ℝ) : Continuous (fun θ => df (y, θ)) :=
    hdf.comp (continuous_const.prodMk continuous_id)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y θ : ℝ => f (y, θ)) (F' := fun y θ : ℝ => df (y, θ))
    (μ := volume) (a := a) (b := b) (s := Ioo (x - 1) (x + 1))
    (bound := fun _ : ℝ => B) hs
    (Eventually.of_forall fun y => (hsection y).aestronglyMeasurable)
    ((hsection x).intervalIntegrable a b)
    ((hdsection x).aestronglyMeasurable)
    (Eventually.of_forall fun θ hθ y hy =>
      hB (y, θ) ⟨⟨hy.1.le, hy.2.le⟩, uIoc_subset_uIcc hθ⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ y _ => hd y θ)
  exact h.2

/-- Every radial jet can be differentiated through its actual angular mode. -/
set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_referenceMode_mixedDerivative {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (n j : ℕ) (r : ℝ) :
    HasDerivAt (referenceMode (mixedDerivative n 0 u) j)
      (referenceMode (mixedDerivative (n + 1) 0 u) j r) r := by
  have hc : Continuous (Radial.cosineMode j) := by
    unfold Radial.cosineMode
    fun_prop
  have hf : Continuous (fun p : PolarPoint =>
      mixedDerivative n 0 u p * Radial.cosineMode j p.2) :=
    (contDiff_mixedDerivative hu n 0).continuous.mul (hc.comp continuous_snd)
  have hdf : Continuous (fun p : PolarPoint =>
      mixedDerivative (n + 1) 0 u p * Radial.cosineMode j p.2) :=
    (contDiff_mixedDerivative hu (n + 1) 0).continuous.mul (hc.comp continuous_snd)
  have hd (x θ : ℝ) : HasDerivAt
      (fun y => mixedDerivative n 0 u (y, θ) * Radial.cosineMode j θ)
      (mixedDerivative (n + 1) 0 u (x, θ) * Radial.cosineMode j θ) x := by
    have hs : ContDiff ℝ ∞ (fun y : ℝ => u (y, θ)) :=
      hu.comp (contDiff_id.prodMk contDiff_const)
    have hn : Differentiable ℝ (iteratedDeriv n (fun y : ℝ => u (y, θ))) :=
      hs.differentiable_iteratedDeriv n
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
    simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_succ] using
      (hn x).hasDerivAt.mul_const (Radial.cosineMode j θ)
  have hi := n01a_hasDerivAt_fixed_intervalIntegral hf hdf hd 0 (2 * Real.pi) r
  change HasDerivAt
    (fun y => (2 * Real.pi)⁻¹ *
      ∫ θ in 0..2 * Real.pi, mixedDerivative n 0 u (y, θ) * Radial.cosineMode j θ)
    ((2 * Real.pi)⁻¹ *
      ∫ θ in 0..2 * Real.pi, mixedDerivative (n + 1) 0 u (r, θ) * Radial.cosineMode j θ) r
  exact hi.const_mul (2 * Real.pi)⁻¹

theorem iteratedDeriv_referenceMode {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (n j : ℕ) :
    iteratedDeriv n (referenceMode u j) = referenceMode (mixedDerivative n 0 u) j := by
  induction n with
  | zero =>
      have hm : mixedDerivative 0 0 u = u := by
        funext p
        simp only [mixedDerivative, iteratedDeriv_zero]
      simp only [iteratedDeriv_zero, hm]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      exact funext fun r => (hasDerivAt_referenceMode_mixedDerivative hu n j r).deriv

theorem contDiff_referenceMode {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (j : ℕ) : ContDiff ℝ ∞ (referenceMode u j) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro n _
  rw [iteratedDeriv_referenceMode hu n j]
  exact fun r => (hasDerivAt_referenceMode_mixedDerivative hu n j r).differentiableAt

/-- The constant left state has no positive cosine coefficient. -/
theorem referenceMode_eq_zero_of_angle_constant {u : PolarPoint → ℝ}
    {r c : ℝ} (h : ∀ θ, u (r, θ) = c) (j : ℕ) (hj : 0 < j) :
    referenceMode u j r = 0 := by
  unfold referenceMode
  simp_rw [h]
  rw [radialAngularMean_const_mul, radialAngularMean_cosineMode j hj, mul_zero]

theorem smoothAdmissible_referenceMode_support {D : ReferenceData} {U : RadialUnknown}
    (hU : SmoothAdmissibleField D U) (j : ℕ) (hj : 0 < j) :
    Function.support (referenceMode U.1 j) ⊆ radialCore D := by
  obtain ⟨_, _, aL, hleft, hright⟩ := hU
  intro r hr
  by_contra hnot
  have hsplit : r ≤ D.a ∨ D.b ≤ r := by
    simpa only [radialCore, mem_Ioo, not_and_or, not_lt] using hnot
  rcases hsplit with h | h
  · exact hr (referenceMode_eq_zero_of_angle_constant (hleft r h) j hj)
  · exact hr (referenceMode_eq_zero_of_angle_constant (hright r h) j hj)

theorem smoothAdmissible_referenceMode_hasCompactSupport
    {D : ReferenceData} {U : RadialUnknown}
    (hU : SmoothAdmissibleField D U) (j : ℕ) (hj : 0 < j) :
    HasCompactSupport (referenceMode U.1 j) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((smoothAdmissible_referenceMode_support hU j hj).trans Ioo_subset_Icc_self)

theorem naturalRadialNull_phi {D : ReferenceData} (hkernel : RadialNaturalKernels D) :
    NaturalRadialNull D 2 D.phi := by
  apply (hkernel.2.1 D.phi).mpr
  refine ⟨1, Eventually.of_forall fun r => ?_⟩
  simp only [one_mul]

/-- The smooth core's second mode is a valid natural test, even when its
nonzero values approach the two end circles. -/
theorem natural_phi_pairing_referenceMode {D : ReferenceData} {U : RadialUnknown}
    (hkernel : RadialNaturalKernels D) (hU : SmoothAdmissibleField D U) :
    (∫ r in D.a..D.b,
      D.phi r * Radial.radialJacobi 4 D.w (referenceMode U.1 2) r) = 0 := by
  have h := (naturalRadialNull_phi hkernel).2 (referenceMode U.1 2)
    (contDiff_referenceMode hU.1 2)
    (smoothAdmissible_referenceMode_hasCompactSupport hU 2 (by decide))
    (smoothAdmissible_referenceMode_support hU 2 (by decide))
  simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

end ContinuousFlexibility.Statements
