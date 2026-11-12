import ContinuousFlexibility.Radial.InnerLiouvilleEnergyDomain

/-!
# One smooth representative for both physical H1 coordinates

The value and normalized derivative are those of the same transported
model field. Constant rescaling includes the actual unit Poisson
normalization without choosing an independent gradient representative.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

theorem exists_innerLiouvilleScaledH1Representative
    (c : ℝ) (f d : RadialL2) (p : ℝ → ℝ)
    (hpp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hfp : (f : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] p)
    (hdp : (d : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] deriv p) :
    ∃ u : ℝ → ℝ,
      (∀ x ∈ Icc a b, (fun y => u (R y)) =ᶠ[𝓝 x]
        (fun y => c * (p y / (Real.sqrt lam * s y)))) ∧
      (∀ r ∈ Icc (R a) (R b), ContDiffAt ℝ ∞ u r) ∧
      ((c • innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f :
          RadialModeL2 D) : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        (Ioo (R a) (R b)).indicator u ∧
      ((c • innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d) :
          RadialModeL2 D) : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        (Ioo (R a) (R b)).indicator (innerGapGradientField u) := by
  obtain ⟨v, hnear, hreg⟩ :=
    exists_innerLiouvilleSmoothRepresentative hab hlam hR hs hp hpp
  have hvalue := innerLiouvilleFieldLift_eq_indicator D hab hlam hR hs hp hcore hw U hU hv
    f p v hfp (fun r hr => (hreg r hr).continuousAt.continuousWithinAt)
      (fun x hx => (hnear x hx).eq_of_nhds)
  have hgradient := innerLiouvilleGradientLift_eq_indicator D hab hlam hR hs hp hcore hw
    f d p v hpp hfp hdp hreg hnear
  let u : ℝ → ℝ := fun r => c * v r
  have hureg : ∀ r ∈ Icc (R a) (R b), ContDiffAt ℝ ∞ u r :=
    fun r hr => contDiffAt_const.mul (hreg r hr)
  refine ⟨u, ?_, hureg, ?_, ?_⟩
  · intro x hx
    filter_upwards [hnear x hx] with y hy
    dsimp only [u]
    rw [hy]
  · filter_upwards [Lp.coeFn_smul c
      (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f),
      hvalue] with r hc hr
    rw [hc, Pi.smul_apply, smul_eq_mul, hr]
    by_cases hri : r ∈ Ioo (R a) (R b)
    · simp only [indicator_of_mem hri, u]
    · simp only [indicator_of_notMem hri, mul_zero]
  · filter_upwards [Lp.coeFn_smul c
      (innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d)),
      hgradient] with r hc hr
    rw [hc, Pi.smul_apply, smul_eq_mul, hr]
    by_cases hri : r ∈ Ioo (R a) (R b)
    · have hd : deriv u r = c * deriv v r :=
        (((hreg r (Ioo_subset_Icc_self hri)).differentiableAt (by simp)).hasDerivAt.const_mul c).deriv
      simp only [indicator_of_mem hri, innerGapGradientField, hd]
      ring
    · simp only [indicator_of_notMem hri, mul_zero]

end ContinuousFlexibility.Radial
