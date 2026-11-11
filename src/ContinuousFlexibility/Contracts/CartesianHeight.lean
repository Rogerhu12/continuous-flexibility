import ContinuousFlexibility.Contracts.Annular
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The actual filled Cartesian height

The polar height is evaluated at norm and principal argument. Half-turn
periodicity proves equality across the argument branch cut, and the
constant inner extension makes the center genuinely smooth. Thus this
constructs a global Cartesian function from the analytic core, rather than
assuming that a smooth Cartesian extension exists.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def polarHeightOnComplex (z : PolarPoint → ℝ) (v : ℂ) : ℝ := z (‖v‖, v.arg)

theorem contDiffAt_complexArg_real {v : ℂ} (hv : v ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg v := by
  have hl : ContDiffAt ℝ ∞ Complex.log v := (Complex.contDiffAt_log hv).restrict_scalars ℝ
  have hi := (Complex.imCLM.contDiff : ContDiff ℝ ∞ Complex.imCLM).contDiffAt.comp v hl
  change ContDiffAt ℝ ∞ (fun u : ℂ => (Complex.log u).im) v at hi
  simpa only [Complex.log_im] using hi

theorem polarHeightOnComplex_neg
    {z : PolarPoint → ℝ} (hper : Function.Periodic z (0, Real.pi)) (v : ℂ) :
    polarHeightOnComplex z (-v) = polarHeightOnComplex z v := by
  by_cases hv : v = 0
  · simp [hv]
  let f : ℝ → ℝ := fun θ => z (‖v‖, θ)
  have hp : Function.Periodic f Real.pi := by
    intro θ
    simpa only [f, Prod.mk_add_mk, add_zero] using hper (‖v‖, θ)
  unfold polarHeightOnComplex
  rw [norm_neg]
  change f (-v).arg = f v.arg
  by_cases hi : 0 < v.im
  · rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi]
    exact hp.sub_eq v.arg
  by_cases hn : v.im < 0
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hn]
    exact hp v.arg
  have him : v.im = 0 := le_antisymm (le_of_not_gt hi) (le_of_not_gt hn)
  by_cases hr : v.re < 0
  · rw [Complex.arg_neg_eq_arg_sub_pi_iff.mpr (Or.inr ⟨him, hr⟩)]
    exact hp.sub_eq v.arg
  have hrep : 0 < v.re := by
    have hne : v.re ≠ 0 := by
      intro hzero
      exact hv (Complex.ext hzero him)
    exact lt_of_le_of_ne (le_of_not_gt hr) hne.symm
  rw [Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inr ⟨him, hrep⟩)]
  exact hp v.arg

theorem contDiffAt_polarHeightOnComplex_slit
    {z : PolarPoint → ℝ} (hz : ContDiff ℝ ∞ z) {v : ℂ}
    (hv : v ∈ Complex.slitPlane) : ContDiffAt ℝ ∞ (polarHeightOnComplex z) v := by
  exact hz.contDiffAt.comp v
    ((contDiffAt_norm ℂ (Complex.slitPlane_ne_zero hv)).prodMk (contDiffAt_complexArg_real hv))

/-- The half-turn condition pays for the branch cut: one of `v,-v` is in
the slit plane, and the two height formulas agree as actual functions. -/
theorem contDiffAt_polarHeightOnComplex_of_ne_zero
    {z : PolarPoint → ℝ} (hz : ContDiff ℝ ∞ z)
    (hper : Function.Periodic z (0, Real.pi)) {v : ℂ} (hv : v ≠ 0) :
    ContDiffAt ℝ ∞ (polarHeightOnComplex z) v := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hv with hs | hs
  · exact contDiffAt_polarHeightOnComplex_slit hz hs
  · have h := (contDiffAt_polarHeightOnComplex_slit hz hs).comp v contDiffAt_id.neg
    change ContDiffAt ℝ ∞ (fun u : ℂ => polarHeightOnComplex z (-u)) v at h
    have heq : (fun u : ℂ => polarHeightOnComplex z (-u)) = polarHeightOnComplex z :=
      funext (polarHeightOnComplex_neg hper)
    rw [heq] at h
    exact h

def cartesianRadius (x : PolarPoint) : ℝ := ‖Complex.equivRealProdCLM.symm x‖

def FlatAnnularCore.cartesianHeight (A : FlatAnnularCore) (x : PolarPoint) : ℝ :=
  polarHeightOnComplex A.z (Complex.equivRealProdCLM.symm x)

theorem FlatAnnularCore.complexHeight_left (A : FlatAnnularCore) {v : ℂ}
    (hv : ‖v‖ ≤ A.a) : polarHeightOnComplex A.z v = A.cLeft :=
  A.z_left ‖v‖ hv v.arg

theorem FlatAnnularCore.complexHeight_right (A : FlatAnnularCore) {v : ℂ}
    (hv : A.b ≤ ‖v‖) : polarHeightOnComplex A.z v = A.cRight :=
  A.z_right ‖v‖ hv v.arg

theorem FlatAnnularCore.contDiff_complexHeight (A : FlatAnnularCore) :
    ContDiff ℝ ∞ (polarHeightOnComplex A.z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    have hn : {u : ℂ | ‖u‖ < A.a} ∈ 𝓝 0 :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using A.a_pos)
    have hc : polarHeightOnComplex A.z =ᶠ[𝓝 0] fun _ => A.cLeft := by
      filter_upwards [hn] with u hu
      exact A.complexHeight_left hu.le
    exact contDiffAt_const.congr_of_eventuallyEq hc
  · exact contDiffAt_polarHeightOnComplex_of_ne_zero A.smooth_z A.half_turn hv

theorem FlatAnnularCore.contDiff_cartesianHeight (A : FlatAnnularCore) :
    ContDiff ℝ ∞ A.cartesianHeight :=
  A.contDiff_complexHeight.comp Complex.equivRealProdCLM.symm.contDiff

theorem FlatAnnularCore.cartesianHeight_left (A : FlatAnnularCore) {x : PolarPoint}
    (hx : cartesianRadius x ≤ A.a) : A.cartesianHeight x = A.cLeft :=
  A.complexHeight_left hx

theorem FlatAnnularCore.cartesianHeight_right (A : FlatAnnularCore) {x : PolarPoint}
    (hx : A.b ≤ cartesianRadius x) : A.cartesianHeight x = A.cRight :=
  A.complexHeight_right hx

theorem FlatAnnularCore.cartesianHeight_even (A : FlatAnnularCore) (x : PolarPoint) :
    A.cartesianHeight (-x) = A.cartesianHeight x := by
  simp only [FlatAnnularCore.cartesianHeight, map_neg, polarHeightOnComplex_neg A.half_turn]

def polarPosition (r θ : ℝ) : PolarPoint := (r * Real.cos θ, r * Real.sin θ)

def polarToComplex (r θ : ℝ) : ℂ :=
  (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)

theorem complex_polarPosition (r θ : ℝ) :
    Complex.equivRealProdCLM.symm (polarPosition r θ) = polarToComplex r θ := by
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply, polarPosition, polarToComplex]

theorem norm_polarToComplex {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖polarToComplex r θ‖ = r := by
  simp [polarToComplex, abs_of_pos hr]

theorem cartesianRadius_polarPosition {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    cartesianRadius (polarPosition r θ) = r := by
  rw [cartesianRadius, complex_polarPosition, norm_polarToComplex hr]

/-- Descent recovers the original height for every real angle, including
angles outside the principal branch interval. -/
theorem polarHeightOnComplex_polarToComplex
    {z : PolarPoint → ℝ} (hper : Function.Periodic z (0, 2 * Real.pi))
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    polarHeightOnComplex z (polarToComplex r θ) = z (r, θ) := by
  have hp : Function.Periodic (fun t : ℝ => z (r, t)) (2 * Real.pi) := by
    intro t
    simpa only [Prod.mk_add_mk, add_zero] using hper (r, t)
  unfold polarHeightOnComplex
  rw [norm_polarToComplex hr]
  unfold polarToComplex
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]
  rw [Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hr,
    ← self_sub_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) θ]
  exact hp.sub_zsmul_eq (toIocDiv Real.two_pi_pos (-Real.pi) θ)

theorem FlatAnnularCore.cartesianHeight_polarPosition (A : FlatAnnularCore)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    A.cartesianHeight (polarPosition r θ) = A.z (r, θ) := by
  rw [FlatAnnularCore.cartesianHeight, complex_polarPosition]
  exact polarHeightOnComplex_polarToComplex A.periodic_two_pi hr θ

/-- The nonradial witness survives in the actual Cartesian function on
two points of exactly the same Euclidean radius. -/
theorem FlatAnnularCore.cartesianHeight_nonradial (A : FlatAnnularCore) :
    ∃ r ∈ Ioo A.a A.b, ∃ x y : PolarPoint,
      cartesianRadius x = r ∧ cartesianRadius y = r ∧
        A.cartesianHeight x ≠ A.cartesianHeight y := by
  obtain ⟨r, hr, θ, φ, hne⟩ := A.nonradial
  have hr0 : 0 < r := A.a_pos.trans hr.1
  refine ⟨r, hr, polarPosition r θ, polarPosition r φ,
    cartesianRadius_polarPosition hr0 θ, cartesianRadius_polarPosition hr0 φ, ?_⟩
  simpa only [A.cartesianHeight_polarPosition hr0] using hne

end ContinuousFlexibility
