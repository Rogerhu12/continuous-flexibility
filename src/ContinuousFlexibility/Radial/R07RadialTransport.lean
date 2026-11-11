import ContinuousFlexibility.Radial.R07LinearTransport
import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Continuous finite transport of actual radial Cauchy data

The flux state `(u, w u')` satisfies a linear first-order equation whose
coefficients use only `w`, `w'`, and the positive radius.  Joint continuity
of those two profile jets on a fixed compact interval therefore gives
continuous dependence of the endpoint Cauchy data of any smooth solution
family.  This applies to solutions chosen by the radial initial-value
existence theorem as well as to continuations of the natural tail.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

/-- The unnormalized physical flux state used for finite ODE transport. -/
def r07RadialFluxState (w u : ℝ → ℝ) (r : ℝ) : ℝ × ℝ :=
  (u r, w r * deriv u r)

/-- The first-order operator for the physical radial flux state. -/
def r07RadialFluxOperator (w : ℝ → ℝ) (j : ℕ) (r : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (1 / w r) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0) +
    ((j : ℝ) ^ 2 * deriv w r / r) • ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ))

theorem r07RadialFluxOperator_apply (w : ℝ → ℝ) (j : ℕ) (r : ℝ) (v : ℝ × ℝ) :
    r07RadialFluxOperator w j r v =
      (v.2 / w r, ((j : ℝ) ^ 2 * deriv w r / r) * v.1) := by
  ext <;> simp [r07RadialFluxOperator, div_eq_mul_inv, mul_comm]

/-- The physical Jacobi equation is exactly the linear flux-state ODE. -/
theorem hasDerivAt_r07RadialFluxState {w u : ℝ → ℝ} {j : ℕ} {r : ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hwn : w r ≠ 0)
    (hode : radialJacobi ((j : ℝ) ^ 2) w u r = 0) :
    HasDerivAt (r07RadialFluxState w u)
      (r07RadialFluxOperator w j r (r07RadialFluxState w u r)) r := by
  have hu' : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hflux : HasDerivAt (fun t => w t * deriv u t)
      (deriv (fun t => w t * deriv u t) r) r :=
    ((hw.differentiable (by simp) r).mul
      (hu'.differentiable (by simp) r)).hasDerivAt
  have heq : deriv (fun t => w t * deriv u t) r =
      ((j : ℝ) ^ 2 * deriv w r / r) * u r := sub_eq_zero.mp hode
  rw [heq] at hflux
  rw [r07RadialFluxOperator_apply]
  have hcancel : w r * deriv u r / w r = deriv u r := by field_simp [hwn]
  dsimp only [r07RadialFluxState]
  rw [hcancel]
  exact (hu.differentiable (by simp) r).hasDerivAt.prodMk hflux

/-- Joint continuity of the first two profile jets gives joint continuity
of the radial flux operator wherever the profile and radius do not vanish. -/
theorem continuousOn_r07RadialFluxOperator {X : Type*} [TopologicalSpace X]
    {w : X → ℝ → ℝ} {s : Set ℝ} (j : ℕ)
    (h₀ : ContinuousOn (fun z : X × ℝ => w z.1 z.2) {z | z.2 ∈ s})
    (h₁ : ContinuousOn (fun z : X × ℝ => deriv (w z.1) z.2) {z | z.2 ∈ s})
    (hwn : ∀ p r, r ∈ s → w p r ≠ 0) (hrn : ∀ r ∈ s, r ≠ 0) :
    ContinuousOn (fun z : X × ℝ => r07RadialFluxOperator (w z.1) j z.2)
      {z | z.2 ∈ s} := by
  have hinv : ContinuousOn (fun z : X × ℝ => 1 / w z.1 z.2) {z | z.2 ∈ s} :=
    continuousOn_const.div h₀ (fun z hz => hwn z.1 z.2 hz)
  have hq : ContinuousOn (fun z : X × ℝ => (j : ℝ) ^ 2 * deriv (w z.1) z.2 / z.2)
      {z | z.2 ∈ s} :=
    (continuousOn_const.mul h₁).div continuous_snd.continuousOn (fun z hz => hrn z.2 hz)
  exact (hinv.smul continuousOn_const).add (hq.smul continuousOn_const)

/-- Smooth radial solutions with continuous initial Cauchy data have a
continuous transported flux state at the other end of any fixed compact
interval.  Both physical orientations are covered by the same theorem. -/
theorem continuous_radialFluxState_transport {X : Type*} [TopologicalSpace X]
    {w u : X → ℝ → ℝ} {a b : ℝ} (j : ℕ)
    (hw : ∀ p, ContDiff ℝ ∞ (w p)) (hu : ∀ p, ContDiff ℝ ∞ (u p))
    (h₀ : ContinuousOn (fun z : X × ℝ => w z.1 z.2) {z | z.2 ∈ uIcc a b})
    (h₁ : ContinuousOn (fun z : X × ℝ => deriv (w z.1) z.2) {z | z.2 ∈ uIcc a b})
    (hwn : ∀ p r, r ∈ uIcc a b → w p r ≠ 0)
    (hrn : ∀ r ∈ uIcc a b, r ≠ 0)
    (hode : ∀ p r, r ∈ uIcc a b → radialJacobi ((j : ℝ) ^ 2) (w p) (u p) r = 0)
    (hinit₀ : Continuous (fun p => u p a))
    (hinit₁ : Continuous (fun p => deriv (u p) a)) :
    Continuous (fun p => r07RadialFluxState (w p) (u p) b) := by
  have hA := continuousOn_r07RadialFluxOperator j h₀ h₁ hwn hrn
  have hU (p : X) : ContinuousOn (r07RadialFluxState (w p) (u p)) (uIcc a b) :=
    ((hu p).continuous.prodMk
      ((hw p).continuous.mul (contDiff_infty_iff_deriv.mp (hu p)).2.continuous)).continuousOn
  have hd (p : X) (r : ℝ) (hr : r ∈ uIcc a b) :=
    hasDerivAt_r07RadialFluxState (hw p) (hu p) (hwn p r hr) (hode p r hr)
  have hwa : Continuous (fun p => w p a) :=
    h₀.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => left_mem_uIcc)
  have hi : Continuous (fun p => r07RadialFluxState (w p) (u p) a) :=
    hinit₀.prodMk (hwa.mul hinit₁)
  exact continuous_linearODE_transport hA hU hd hi

/-- The ordinary value and derivative at the final radius are continuous
as well, since the positive physical coefficient converts flux to slope. -/
theorem continuous_radialCauchyData_transport {X : Type*} [TopologicalSpace X]
    {w u : X → ℝ → ℝ} {a b : ℝ} (j : ℕ)
    (hw : ∀ p, ContDiff ℝ ∞ (w p)) (hu : ∀ p, ContDiff ℝ ∞ (u p))
    (h₀ : ContinuousOn (fun z : X × ℝ => w z.1 z.2) {z | z.2 ∈ uIcc a b})
    (h₁ : ContinuousOn (fun z : X × ℝ => deriv (w z.1) z.2) {z | z.2 ∈ uIcc a b})
    (hwn : ∀ p r, r ∈ uIcc a b → w p r ≠ 0)
    (hrn : ∀ r ∈ uIcc a b, r ≠ 0)
    (hode : ∀ p r, r ∈ uIcc a b → radialJacobi ((j : ℝ) ^ 2) (w p) (u p) r = 0)
    (hinit₀ : Continuous (fun p => u p a))
    (hinit₁ : Continuous (fun p => deriv (u p) a)) :
    Continuous (fun p => (u p b, deriv (u p) b)) := by
  have hF := continuous_radialFluxState_transport j hw hu h₀ h₁ hwn hrn hode hinit₀ hinit₁
  have hwb : Continuous (fun p => w p b) :=
    h₀.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => right_mem_uIcc)
  have hq : Continuous (fun p : X =>
      (r07RadialFluxState (w p) (u p) b).2 / w p b) :=
    hF.snd.div hwb (fun p => hwn p b right_mem_uIcc)
  have he : (fun p => (r07RadialFluxState (w p) (u p) b).2 / w p b) =
      (fun p => deriv (u p) b) := by
    funext p
    dsimp only [r07RadialFluxState]
    field_simp [hwn p b right_mem_uIcc]
  rw [he] at hq
  exact hF.fst.prodMk hq

end ContinuousFlexibility.Radial
