import ContinuousFlexibility.Analysis.FiniteLinearFlow
import ContinuousFlexibility.Radial.OuterNormalizedState
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual value and flux states on a regular outer interval

The transfer is the continuous linear equivalence furnished by the actual
first-order equation. Its component equations recover the radial Jacobi
equation and the physical scaled flux, without postulating homogeneous
solutions or an invertible transfer matrix.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped Topology

set_option backward.isDefEq.respectTransparency false

/-- The coefficient of the value/flux system. -/
def outerStateMatrix (alpha beta : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (alpha • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (beta • ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem outerStateMatrix_apply (alpha beta : ℝ) (x : ℝ × ℝ) :
    outerStateMatrix alpha beta x = (alpha * x.2, beta * x.1) := rfl

theorem outerStateMatrix_continuousOn {alpha beta : ℝ → ℝ} {s : Set ℝ}
    (halpha : ContinuousOn alpha s) (hbeta : ContinuousOn beta s) :
    ContinuousOn (fun t => outerStateMatrix (alpha t) (beta t)) s := by
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn
    ((halpha.smul continuousOn_const).prodMk (hbeta.smul continuousOn_const))

/-- The actual two scalar differential equations. -/
def OuterFirstOrderSystem (alpha beta u z : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt u (alpha t * z t) t ∧ HasDerivAt z (beta t * u t) t

theorem outerFirstOrderSystem_iff {alpha beta u z : ℝ → ℝ} {s : Set ℝ} :
    OuterFirstOrderSystem alpha beta u z s ↔
      ∀ t ∈ s, HasDerivAt (fun r => (u r, z r))
        (outerStateMatrix (alpha t) (beta t) (u t, z t)) t := by
  constructor
  · intro h t ht
    exact (h t ht).1.prodMk (h t ht).2
  · intro h t ht
    constructor
    · exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (h t ht)
    · exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (h t ht)

/-- Actual scalar solutions through any full initial state. -/
theorem exists_outerFirstOrder_state {a b : ℝ} (hab : a ≤ b)
    {alpha beta : ℝ → ℝ} (halpha : ContinuousOn alpha (Icc a b))
    (hbeta : ContinuousOn beta (Icc a b)) (c : ℝ) (v : ℝ × ℝ) :
    ∃ u z : ℝ → ℝ, (u c, z c) = v ∧ OuterFirstOrderSystem alpha beta u z (Icc a b) := by
  obtain ⟨f, hfc, hf⟩ := Analysis.exists_linear_ode_on_Icc hab
    (fun t => outerStateMatrix (alpha t) (beta t))
    (outerStateMatrix_continuousOn halpha hbeta) c v
  refine ⟨fun t => (f t).1, fun t => (f t).2, hfc, ?_⟩
  intro t ht
  constructor
  · exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hf t ht)
  · exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hf t ht)

/-- The real state transfer, with inverse given by solving from the other end. -/
def outerStateTransfer {a b c d : ℝ} (hab : a ≤ b)
    {alpha beta : ℝ → ℝ} (halpha : ContinuousOn alpha (Icc a b))
    (hbeta : ContinuousOn beta (Icc a b)) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  Analysis.finiteLinearTransferL hab (fun t => outerStateMatrix (alpha t) (beta t))
    (outerStateMatrix_continuousOn halpha hbeta) hc hd

theorem outerStateTransfer_actual {a b c d : ℝ} (hab : a ≤ b)
    {alpha beta u z : ℝ → ℝ} (halpha : ContinuousOn alpha (Icc a b))
    (hbeta : ContinuousOn beta (Icc a b)) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b)
    (hstate : OuterFirstOrderSystem alpha beta u z (Icc a b)) :
    outerStateTransfer hab halpha hbeta hc hd (u c, z c) = (u d, z d) :=
  Analysis.finiteLinearTransferL_actual hab _ (outerStateMatrix_continuousOn halpha hbeta)
    hc hd (outerFirstOrderSystem_iff.mp hstate)

/-- A nonzero state remains nonzero, even if its value coordinate vanishes. -/
theorem outerFirstOrder_state_ne_zero {a b c d : ℝ} (hab : a ≤ b)
    {alpha beta u z : ℝ → ℝ} (halpha : ContinuousOn alpha (Icc a b))
    (hbeta : ContinuousOn beta (Icc a b)) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b)
    (hstate : OuterFirstOrderSystem alpha beta u z (Icc a b))
    (hnd : (u d, z d) ≠ 0) : (u c, z c) ≠ 0 := by
  intro hz
  have h := outerStateTransfer_actual hab halpha hbeta hc hd hstate
  rw [hz, map_zero] at h
  exact hnd h.symm

/-- The first-order solution has exactly the physical scaled flux and solves
the original radial Jacobi equation throughout the open regular interval. -/
theorem exists_outerFluxState_solution {a b J lam : ℝ} (hab : a ≤ b)
    (hlam : lam ≠ 0) {w : ℝ → ℝ}
    (hwc : ContinuousOn w (Icc a b)) (hwdc : ContinuousOn (deriv w) (Icc a b))
    (hwd : ∀ r ∈ Icc a b, DifferentiableAt ℝ w r)
    (hwpos : ∀ r ∈ Icc a b, 0 < w r) (hrzero : ∀ r ∈ Icc a b, r ≠ 0)
    (c : ℝ) (v : ℝ × ℝ) :
    ∃ u z : ℝ → ℝ, (u c, z c) = v ∧
      OuterFirstOrderSystem (fun r => lam / w r)
        (fun r => J * deriv w r / (lam * r)) u z (Icc a b) ∧
      (∀ r ∈ Icc a b, outerFluxState lam w u r = (u r, z r)) ∧
      ∀ r ∈ Ioo a b, DifferentiableAt ℝ u r ∧
        DifferentiableAt ℝ (deriv u) r ∧ radialJacobi J w u r = 0 := by
  have halpha : ContinuousOn (fun r => lam / w r) (Icc a b) :=
    continuousOn_const.div hwc (fun r hr => (hwpos r hr).ne')
  have hbeta : ContinuousOn (fun r => J * deriv w r / (lam * r)) (Icc a b) :=
    (continuousOn_const.mul hwdc).div (continuousOn_const.mul continuousOn_id)
      (fun r hr => mul_ne_zero hlam (hrzero r hr))
  obtain ⟨u, z, hinit, hstate⟩ := exists_outerFirstOrder_state hab halpha hbeta c v
  have hflux (r : ℝ) (hr : r ∈ Icc a b) : w r * deriv u r = lam * z r := by
    rw [(hstate r hr).1.deriv]
    field_simp [(hwpos r hr).ne'] <;> ring
  refine ⟨u, z, hinit, hstate, fun r hr => ?_, fun r hr => ?_⟩
  · apply Prod.ext rfl
    change w r * deriv u r / lam = z r
    rw [hflux r hr]
    field_simp [hlam]
  · have hr' := Ioo_subset_Icc_self hr
    have hdu : deriv u =ᶠ[𝓝 r] fun t => lam / w t * z t := by
      filter_upwards [Icc_mem_nhds hr.1 hr.2] with t ht
      exact (hstate t ht).1.deriv
    have hddu : DifferentiableAt ℝ (deriv u) r :=
      ((differentiableAt_const.div (hwd r hr') (hwpos r hr').ne').mul
        (hstate r hr').2.differentiableAt).congr_of_eventuallyEq hdu
    have hfluxeq : (fun t => w t * deriv u t) =ᶠ[𝓝 r] fun t => lam * z t := by
      filter_upwards [Icc_mem_nhds hr.1 hr.2] with t ht
      exact hflux t ht
    have hfluxd : HasDerivAt (fun t => w t * deriv u t)
        (J * deriv w r / r * u r) r := by
      apply (((hstate r hr').2.const_mul lam).congr_of_eventuallyEq hfluxeq).congr_deriv
      field_simp [hlam, hrzero r hr'] <;> ring
    refine ⟨(hstate r hr').1.differentiableAt, hddu, ?_⟩
    rw [radialJacobi, hfluxd.deriv]
    ring

end ContinuousFlexibility.Radial
