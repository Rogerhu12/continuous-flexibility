module

public import ContinuousFlexibility.Geometry.FlatDevelopment
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Conservation from the actual connection

The integral below uses the manuscript's `dr dθ` density. The proof applies
one-dimensional FTC to both components of a genuine one-form and Fubini to
its radial derivative. Boundary matching is explicit; no Stokes identity or
zero-mean source condition is postulated.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_radial_slice {f : PolarPoint → ℝ} {r θ : ℝ}
    (hf : DifferentiableAt ℝ f (r, θ)) :
    HasDerivAt (fun s => f (s, θ)) (radialPartial f (r, θ)) r := by
  convert! hf.hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ)) using 1

theorem hasDerivAt_angular_slice {f : PolarPoint → ℝ} {r θ : ℝ}
    (hf : DifferentiableAt ℝ f (r, θ)) :
    HasDerivAt (fun t => f (r, t)) (angularPartial f (r, θ)) θ := by
  convert! hf.hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ)) using 1

/-- Translation-periodicity passes to actual partials, including the
totalized derivative at any nondifferentiability point. -/
theorem periodic_radialPartial {f : PolarPoint → ℝ} {v : PolarPoint}
    (hf : Function.Periodic f v) : Function.Periodic (radialPartial f) v := by
  intro x
  have heq : (fun y => f (y + v)) = f := funext hf
  have hd : fderiv ℝ f (x + v) = fderiv ℝ f x := by
    rw [← fderiv_comp_add_right v, heq]
  exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hd

theorem periodic_angularPartial {f : PolarPoint → ℝ} {v : PolarPoint}
    (hf : Function.Periodic f v) : Function.Periodic (angularPartial f) v := by
  intro x
  have heq : (fun y => f (y + v)) = f := funext hf
  have hd : fderiv ℝ f (x + v) = fderiv ℝ f x := by
    rw [← fderiv_comp_add_right v, heq]
  exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hd

theorem heightConnection_periodic
    (w : ℝ → ℝ) {z : PolarPoint → ℝ} {T : ℝ}
    (hz : Function.Periodic z (0, T)) :
    Function.Periodic (heightConnectionForm w z).radial (0, T) ∧
      Function.Periodic (heightConnectionForm w z).angular (0, T) := by
  have hk : Function.Periodic (heightRadial z) (0, T) := periodic_radialPartial hz
  have hp : Function.Periodic (heightAngular z) (0, T) := by
    intro x
    simp only [heightAngular, periodic_angularPartial hz x, Prod.fst_add, add_zero]
  have hpr := periodic_radialPartial hp
  have hpt := periodic_angularPartial hp
  constructor <;> intro x <;>
    simp only [heightConnectionForm, connectionRadialField, connectionAngularField,
      connectionRadialValue, connectionAngularValue, profileEnergy, Prod.fst_add, add_zero,
      hk x, hp x, hpr x, hpt x]

/-- Rectangle conservation for genuine `C¹` coefficients with matching
opposite boundary values. The radius and angle intervals are oriented. -/
theorem integral_exteriorCoefficient_eq_zero
    {α : PlaneOneForm} {a b c d : ℝ}
    (hαr : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ 1 α.radial x)
    (hαθ : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ 1 α.angular x)
    (hperiod : ∀ r ∈ uIcc a b, α.radial (r, d) = α.radial (r, c))
    (hboundary : ∀ θ ∈ uIcc c d, α.angular (b, θ) = α.angular (a, θ)) :
    (∫ r in a..b, ∫ θ in c..d, exteriorCoefficient α (r, θ)) = 0 := by
  have hBr : ContinuousOn (radialPartial α.angular) (uIcc a b ×ˢ uIcc c d) := by
    intro x hx
    exact (contDiffAt_radialPartial (hαθ x hx) (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hAt : ContinuousOn (angularPartial α.radial) (uIcc a b ×ˢ uIcc c d) := by
    intro x hx
    exact (contDiffAt_angularPartial (hαr x hx) (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hBrθ : ∀ r ∈ uIcc a b,
      IntervalIntegrable (fun θ => radialPartial α.angular (r, θ)) volume c d := by
    intro r hr
    exact (hBr.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => ⟨hr, hθ⟩)).intervalIntegrable
  have hAtθ : ∀ r ∈ uIcc a b,
      IntervalIntegrable (fun θ => angularPartial α.radial (r, θ)) volume c d := by
    intro r hr
    exact (hAt.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => ⟨hr, hθ⟩)).intervalIntegrable
  have hAtzero : ∀ r ∈ uIcc a b,
      (∫ θ in c..d, angularPartial α.radial (r, θ)) = 0 := by
    intro r hr
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ hθ => hasDerivAt_angular_slice
        ((hαr (r, θ) ⟨hr, hθ⟩).differentiableAt one_ne_zero)) (hAtθ r hr),
      hperiod r hr, sub_self]
  have hBrzero : ∀ θ ∈ uIcc c d,
      (∫ r in a..b, radialPartial α.angular (r, θ)) = 0 := by
    intro θ hθ
    have hint : IntervalIntegrable (fun r => radialPartial α.angular (r, θ)) volume a b :=
      (hBr.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr, hθ⟩)).intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hasDerivAt_radial_slice
        ((hαθ (r, θ) ⟨hr, hθ⟩).differentiableAt one_ne_zero)) hint,
      hboundary θ hθ, sub_self]
  have hrect : IntegrableOn (radialPartial α.angular) (uIoc a b ×ˢ uIoc c d) :=
    (hBr.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  calc
    (∫ r in a..b, ∫ θ in c..d, exteriorCoefficient α (r, θ)) =
        ∫ r in a..b, ∫ θ in c..d, radialPartial α.angular (r, θ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      change (∫ θ in c..d,
        radialPartial α.angular (r, θ) - angularPartial α.radial (r, θ)) = _
      rw [intervalIntegral.integral_sub (hBrθ r hr) (hAtθ r hr), hAtzero r hr, sub_zero]
    _ = ∫ θ in c..d, ∫ r in a..b, radialPartial α.angular (r, θ) :=
      intervalIntegral_intervalIntegral_swap hrect
    _ = 0 := by
      calc
        _ = ∫ θ in c..d, (0 : ℝ) :=
          intervalIntegral.integral_congr (fun θ hθ => hBrzero θ hθ)
        _ = 0 := by simp

/-- Conservation of the actual height residual under explicitly matching
connection boundary values. No equation `N = 0` is assumed. -/
theorem integral_heightResidual_eq_zero
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {a b c d : ℝ}
    (hw : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ ∞ w x.1)
    (hz : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ ∞ z x)
    (hr : ∀ x ∈ uIcc a b ×ˢ uIcc c d, x.1 ≠ 0)
    (hD : ∀ x ∈ uIcc a b ×ˢ uIcc c d, 0 < polarDiscriminant w z x)
    (hperiod : ∀ r ∈ uIcc a b,
      (heightConnectionForm w z).radial (r, d) = (heightConnectionForm w z).radial (r, c))
    (hboundary : ∀ θ ∈ uIcc c d,
      (heightConnectionForm w z).angular (b, θ) = (heightConnectionForm w z).angular (a, θ)) :
    (∫ r in a..b, ∫ θ in c..d, r * polarCoordinateResidual w z (r, θ)) = 0 := by
  have hα := fun x hx => contDiffAt_heightConnection (hw x hx) (hz x hx) (hr x hx) (hD x hx)
  have hi := integral_exteriorCoefficient_eq_zero
    (fun x hx => (hα x hx).1.of_le (by simp))
    (fun x hx => (hα x hx).2.of_le (by simp)) hperiod hboundary
  convert hi using 1
  apply intervalIntegral.integral_congr
  intro r hrr
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact (heightConnection_exterior_eq_residual
    ((hw (r, θ) ⟨hrr, hθ⟩).differentiableAt (by simp))
    ((hz (r, θ) ⟨hrr, hθ⟩).of_le (by simp))
    (hr (r, θ) ⟨hrr, hθ⟩) (hD (r, θ) ⟨hrr, hθ⟩)).symm

theorem heightConnection_of_boundary_jets
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : w x.1 = 0) (hk : heightRadial z x = 0) (hp : heightAngular z x = 0) :
    (heightConnectionForm w z).radial x = 0 ∧
      (heightConnectionForm w z).angular x = 1 := by
  simp [heightConnectionForm, connectionRadialField, connectionAngularField,
    connectionRadialValue, connectionAngularValue, connectionInverseRoot,
    connectionB1, profileEnergy, radialEnergy, heightDiscriminant, hk, hp, hw]

/-- A genuinely constant height germ in a flat metric collar has the
connection `dθ`. In particular, its boundary period is the angular length. -/
theorem heightConnection_of_flat_collar
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint} {c : ℝ}
    (hw : w x.1 = 0) (hz : z =ᶠ[𝓝 x] fun _ => c) :
    (heightConnectionForm w z).radial x = 0 ∧
      (heightConnectionForm w z).angular x = 1 := by
  have hk : heightRadial z x = 0 := by
    simp [heightRadial, radialPartial, hz.fderiv_eq]
  have hp : heightAngular z x = 0 := by
    simp [heightAngular, angularPartial, hz.fderiv_eq]
  exact heightConnection_of_boundary_jets hw hk hp

/-- The two collar heights may differ: each is represented by its own
constant germ. Their actual connection boundary values are both `1`. -/
theorem integral_heightResidual_eq_zero_of_flat_collars
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {a b c d : ℝ}
    (hw : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ ∞ w x.1)
    (hz : ∀ x ∈ uIcc a b ×ˢ uIcc c d, ContDiffAt ℝ ∞ z x)
    (hr : ∀ x ∈ uIcc a b ×ˢ uIcc c d, x.1 ≠ 0)
    (hD : ∀ x ∈ uIcc a b ×ˢ uIcc c d, 0 < polarDiscriminant w z x)
    (hperiod : ∀ r ∈ uIcc a b,
      (heightConnectionForm w z).radial (r, d) = (heightConnectionForm w z).radial (r, c))
    (hwa : w a = 0) (hwb : w b = 0)
    (hza : ∀ θ ∈ uIcc c d, ∃ ca : ℝ, z =ᶠ[𝓝 (a, θ)] fun _ => ca)
    (hzb : ∀ θ ∈ uIcc c d, ∃ cb : ℝ, z =ᶠ[𝓝 (b, θ)] fun _ => cb) :
    (∫ r in a..b, ∫ θ in c..d, r * polarCoordinateResidual w z (r, θ)) = 0 := by
  apply integral_heightResidual_eq_zero hw hz hr hD hperiod
  intro θ hθ
  obtain ⟨ca, hca⟩ := hza θ hθ
  obtain ⟨cb, hcb⟩ := hzb θ hθ
  rw [(heightConnection_of_flat_collar hwb hcb).2,
    (heightConnection_of_flat_collar hwa hca).2]

/-- A periodic height with genuinely flat endpoint collars has zero total
source in the manuscript's normalized angular-average convention. -/
theorem integral_mean_heightResidual_eq_zero
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {a b T : ℝ}
    (hw : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ w x.1)
    (hz : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ z x)
    (hr : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, x.1 ≠ 0)
    (hD : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, 0 < polarDiscriminant w z x)
    (hperiod : Function.Periodic z (0, T))
    (hwa : w a = 0) (hwb : w b = 0)
    (hza : ∀ θ ∈ uIcc 0 T, ∃ ca : ℝ, z =ᶠ[𝓝 (a, θ)] fun _ => ca)
    (hzb : ∀ θ ∈ uIcc 0 T, ∃ cb : ℝ, z =ᶠ[𝓝 (b, θ)] fun _ => cb) :
    (∫ r in a..b, (1 / T) * ∫ θ in 0..T,
      r * polarCoordinateResidual w z (r, θ)) = 0 := by
  have hp : ∀ r ∈ uIcc a b,
      (heightConnectionForm w z).radial (r, T) = (heightConnectionForm w z).radial (r, 0) := by
    intro r _
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      (heightConnection_periodic w hperiod).1 (r, 0)
  rw [intervalIntegral.integral_const_mul,
    integral_heightResidual_eq_zero_of_flat_collars hw hz hr hD hp hwa hwb hza hzb, mul_zero]

/-- First boundary jets suffice for compatibility; no constant germ or
open planar collar is needed at this analytic stage. The endpoint height
values are unrestricted and may differ. -/
theorem integral_mean_heightResidual_eq_zero_of_boundary_jets
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {a b T : ℝ}
    (hw : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ w x.1)
    (hz : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, ContDiffAt ℝ ∞ z x)
    (hr : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, x.1 ≠ 0)
    (hD : ∀ x ∈ uIcc a b ×ˢ uIcc 0 T, 0 < polarDiscriminant w z x)
    (hperiod : Function.Periodic z (0, T))
    (hwa : w a = 0) (hwb : w b = 0)
    (hka : ∀ θ ∈ uIcc 0 T, heightRadial z (a, θ) = 0)
    (hpa : ∀ θ ∈ uIcc 0 T, heightAngular z (a, θ) = 0)
    (hkb : ∀ θ ∈ uIcc 0 T, heightRadial z (b, θ) = 0)
    (hpb : ∀ θ ∈ uIcc 0 T, heightAngular z (b, θ) = 0) :
    (∫ r in a..b, (1 / T) * ∫ θ in 0..T,
      r * polarCoordinateResidual w z (r, θ)) = 0 := by
  have hp : ∀ r ∈ uIcc a b,
      (heightConnectionForm w z).radial (r, T) = (heightConnectionForm w z).radial (r, 0) := by
    intro r _
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      (heightConnection_periodic w hperiod).1 (r, 0)
  have hb : ∀ θ ∈ uIcc 0 T,
      (heightConnectionForm w z).angular (b, θ) = (heightConnectionForm w z).angular (a, θ) := by
    intro θ hθ
    rw [(heightConnection_of_boundary_jets hwb (hkb θ hθ) (hpb θ hθ)).2,
      (heightConnection_of_boundary_jets hwa (hka θ hθ) (hpa θ hθ)).2]
  rw [intervalIntegral.integral_const_mul,
    integral_heightResidual_eq_zero hw hz hr hD hp hb, mul_zero]

end ContinuousFlexibility
