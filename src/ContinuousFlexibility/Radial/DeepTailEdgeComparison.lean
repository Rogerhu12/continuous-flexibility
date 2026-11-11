import ContinuousFlexibility.Radial.DeepTailPhysicalPoisson
import ContinuousFlexibility.Radial.TailMassResistanceData

/-!
# Comparing an actual tail solution with its endpoint interpolation

The positive right Poisson function gives Dirichlet uniqueness. Thus the
pointwise Poisson bounds control every actual natural solution, rather
than only a separately chosen model solution.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

namespace TailPhysicalPoissonData

variable {p : ℝ → ℝ} {a b Λ η : ℝ} {hab : a ≤ b}
  (B : TailPhysicalPoissonData p a b Λ η hab)

/-- Interpolation by the actual two endpoint Poisson functions. -/
def interpolate (A Z : ℝ) : ℝ → ℝ := fun x => A * B.u false x + Z * B.u true x

theorem interpolate_differentiable (A Z : ℝ) : Differentiable ℝ (B.interpolate A Z) :=
  ((B.differentiable false).const_mul A).add ((B.differentiable true).const_mul Z)

theorem interpolate_deriv (A Z x : ℝ) :
    deriv (B.interpolate A Z) x = A * deriv (B.u false) x + Z * deriv (B.u true) x :=
  (((B.differentiable false x).hasDerivAt.const_mul A).add
    ((B.differentiable true x).hasDerivAt.const_mul Z)).deriv

theorem interpolate_derivative_continuous (A Z : ℝ) :
    Continuous (deriv (B.interpolate A Z)) := by
  have h : deriv (B.interpolate A Z) =
      fun x => A * deriv (B.u false) x + Z * deriv (B.u true) x :=
    funext (B.interpolate_deriv A Z)
  rw [h]
  exact ((B.derivative_continuous false).const_mul A).add
    ((B.derivative_continuous true).const_mul Z)

@[simp] theorem interpolate_left (A Z : ℝ) : B.interpolate A Z a = A := by
  simp [interpolate, B.left_endpoint]

@[simp] theorem interpolate_right (A Z : ℝ) : B.interpolate A Z b = Z := by
  simp [interpolate, B.right_endpoint]

theorem interpolate_equation (A Z : ℝ) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => p y * deriv (B.interpolate A Z) y)
      (-(Λ * p x * B.interpolate A Z x)) x := by
  convert ((B.equation false x hx).const_mul A).add
    ((B.equation true x hx).const_mul Z) using 1
  · funext y
    dsimp only
    rw [B.interpolate_deriv]
    ring
  · dsimp only [interpolate]
    ring

theorem right_pos (hlt : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) {x : ℝ} (hx : x ∈ Ioc a b) :
    0 < B.u true x := by
  have hS := tailResistanceChart_strictMono
    (tailClampedDensity_continuous hab hp) (tailClampedDensity_pos hab hpos) a
  have h0 : tailResistanceChart (tailClampedDensity p a b hab) a a = 0 :=
    intervalIntegral.integral_same
  have hx' : 0 < tailResistanceChart (tailClampedDensity p a b hab) a x := by
    simpa only [h0] using hS hx.1
  have hb' : 0 < tailResistanceChart (tailClampedDensity p a b hab) a b := by
    simpa only [h0] using hS hlt
  exact (div_pos hx' hb').trans_le (B.bounds true x ⟨hx.1.le, hx.2⟩).1

/-- The actual solution equals the interpolation of its actual endpoint
values. Only interior differential equations are required. -/
theorem eq_interpolate {u : ℝ → ℝ} (hlt : a < b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < p x)
    (hu : ContinuousOn u (Icc a b)) (hdu : ContinuousOn (deriv u) (Icc a b))
    (huD : ∀ x ∈ Ioo a b, HasDerivAt u (deriv u x) x)
    (hflux : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => p y * deriv u y) (-(Λ * p x * u x)) x) :
    EqOn u (B.interpolate (u a) (u b)) (Icc a b) := by
  apply tailEdge_solutions_eq_of_positive_solution hlt hp hu hdu
    (B.interpolate_differentiable _ _).continuous.continuousOn
    (B.interpolate_derivative_continuous _ _).continuousOn
    (B.differentiable true).continuous.continuousOn (B.derivative_continuous true).continuousOn
    (fun x hx => hpos x (Ioo_subset_Icc_self hx)) huD
    (fun x _ => (B.interpolate_differentiable _ _ x).hasDerivAt)
    (fun x _ => (B.differentiable true x).hasDerivAt) hflux
    (fun _ hx => B.interpolate_equation _ _ hx) (B.equation true)
  · exact (B.interpolate_left _ _).symm
  · exact (B.interpolate_right _ _).symm
  · exact B.left_endpoint true
  · exact fun _ hx => B.right_pos hlt hp hpos hx

theorem basis_bounds (hlt : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hη : η < 1) (right : Bool)
    {x : ℝ} (hx : x ∈ Icc a b) : 0 ≤ B.u right x ∧ B.u right x ≤ 1 / (1 - η) := by
  have hS := tailResistanceChart_strictMono
    (tailClampedDensity_continuous hab hp) (tailClampedDensity_pos hab hpos) a
  let S := tailResistanceChart (tailClampedDensity p a b hab) a
  have h0 : S a = 0 := intervalIntegral.integral_same
  have hL : 0 < S b := by simpa only [h0] using hS hlt
  have hxl : 0 ≤ S x := by simpa only [h0] using hS.monotone hx.1
  have hxr : S x ≤ S b := hS.monotone hx.2
  have hh : 0 ≤ tailPhysicalHeight p a b hab right x ∧
      tailPhysicalHeight p a b hab right x ≤ 1 := by
    cases right
    · exact ⟨div_nonneg (sub_nonneg.mpr hxr) hL.le,
        (div_le_one hL).mpr (sub_le_self _ hxl)⟩
    · exact ⟨div_nonneg hxl hL.le, (div_le_one hL).mpr hxr⟩
  exact ⟨hh.1.trans (B.bounds right x hx).1,
    (B.bounds right x hx).2.trans (div_le_div_of_nonneg_right hh.2 (sub_pos.mpr hη).le)⟩

theorem interpolate_bound (hlt : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hη : η < 1) (A Z : ℝ)
    {x : ℝ} (hx : x ∈ Icc a b) :
    |B.interpolate A Z x| ≤ (|A| + |Z|) / (1 - η) := by
  have h₀ := B.basis_bounds hlt hp hpos hη false hx
  have h₁ := B.basis_bounds hlt hp hpos hη true hx
  calc
    _ ≤ |A * B.u false x| + |Z * B.u true x| := abs_add_le _ _
    _ = |A| * B.u false x + |Z| * B.u true x := by
      rw [abs_mul, abs_mul, abs_of_nonneg h₀.1, abs_of_nonneg h₁.1]
    _ ≤ |A| * (1 / (1 - η)) + |Z| * (1 / (1 - η)) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀.2 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h₁.2 (abs_nonneg _))
    _ = _ := by ring

end TailPhysicalPoissonData

end ContinuousFlexibility.Radial
