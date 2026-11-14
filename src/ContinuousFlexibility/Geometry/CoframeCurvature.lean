module

public import ContinuousFlexibility.Geometry.CoframeSO2

/-!
# Curvature is independent of an oriented metric coframe

Equal quadratic metrics and equal orientation determine actual smooth relative
SO(2) coefficients. The two Cartan connections then differ by `C dS - S dC`,
whose actual exterior derivative vanishes. No global angle is required.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem exteriorCoefficient_congr_germ {α β : PlaneOneForm} {x : PolarPoint}
    (hr : α.radial =ᶠ[𝓝 x] β.radial) (hθ : α.angular =ᶠ[𝓝 x] β.angular) :
    exteriorCoefficient α x = exteriorCoefficient β x := by
  unfold exteriorCoefficient radialPartial angularPartial
  rw [hθ.fderiv_eq, hr.fderiv_eq]

theorem cartan_connection_unique {η₁ η₂ α β : PlaneOneForm} {x : PolarPoint}
    (hw : wedgeCoefficient η₁ η₂ x ≠ 0)
    (h1 : wedgeCoefficient α η₁ x = wedgeCoefficient β η₁ x)
    (h2 : wedgeCoefficient α η₂ x = wedgeCoefficient β η₂ x) :
    α.radial x = β.radial x ∧ α.angular x = β.angular x := by
  have hr : wedgeCoefficient η₁ η₂ x * (α.radial x - β.radial x) = 0 := by
    unfold wedgeCoefficient at *
    linear_combination η₁.radial x * h2 - η₂.radial x * h1
  have hθ : wedgeCoefficient η₁ η₂ x * (α.angular x - β.angular x) = 0 := by
    unfold wedgeCoefficient at *
    linear_combination η₁.angular x * h2 - η₂.angular x * h1
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left hw),
    sub_eq_zero.mp ((mul_eq_zero.mp hθ).resolve_left hw)⟩

theorem contDiffAt_relativeCoframeRotation {n : ℕ∞ω}
    {η₁ η₂ ξ₁ : PlaneOneForm} {x : PolarPoint}
    (h1r : ContDiffAt ℝ n η₁.radial x) (h1θ : ContDiffAt ℝ n η₁.angular x)
    (h2r : ContDiffAt ℝ n η₂.radial x) (h2θ : ContDiffAt ℝ n η₂.angular x)
    (hξr : ContDiffAt ℝ n ξ₁.radial x) (hξθ : ContDiffAt ℝ n ξ₁.angular x)
    (hw : wedgeCoefficient η₁ η₂ x ≠ 0) :
    ContDiffAt ℝ n (relativeCoframeCos η₁ η₂ ξ₁) x ∧
      ContDiffAt ℝ n (relativeCoframeSin η₁ η₂ ξ₁) x := by
  have hd : ContDiffAt ℝ n (fun y => wedgeCoefficient η₁ η₂ y) x :=
    (h1r.mul h2θ).sub (h1θ.mul h2r)
  exact ⟨((hξr.mul h2θ).sub (hξθ.mul h2r)).div hd hw,
    ((hξr.mul h1θ).sub (hξθ.mul h1r)).div hd hw⟩

/-- Two oriented smooth coframes for the same quadratic metric have the same actual
Cartan curvature coefficient. The Cartan equations, rather than curvature equality,
are the connection hypotheses. -/
theorem coframe_curvature_eq_of_same_metric
    {U : Set PolarPoint} (hU : IsOpen U) {x : PolarPoint} (hx : x ∈ U)
    {η₁ η₂ ξ₁ ξ₂ α β : PlaneOneForm}
    (hη : ∀ y ∈ U, ContDiffAt ℝ ∞ η₁.radial y ∧ ContDiffAt ℝ ∞ η₁.angular y ∧
      ContDiffAt ℝ ∞ η₂.radial y ∧ ContDiffAt ℝ ∞ η₂.angular y)
    (hξ : ∀ y ∈ U, ContDiffAt ℝ ∞ ξ₁.radial y ∧ ContDiffAt ℝ ∞ ξ₁.angular y ∧
      ContDiffAt ℝ ∞ ξ₂.radial y ∧ ContDiffAt ℝ ∞ ξ₂.angular y)
    (hαr : DifferentiableAt ℝ α.radial x) (hαθ : DifferentiableAt ℝ α.angular x)
    (hcartη : ∀ y ∈ U,
      exteriorCoefficient η₁ y = wedgeCoefficient α η₂ y ∧
      exteriorCoefficient η₂ y = -wedgeCoefficient α η₁ y)
    (hcartξ : ∀ y ∈ U,
      exteriorCoefficient ξ₁ y = wedgeCoefficient β ξ₂ y ∧
      exteriorCoefficient ξ₂ y = -wedgeCoefficient β ξ₁ y)
    (hmetric : ∀ y ∈ U, ∀ v : PolarPoint,
      formValue ξ₁ y v ^ 2 + formValue ξ₂ y v ^ 2 =
        formValue η₁ y v ^ 2 + formValue η₂ y v ^ 2)
    (hor : ∀ y ∈ U, 0 < wedgeCoefficient η₁ η₂ y * wedgeCoefficient ξ₁ ξ₂ y) :
    exteriorCoefficient β x = exteriorCoefficient α x := by
  let C := relativeCoframeCos η₁ η₂ ξ₁
  let S := relativeCoframeSin η₁ η₂ ξ₁
  let τ := so2Connection C S
  let γ := subtractPlaneOneForm α τ
  have hwη : ∀ y ∈ U, wedgeCoefficient η₁ η₂ y ≠ 0 := by
    intro y hy hz
    have hp := hor y hy
    rw [hz, zero_mul] at hp
    exact (lt_irrefl 0) hp
  have hwξ : ∀ y ∈ U, wedgeCoefficient ξ₁ ξ₂ y ≠ 0 := by
    intro y hy hz
    have hp := hor y hy
    rw [hz, mul_zero] at hp
    exact (lt_irrefl 0) hp
  have hCS : ∀ y ∈ U, ContDiffAt ℝ ∞ C y ∧ ContDiffAt ℝ ∞ S y := by
    intro y hy
    obtain ⟨h1r, h1θ, h2r, h2θ⟩ := hη y hy
    obtain ⟨hξr, hξθ, _, _⟩ := hξ y hy
    exact contDiffAt_relativeCoframeRotation h1r h1θ h2r h2θ hξr hξθ (hwη y hy)
  have hrot : ∀ y ∈ U, C y ^ 2 + S y ^ 2 = 1 ∧
      ξ₁.radial y = C y * η₁.radial y - S y * η₂.radial y ∧
      ξ₁.angular y = C y * η₁.angular y - S y * η₂.angular y ∧
      ξ₂.radial y = S y * η₁.radial y + C y * η₂.radial y ∧
      ξ₂.angular y = S y * η₁.angular y + C y * η₂.angular y :=
    fun y hy => relativeCoframe_rotation (hmetric y hy) (hor y hy)
  have hunit : ∀ y ∈ U, (fun q => C q ^ 2 + S q ^ 2) =ᶠ[𝓝 y] fun _ => 1 := by
    intro y hy
    filter_upwards [hU.mem_nhds hy] with q hq
    exact (hrot q hq).1
  have hconn : ∀ y ∈ U, β.radial y = γ.radial y ∧ β.angular y = γ.angular y := by
    intro y hy
    obtain ⟨h1r, h1θ, h2r, h2θ⟩ := hη y hy
    obtain ⟨hCy, hSy⟩ := hCS y hy
    have hg := so2Coframe_cartan (hCy.differentiableAt (by simp)) (hSy.differentiableAt (by simp))
      (h1r.differentiableAt (by simp)) (h1θ.differentiableAt (by simp))
      (h2r.differentiableAt (by simp)) (h2θ.differentiableAt (by simp))
      (hunit y hy) (hcartη y hy).1 (hcartη y hy).2
    have hr1 : ξ₁.radial =ᶠ[𝓝 y] (so2CoframeOne C S η₁ η₂).radial := by
      filter_upwards [hU.mem_nhds hy] with q hq
      exact (hrot q hq).2.1
    have hθ1 : ξ₁.angular =ᶠ[𝓝 y] (so2CoframeOne C S η₁ η₂).angular := by
      filter_upwards [hU.mem_nhds hy] with q hq
      exact (hrot q hq).2.2.1
    have hr2 : ξ₂.radial =ᶠ[𝓝 y] (so2CoframeTwo C S η₁ η₂).radial := by
      filter_upwards [hU.mem_nhds hy] with q hq
      exact (hrot q hq).2.2.2.1
    have hθ2 : ξ₂.angular =ᶠ[𝓝 y] (so2CoframeTwo C S η₁ η₂).angular := by
      filter_upwards [hU.mem_nhds hy] with q hq
      exact (hrot q hq).2.2.2.2
    have hg1 : exteriorCoefficient ξ₁ y = wedgeCoefficient γ ξ₂ y := by
      rw [exteriorCoefficient_congr_germ hr1 hθ1, hg.1]
      change γ.radial y * (S y * η₁.angular y + C y * η₂.angular y) -
        γ.angular y * (S y * η₁.radial y + C y * η₂.radial y) = _
      rw [← (hrot y hy).2.2.2.1, ← (hrot y hy).2.2.2.2]
      rfl
    have hg2 : exteriorCoefficient ξ₂ y = -wedgeCoefficient γ ξ₁ y := by
      rw [exteriorCoefficient_congr_germ hr2 hθ2, hg.2]
      change -(γ.radial y * (C y * η₁.angular y - S y * η₂.angular y) -
        γ.angular y * (C y * η₁.radial y - S y * η₂.radial y)) = _
      rw [← (hrot y hy).2.1, ← (hrot y hy).2.2.1]
      rfl
    apply cartan_connection_unique (hwξ y hy)
    · linarith [(hcartξ y hy).2, hg2]
    · exact (hcartξ y hy).1.symm.trans hg1
  have hβr : β.radial =ᶠ[𝓝 x] γ.radial := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hconn y hy).1
  have hβθ : β.angular =ᶠ[𝓝 x] γ.angular := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hconn y hy).2
  obtain ⟨hCx, hSx⟩ := hCS x hx
  obtain ⟨hτr, hτθ⟩ := contDiffAt_so2Connection hCx hSx
  have hτclosed : exteriorCoefficient τ x = 0 :=
    so2Connection_closed (hCx.of_le (by simp)) (hSx.of_le (by simp)) (hunit x hx)
  calc
    exteriorCoefficient β x = exteriorCoefficient γ x := exteriorCoefficient_congr_germ hβr hβθ
    _ = exteriorCoefficient α x - exteriorCoefficient τ x :=
      exteriorCoefficient_subtractPlaneOneForm hαr hαθ
        (hτr.differentiableAt (by simp)) (hτθ.differentiableAt (by simp))
    _ = exteriorCoefficient α x := by rw [hτclosed, sub_zero]

end ContinuousFlexibility
