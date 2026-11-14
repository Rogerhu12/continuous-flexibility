module

public import ContinuousFlexibility.Geometry.Primitive
public import ContinuousFlexibility.Geometry.LocalInverse

/-!
# Cartesian coframe linear algebra

The underlying coordinate space is `ℝ × ℝ`; the names of the two one-form
fields denote its coordinate coefficients here. No positive-radius or
polar chart assumption is made in this file.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

theorem PlaneOneForm.ext_components {α β : PlaneOneForm}
    (hr : α.radial = β.radial) (hθ : α.angular = β.angular) : α = β := by
  cases α
  cases β
  cases hr
  cases hθ
  rfl

/-- The derivative matrix encoded by the two members of a coordinate coframe. -/
def coframeLinearMap (η₁ η₂ : PlaneOneForm) (x : PolarPoint) :
    PolarPoint →L[ℝ] PolarPoint :=
  (η₁.toCLM x).prod (η₂.toCLM x)

theorem PlaneOneForm.toCLM_eq_zero_of_components
    {α : PlaneOneForm} {x : PolarPoint}
    (hr : α.radial x = 0) (hθ : α.angular x = 0) : α.toCLM x = 0 := by
  simp [PlaneOneForm.toCLM, hr, hθ]

theorem coframeLinearMap_eq_id_of_standard
    {η₁ η₂ : PlaneOneForm} {x : PolarPoint}
    (h1r : η₁.radial x = 1) (h1θ : η₁.angular x = 0)
    (h2r : η₂.radial x = 0) (h2θ : η₂.angular x = 1) :
    coframeLinearMap η₁ η₂ x = ContinuousLinearMap.id ℝ PolarPoint := by
  apply ContinuousLinearMap.ext
  intro v
  simp [coframeLinearMap, PlaneOneForm.toCLM, h1r, h1θ, h2r, h2θ]

theorem coframeLinearMap_injective
    {η₁ η₂ : PlaneOneForm} {x : PolarPoint}
    (hwedge : wedgeCoefficient η₁ η₂ x ≠ 0) :
    Function.Injective (coframeLinearMap η₁ η₂ x) := by
  have hker : ∀ v : PolarPoint, coframeLinearMap η₁ η₂ x v = 0 → v = 0 := by
    intro v hv
    have h1 : η₁.radial x * v.1 + η₁.angular x * v.2 = 0 := by
      simpa [coframeLinearMap, PlaneOneForm.toCLM, smul_eq_mul]
        using congrArg Prod.fst hv
    have h2 : η₂.radial x * v.1 + η₂.angular x * v.2 = 0 := by
      simpa [coframeLinearMap, PlaneOneForm.toCLM, smul_eq_mul]
        using congrArg Prod.snd hv
    have hfirst : wedgeCoefficient η₁ η₂ x * v.1 = 0 := by
      calc
        _ = η₂.angular x * (η₁.radial x * v.1 + η₁.angular x * v.2) -
            η₁.angular x * (η₂.radial x * v.1 + η₂.angular x * v.2) := by
          unfold wedgeCoefficient
          ring
        _ = 0 := by rw [h1, h2]; ring
    have hsecond : wedgeCoefficient η₁ η₂ x * v.2 = 0 := by
      calc
        _ = η₁.radial x * (η₂.radial x * v.1 + η₂.angular x * v.2) -
            η₂.radial x * (η₁.radial x * v.1 + η₁.angular x * v.2) := by
          unfold wedgeCoefficient
          ring
        _ = 0 := by rw [h1, h2]; ring
    exact Prod.ext ((mul_eq_zero.mp hfirst).resolve_left hwedge)
      ((mul_eq_zero.mp hsecond).resolve_left hwedge)
  intro u v huv
  apply sub_eq_zero.mp
  apply hker (u - v)
  rw [map_sub, huv, sub_self]

theorem coframeLinearMap_bijective
    {η₁ η₂ : PlaneOneForm} {x : PolarPoint}
    (hwedge : wedgeCoefficient η₁ η₂ x ≠ 0) :
    Function.Bijective (coframeLinearMap η₁ η₂ x) := by
  have hi := coframeLinearMap_injective hwedge
  exact ⟨hi, (LinearMap.injective_iff_surjective
    (f := (coframeLinearMap η₁ η₂ x).toLinearMap)).mp hi⟩

theorem fderiv_bijective_of_hasFDerivAt_coframe
    {η₁ η₂ : PlaneOneForm} {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hP : HasFDerivAt P (coframeLinearMap η₁ η₂ x) x)
    (hwedge : wedgeCoefficient η₁ η₂ x ≠ 0) :
    Function.Bijective (fderiv ℝ P x) := by
  rw [hP.fderiv]
  exact coframeLinearMap_bijective hwedge

end ContinuousFlexibility
