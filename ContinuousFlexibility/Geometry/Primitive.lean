import ContinuousFlexibility.Geometry.RotatedCoframe
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Primitives of closed coordinate one-forms

The coordinate curl is identified with symmetry of the actual derivative
of a continuous-linear-map-valued one-form. The primitive is then obtained
from mathlib's Poincare lemma on open convex sets, not assumed to exist.

The two-component development here takes values in `ℝ × ℝ` as a coordinate
space. Its Euclidean metric is the sum of coordinate squares; it is not
identified with the default product norm.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A coordinate one-form as a continuous-linear-map-valued field. -/
def PlaneOneForm.toCLM (η : PlaneOneForm) (x : PolarPoint) : PolarPoint →L[ℝ] ℝ :=
  η.radial x • ContinuousLinearMap.fst ℝ ℝ ℝ +
    η.angular x • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem PlaneOneForm.toCLM_apply (η : PlaneOneForm) (x v : PolarPoint) :
    η.toCLM x v = formValue η x v := by
  simp [PlaneOneForm.toCLM, formValue, smul_eq_mul]

variable {η η₁ η₂ : PlaneOneForm} {x : PolarPoint}

theorem PlaneOneForm.hasFDerivAt_toCLM
    (hr : DifferentiableAt ℝ η.radial x) (hθ : DifferentiableAt ℝ η.angular x) :
    HasFDerivAt η.toCLM
      ((fderiv ℝ η.radial x).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
        (fderiv ℝ η.angular x).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
  exact (hr.hasFDerivAt.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
    (hθ.hasFDerivAt.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem PlaneOneForm.differentiableAt_toCLM
    (hr : DifferentiableAt ℝ η.radial x) (hθ : DifferentiableAt ℝ η.angular x) :
    DifferentiableAt ℝ η.toCLM x :=
  (η.hasFDerivAt_toCLM hr hθ).differentiableAt

theorem PlaneOneForm.fderiv_toCLM_apply
    (hr : DifferentiableAt ℝ η.radial x) (hθ : DifferentiableAt ℝ η.angular x)
    (u v : PolarPoint) :
    fderiv ℝ η.toCLM x u v =
      fderiv ℝ η.radial x u * v.1 + fderiv ℝ η.angular x u * v.2 := by
  rw [(η.hasFDerivAt_toCLM hr hθ).fderiv]
  simp [smul_eq_mul]

/-- Evaluation of an arbitrary continuous linear functional in the coordinate basis. -/
theorem polarCLM_apply_decompose (L : PolarPoint →L[ℝ] ℝ) (u : PolarPoint) :
    L u = u.1 * L (1, 0) + u.2 * L (0, 1) := by
  have hu : u = u.1 • (1, 0) + u.2 • (0, 1) := by
    ext <;> simp [smul_eq_mul]
  calc
    L u = L (u.1 • (1, 0) + u.2 • (0, 1)) := congrArg L hu
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

/-- The skew part of the actual derivative is the coordinate exterior coefficient. -/
theorem PlaneOneForm.fderiv_toCLM_skew
    (hr : DifferentiableAt ℝ η.radial x) (hθ : DifferentiableAt ℝ η.angular x)
    (u v : PolarPoint) :
    fderiv ℝ η.toCLM x u v - fderiv ℝ η.toCLM x v u =
      exteriorCoefficient η x * (u.1 * v.2 - u.2 * v.1) := by
  rw [η.fderiv_toCLM_apply hr hθ, η.fderiv_toCLM_apply hr hθ]
  rw [polarCLM_apply_decompose (fderiv ℝ η.radial x) u,
    polarCLM_apply_decompose (fderiv ℝ η.angular x) u,
    polarCLM_apply_decompose (fderiv ℝ η.radial x) v,
    polarCLM_apply_decompose (fderiv ℝ η.angular x) v]
  unfold exteriorCoefficient radialPartial angularPartial
  ring

theorem exteriorCoefficient_eq_zero_iff_fderiv_toCLM_symmetric
    (hr : DifferentiableAt ℝ η.radial x) (hθ : DifferentiableAt ℝ η.angular x) :
    exteriorCoefficient η x = 0 ↔
      ∀ u v : PolarPoint, fderiv ℝ η.toCLM x u v = fderiv ℝ η.toCLM x v u := by
  constructor
  · intro hc u v
    apply sub_eq_zero.mp
    rw [η.fderiv_toCLM_skew hr hθ, hc, zero_mul]
  · intro hs
    have hskew := η.fderiv_toCLM_skew hr hθ (1, 0) (0, 1)
    rw [hs (1, 0) (0, 1), sub_self] at hskew
    simpa using hskew.symm

theorem PlaneOneForm.contDiffAt_toCLM {n : ℕ∞ω}
    (hr : ContDiffAt ℝ n η.radial x) (hθ : ContDiffAt ℝ n η.angular x) :
    ContDiffAt ℝ n η.toCLM x := by
  exact (hr.smul contDiffAt_const).add (hθ.smul contDiffAt_const)

/-- A genuinely closed coordinate one-form has a primitive on every open convex set. -/
theorem exists_primitive_of_closed {U : Set PolarPoint}
    (hU : Convex ℝ U) (hUo : IsOpen U)
    (hr : ∀ x ∈ U, DifferentiableAt ℝ η.radial x)
    (hθ : ∀ x ∈ U, DifferentiableAt ℝ η.angular x)
    (hc : ∀ x ∈ U, exteriorCoefficient η x = 0) :
    ∃ f : PolarPoint → ℝ, ∀ x ∈ U, HasFDerivAt f (η.toCLM x) x := by
  apply hU.exists_forall_hasFDerivAt_of_fderiv_symmetric hUo
  · intro x hx
    exact (η.differentiableAt_toCLM (hr x hx) (hθ x hx)).differentiableWithinAt
  · intro x hx
    exact (exteriorCoefficient_eq_zero_iff_fderiv_toCLM_symmetric
      (hr x hx) (hθ x hx)).mp (hc x hx)

/-- The primitive can be normalized at any prescribed base point. -/
theorem exists_primitive_of_closed_eq_zero {U : Set PolarPoint}
    (hU : Convex ℝ U) (hUo : IsOpen U)
    (hr : ∀ x ∈ U, DifferentiableAt ℝ η.radial x)
    (hθ : ∀ x ∈ U, DifferentiableAt ℝ η.angular x)
    (hc : ∀ x ∈ U, exteriorCoefficient η x = 0) (a : PolarPoint) :
    ∃ f : PolarPoint → ℝ, f a = 0 ∧ ∀ x ∈ U, HasFDerivAt f (η.toCLM x) x := by
  obtain ⟨f, hf⟩ := exists_primitive_of_closed hU hUo hr hθ hc
  refine ⟨fun y => f y - f a, sub_self _, ?_⟩
  intro x hx
  exact (hf x hx).sub_const (f a)

/-- A primitive gains one finite differentiability order from its coefficient field. -/
theorem contDiffAt_of_primitive {U : Set PolarPoint} {f : PolarPoint → ℝ} {n : ℕ}
    (hUo : IsOpen U) (hx : x ∈ U)
    (hf : ∀ y ∈ U, HasFDerivAt f (η.toCLM y) y)
    (hr : ContDiffAt ℝ n η.radial x) (hθ : ContDiffAt ℝ n η.angular x) :
    ContDiffAt ℝ (n + 1) f x := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  exact ⟨η.toCLM, ⟨U, hUo.mem_nhds hx, hf⟩, η.contDiffAt_toCLM hr hθ⟩

/-- Smooth coefficient fields give a genuinely `C∞` primitive, without analyticity. -/
theorem contDiffAt_of_primitive_infty {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hUo : IsOpen U) (hx : x ∈ U)
    (hf : ∀ y ∈ U, HasFDerivAt f (η.toCLM y) y)
    (hr : ContDiffAt ℝ ∞ η.radial x) (hθ : ContDiffAt ℝ ∞ η.angular x) :
    ContDiffAt ℝ ∞ f x := by
  apply contDiffAt_infty.mpr
  intro n
  have hs := contDiffAt_of_primitive hUo hx hf
    (contDiffAt_infty.mp hr n) (contDiffAt_infty.mp hθ n)
  exact hs.of_le (by exact_mod_cast Nat.le_succ n)

/-- Integrating each closed member of a coframe gives an actual two-coordinate development. -/
theorem exists_development_of_closed_coframe {U : Set PolarPoint}
    (hU : Convex ℝ U) (hUo : IsOpen U)
    (h1r : ∀ x ∈ U, DifferentiableAt ℝ η₁.radial x)
    (h1θ : ∀ x ∈ U, DifferentiableAt ℝ η₁.angular x)
    (h2r : ∀ x ∈ U, DifferentiableAt ℝ η₂.radial x)
    (h2θ : ∀ x ∈ U, DifferentiableAt ℝ η₂.angular x)
    (hc1 : ∀ x ∈ U, exteriorCoefficient η₁ x = 0)
    (hc2 : ∀ x ∈ U, exteriorCoefficient η₂ x = 0) :
    ∃ P : PolarPoint → PolarPoint,
      ∀ x ∈ U, HasFDerivAt P ((η₁.toCLM x).prod (η₂.toCLM x)) x := by
  obtain ⟨f, hf⟩ := exists_primitive_of_closed hU hUo h1r h1θ hc1
  obtain ⟨g, hg⟩ := exists_primitive_of_closed hU hUo h2r h2θ hc2
  exact ⟨fun x => (f x, g x), fun x hx => (hf x hx).prodMk (hg x hx)⟩

/-- A smooth closed coframe has a smooth development, obtained from actual primitives. -/
theorem exists_smooth_development_of_closed_coframe {U : Set PolarPoint}
    (hU : Convex ℝ U) (hUo : IsOpen U)
    (h1r : ∀ x ∈ U, ContDiffAt ℝ ∞ η₁.radial x)
    (h1θ : ∀ x ∈ U, ContDiffAt ℝ ∞ η₁.angular x)
    (h2r : ∀ x ∈ U, ContDiffAt ℝ ∞ η₂.radial x)
    (h2θ : ∀ x ∈ U, ContDiffAt ℝ ∞ η₂.angular x)
    (hc1 : ∀ x ∈ U, exteriorCoefficient η₁ x = 0)
    (hc2 : ∀ x ∈ U, exteriorCoefficient η₂ x = 0) :
    ∃ P : PolarPoint → PolarPoint,
      (∀ x ∈ U, HasFDerivAt P ((η₁.toCLM x).prod (η₂.toCLM x)) x) ∧
        ∀ x ∈ U, ContDiffAt ℝ ∞ P x := by
  obtain ⟨f, hf⟩ := exists_primitive_of_closed hU hUo
    (fun x hx => (h1r x hx).differentiableAt (by simp))
    (fun x hx => (h1θ x hx).differentiableAt (by simp)) hc1
  obtain ⟨g, hg⟩ := exists_primitive_of_closed hU hUo
    (fun x hx => (h2r x hx).differentiableAt (by simp))
    (fun x hx => (h2θ x hx).differentiableAt (by simp)) hc2
  refine ⟨fun y => (f y, g y), fun x hx => (hf x hx).prodMk (hg x hx), ?_⟩
  intro x hx
  exact (contDiffAt_of_primitive_infty hUo hx hf (h1r x hx) (h1θ x hx)).prodMk
    (contDiffAt_of_primitive_infty hUo hx hg (h2r x hx) (h2θ x hx))

theorem development_fderiv_apply {P : PolarPoint → PolarPoint}
    (hP : HasFDerivAt P ((η₁.toCLM x).prod (η₂.toCLM x)) x) (v : PolarPoint) :
    fderiv ℝ P x v = (formValue η₁ x v, formValue η₂ x v) := by
  rw [hP.fderiv]
  simp [PlaneOneForm.toCLM_apply]

/-- The coordinate Euclidean quadratic form of the derivative is the coframe sum. -/
theorem development_derivative_square_sum {P : PolarPoint → PolarPoint}
    (hP : HasFDerivAt P ((η₁.toCLM x).prod (η₂.toCLM x)) x) (v : PolarPoint) :
    (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
      formValue η₁ x v ^ 2 + formValue η₂ x v ^ 2 := by
  rw [development_fderiv_apply hP v]

end ContinuousFlexibility
