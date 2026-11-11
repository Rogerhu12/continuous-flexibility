import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation

/-!
# Identifying actual derivatives in homogeneous operator parameters

Linearity of the frozen input maps makes the relevant real difference
quotients exactly constant.  Uniqueness in the actual Hausdorff target then
identifies the first and mixed second entries of any genuine directional
tower.  No continuity of an independently frozen algebraic map is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section AlgebraicCurves

variable {X Y R Z : Type*}
  [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  [AddCommGroup R] [Module ℝ R]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

/-- Along a pure linear input direction the actual difference quotient
is constant, even when no continuity of the frozen map has been assumed. -/
theorem hasProjectiveLineDerivAt_linearFamily_right
    (L : X → Y →ₗ[ℝ] Z) (x : X) (y u : Y) :
    HasProjectiveLineDerivAt (fun z : X × Y => L z.1 z.2)
      (L x u) (x, y) (0, u) := by
  have hquot (t : ℝ) (ht : t ≠ 0) :
      t⁻¹ • ((fun z : X × Y => L z.1 z.2) ((x, y) + t • (0, u)) - L x y) =
        L x u := by
    change t⁻¹ • (L (x + t • 0) (y + t • u) - L x y) = L x u
    rw [smul_zero, add_zero, map_add, map_smul, add_sub_cancel_left,
      smul_smul, inv_mul_cancel₀ ht, one_smul]
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
  simp only [zero_add, zero_smul, add_zero]
  apply (tendsto_const_nhds (x := L x u) :
    Tendsto (fun _ : ℝ => L x u) (𝓝[≠] (0 : ℝ)) (𝓝 (L x u))).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hquot t (by simpa using ht)).symm

/-- Differentiating the first frozen input after evaluating the second
one again produces an exact constant difference quotient. -/
theorem hasProjectiveLineDerivAt_bilinearFamily_first
    (B : X → R →ₗ[ℝ] Y →ₗ[ℝ] Z) (x : X) (r dr : R) (y u : Y) :
    HasProjectiveLineDerivAt (fun z : (X × R) × Y => B z.1.1 z.1.2 u)
      (B x dr u) ((x, r), y) ((0, dr), 0) := by
  have hquot (t : ℝ) (ht : t ≠ 0) :
      t⁻¹ • ((fun z : (X × R) × Y => B z.1.1 z.1.2 u)
        (((x, r), y) + t • ((0, dr), 0)) - B x r u) = B x dr u := by
    change t⁻¹ • (B (x + t • 0) (r + t • dr) u - B x r u) = B x dr u
    simp only [smul_zero, add_zero, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, RingHom.id_apply,
      add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
  simp only [zero_add, zero_smul, add_zero]
  apply (tendsto_const_nhds (x := B x dr u) :
    Tendsto (fun _ : ℝ => B x dr u) (𝓝[≠] (0 : ℝ)) (𝓝 (B x dr u))).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hquot t (by simpa using ht)).symm

end AlgebraicCurves

section ActualTowers

variable {X Y R Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [TopologicalSpace R] [AddCommGroup R] [Module ℝ R]
  [IsTopologicalAddGroup R] [ContinuousSMul ℝ R]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z] [T2Space Z]

/-- Every genuine first jet in a pure linear input direction equals the
frozen algebraic linear map at the same state. -/
theorem SmoothDirections.linearFamily_first_at
    (L : X → Y →ₗ[ℝ] Z) {U : Set (X × Y)}
    (J : SmoothDirections U (fun z : X × Y => L z.1 z.2))
    {x : X} {y : Y} (hxy : (x, y) ∈ U) (u : Y) :
    J.D 1 (x, y) ![(0, u)] = L x u := by
  change projectiveFirstJetValue J.D (x, y) (0, u) = L x u
  exact (J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hxy (0, u)).unique
    (hasProjectiveLineDerivAt_linearFamily_right L x y u)

theorem SmoothDirections.linearFamily_first
    (L : X → Y →ₗ[ℝ] Z) {U : Set (X × Y)}
    (J : SmoothDirections U (fun z : X × Y => L z.1 z.2))
    {x : X} (hx : (x, (0 : Y)) ∈ U) (u : Y) :
    J.D 1 (x, 0) (fun _ : Fin 1 => (0, u)) = L x u := by
  have hvec : (fun _ : Fin 1 => ((0 : X), u)) = ![(0, u)] := by
    funext i
    fin_cases i
    rfl
  rw [hvec]
  exact J.linearFamily_first_at L hx u

theorem SmoothDirections.linearFamily_first_zero
    (L : X → Y →ₗ[ℝ] Z) {U : Set (X × Y)}
    (J : SmoothDirections U (fun z : X × Y => L z.1 z.2))
    {x : X} (hx : (x, (0 : Y)) ∈ U) (u : Y) :
    J.D 1 (x, 0) ![(0, u)] = L x u :=
  J.linearFamily_first_at L hx u

/-- The ordered mixed second jet differentiates once in each homogeneous
input.  Its value is the original bilinear family, with no symmetrization
factor and no assumed continuity of the frozen algebraic coefficients. -/
theorem SmoothDirections.bilinearFamily_second_at
    (B : X → R →ₗ[ℝ] Y →ₗ[ℝ] Z) {U : Set ((X × R) × Y)}
    (J : SmoothDirections U (fun z : (X × R) × Y => B z.1.1 z.1.2 z.2))
    {x : X} {r : R} {y : Y} (hxy : ((x, r), y) ∈ U) (dr : R) (u : Y) :
    J.D 2 ((x, r), y) ![((0, dr), 0), ((0, 0), u)] = B x dr u := by
  have hfirst : ∀ z ∈ U,
      J.D 1 z ![((0, 0), u)] = B z.1.1 z.1.2 u := by
    intro z hz
    exact J.linearFamily_first_at (fun xr : X × R => B xr.1 xr.2) hz u
  have heq : (fun z : (X × R) × Y => B z.1.1 z.1.2 u) =ᶠ[𝓝 ((x, r), y)]
      (fun z => J.D 1 z ![((0, 0), u)]) := by
    filter_upwards [J.open_domain.mem_nhds hxy] with z hz
    exact (hfirst z hz).symm
  have hJ := HasProjectiveLineDerivAt.congr_germ
    (J.derivative 1 ((x, r), y) hxy ![((0, 0), u)] ((0, dr), 0)) heq
  have hvalue := HasProjectiveLineDerivAt.unique hJ
    (hasProjectiveLineDerivAt_bilinearFamily_first B x r dr y u)
  exact hvalue

theorem SmoothDirections.bilinearFamily_second
    (B : X → R →ₗ[ℝ] Y →ₗ[ℝ] Z) {U : Set ((X × R) × Y)}
    (J : SmoothDirections U (fun z : (X × R) × Y => B z.1.1 z.1.2 z.2))
    {x : X} (hx : ((x, (0 : R)), (0 : Y)) ∈ U) (dr : R) (u : Y) :
    J.D 2 ((x, 0), 0) ![((0, dr), 0), ((0, 0), u)] = B x dr u :=
  J.bilinearFamily_second_at B hx dr u

end ActualTowers

end ContinuousFlexibility.Statements
