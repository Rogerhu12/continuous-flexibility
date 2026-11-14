module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.CylinderSobolev

/-!
# The smooth physical divergence operator at a transmission interface

The operator is the actual symmetric divergence operator in the statement
layer. Equality of the value trace gives equality of the angular derivative;
the conormal trace and a nonzero normal coefficient then determine the first
radial derivative. Higher derivatives are handled by the equation.

Source: the readable manuscript, §7, lines 1725–1755.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Analysis
open scoped ContDiff

theorem contDiff_divergenceOperator {L : SymmetricCoefficients} {u : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (divergenceOperator L u) := by
  have hur := contDiff_cylinder_radialPartial hu
  have hut := contDiff_cylinder_angularPartial hu
  exact (contDiff_cylinder_radialPartial ((ha.mul hur).add (hb.mul hut))).add
    (contDiff_cylinder_angularPartial ((hb.mul hur).add (hc.mul hut)))

/-- Product-rule expansion with the second normal derivative isolated. -/
theorem divergenceOperator_expansion {L : SymmetricCoefficients} {u : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hu : ContDiff ℝ ∞ u) (p : PolarPoint) :
    divergenceOperator L u p =
      L.a p * radialPartial (radialPartial u) p +
      2 * L.b p * angularPartial (radialPartial u) p +
      L.c p * angularPartial (angularPartial u) p +
      (radialPartial L.a p + angularPartial L.b p) * radialPartial u p +
      (radialPartial L.b p + angularPartial L.c p) * angularPartial u p := by
  exact divergence_expansion_of_coefficients
    (ha.differentiable (by simp) p) (hb.differentiable (by simp) p)
    (hc.differentiable (by simp) p) (hu.contDiffAt.of_le (by simp))

/-- The value and conormal traces fix the first normal derivative. -/
theorem radialPartial_eq_of_value_conormal {r0 : ℝ} {L : SymmetricCoefficients}
    {u v : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (ha : ∀ θ, L.a (r0, θ) ≠ 0)
    (hvalue : ∀ θ, u (r0, θ) = v (r0, θ))
    (hconormal : ∀ θ,
      L.a (r0, θ) * radialPartial u (r0, θ) +
          L.b (r0, θ) * angularPartial u (r0, θ) =
        L.a (r0, θ) * radialPartial v (r0, θ) +
          L.b (r0, θ) * angularPartial v (r0, θ)) :
    ∀ θ, radialPartial u (r0, θ) = radialPartial v (r0, θ) := by
  have he : (fun θ => u (r0, θ)) = (fun θ => v (r0, θ)) := funext hvalue
  intro θ
  have ht : angularPartial u (r0, θ) = angularPartial v (r0, θ) := by
    calc
      angularPartial u (r0, θ) = deriv (fun t => u (r0, t)) θ :=
        (deriv_cylinder_angular_slice (hu.differentiable (by simp)) r0 θ).symm
      _ = deriv (fun t => v (r0, t)) θ := congrArg (fun g : ℝ → ℝ => deriv g θ) he
      _ = angularPartial v (r0, θ) :=
        deriv_cylinder_angular_slice (hv.differentiable (by simp)) r0 θ
  have hflux := hconormal θ
  rw [ht] at hflux
  exact mul_left_cancel₀ (ha θ) (add_right_cancel hflux)

end ContinuousFlexibility.Statements
