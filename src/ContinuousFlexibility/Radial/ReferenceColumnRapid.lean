module

public import ContinuousFlexibility.Radial.ReferenceColumnSmooth
public import ContinuousFlexibility.Radial.ReferenceRadialJetBootstrap

/-!
# Rapid attenuation of every actual border-column derivative

The true column is the cutoff commutator of the homogeneous mode-two
solution. Its coefficients are built from actual smooth cutoff jets and
the quantitative profile coefficients. The finite-expression derivative
theorem therefore propagates positive attenuation to every column jet.
Only rapid membership of phi and its first derivative is used here; the
separate inverse comparison proves these two analytic inputs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

def referenceColumnExpr (D : ReferenceData) (hχ : ContDiff ℝ ∞ D.chi) :
    ReferenceSolutionExpr :=
  .add
    (.scale (.mul (.profile 0) (.smooth ⟨D.chi, hχ⟩ 1)) .normal)
    (.scale (.mul (.scalar (-4))
      (.mul (.profile 0) (.mul (.smooth ⟨D.chi, hχ⟩ 1) (.reciprocalRadius 0)))) .solution)

theorem referenceColumn_eqOn_expr {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hχ : ContDiff ℝ ∞ D.chi)
    (hφ : ∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0) :
    EqOn (referenceColumn D)
      ((referenceColumnExpr D hχ).eval D D.phi (fun _ => 0)) (radialCore D) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hφc : ContDiff ℝ ∞ D.phi := hgeom.2.2.2.1.1
  have hφ'c : ContDiff ℝ ∞ (deriv D.phi) := (contDiff_infty_iff_deriv.mp hφc).2
  intro r hr
  have hw := (hgeom.2.2.1.1.differentiable (by simp) r).hasDerivAt
  have hchi := (hχ.differentiable (by simp) r).hasDerivAt
  have hphip := (hφ'c.differentiable (by simp) r).hasDerivAt
  have hA : deriv (fun t => D.w t * D.chi t) r =
      deriv D.w r * D.chi r + D.w r * deriv D.chi r := (hw.mul hchi).deriv
  have hF : deriv (fun t => (D.w t * D.chi t) * deriv D.phi t) r =
      (deriv D.w r * D.chi r + D.w r * deriv D.chi r) * deriv D.phi r +
        (D.w r * D.chi r) * deriv (deriv D.phi) r := ((hw.mul hchi).mul hphip).deriv
  have hF0 : deriv (fun t => D.w t * deriv D.phi t) r =
      deriv D.w r * deriv D.phi r + D.w r * deriv (deriv D.phi) r :=
    (hw.mul hphip).deriv
  calc
    referenceColumn D r =
        D.chi r * radialJacobi 4 D.w D.phi r +
          (D.w r * deriv D.chi r) * deriv D.phi r +
          (-4 * (D.w r * (deriv D.chi r * r⁻¹))) * D.phi r := by
      unfold referenceColumn radialJacobi
      rw [hF, hA, hF0]
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [hφ r hr]
      simp only [referenceColumnExpr, ReferenceSolutionExpr.eval,
        ReferenceCoefficientExpr.eval, iteratedDeriv_zero, iteratedDeriv_one, mul_zero, zero_add]

theorem referenceColumn_jets_rapid {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hφ : ∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0)
    (hφW : ReferenceRapid D D.phi) (hφ'W : ReferenceRapid D (deriv D.phi))
    (n : ℕ) : ReferenceRapid D (iteratedDeriv n (referenceColumn D)) := by
  have hz (s : ℕ) : iteratedDeriv s (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    induction s with
    | zero => rfl
    | succ s ih =>
      rw [iteratedDeriv_succ, ih]
      funext r
      exact deriv_const r 0
  have hfW (s : ℕ) : ReferenceRapid D (iteratedDeriv s (fun _ : ℝ => (0 : ℝ))) := by
    rw [hz s]
    exact ReferenceRapid.zero D
  have he := referenceColumn_eqOn_expr hD hborder.1 hφ
  apply ((referenceColumnExpr D hborder.1).jets_rapid hD
    hD.choose_spec.1.2.2.2.1.1.contDiffOn contDiffOn_const hφ hφW hφ'W hfW n).of_eqOn
  exact (he.iteratedDeriv_of_isOpen isOpen_Ioo n).symm

end ContinuousFlexibility.Radial
