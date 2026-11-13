import ContinuousFlexibility.Analysis.N04PositiveGeometryAtomPairInputs
import ContinuousFlexibility.Analysis.N04PositiveGeometryChartJacobianFormula

/-!
# The actual forward Jacobian from the two chart atoms

The determinant polynomial is evaluated at the fixed physical unit
point. The positive range certificate identifies its sign, and the fixed
width factor carries the original material sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

private theorem jacobianFormula_congr
    {j j₀ r r₀ t t₀ : PolarPoint → ℝ} (hj : j₀ = j) (hr : r₀ = r)
    (ht : t₀ = t) (c : ℝ) (q : PolarPoint)
    (h : j q = c * (mixedDerivative 1 0 r q * (1 + mixedDerivative 0 1 t q) -
      mixedDerivative 1 0 t q * mixedDerivative 0 1 r q)) :
    j₀ q = c * (mixedDerivative 1 0 r₀ q * (1 + mixedDerivative 0 1 t₀ q) -
      mixedDerivative 1 0 t₀ q * mixedDerivative 0 1 r₀ q) := by
  rw [hj, hr, ht]
  exact h

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem positiveGeometry_jacobian_atom_formula {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : Parameter (G.S η)} (hz : z ∈ sectorNeighborhood (G.S η) base ε ε)
    {m : ℕ} (hm : G.Pos η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    G.atomFamily η .jacobian z m q =
      (((G.V η).right m - (G.V η).left m) /
        ((G.V η).physicalRight m - (G.V η).physicalLeft m)) *
        (mixedDerivative 1 0 (G.atomFamily η .chartRadial z m) q *
            (1 + mixedDerivative 0 1 (G.atomFamily η .chartAngleDefect z m) q) -
          mixedDerivative 1 0 (G.atomFamily η .chartAngleDefect z m) q *
            mixedDerivative 0 1 (G.atomFamily η .chartRadial z m) q) := by
  have hg := G.positiveRangeGeometry η hA z hz m hm
  have hp := ((G.positiveGeometry_width_values hA).choose_spec.2 η m hm).1
  have hend := G.n04PrincipalDivided_positive_endpoints η hm
  have hc : (G.V η).right m - (G.V η).left m ≠ 0 := by
    rw [hend.1, hend.2]
    norm_num
  have hr := (G.positiveAtom_regular η hA .chartRadial trivial z hz m hm).1
  have ht := (G.positiveAtom_regular η hA .chartAngleDefect trivial z hz m hm).1
  change |planeJacobian ((G.V η).chart (G.lift η z) m) (physicalUnitPoint (G.V η) m q)| = _
  rw [abs_of_pos (hg.jacobian_positive _)]
  exact n04PositiveGeometry_forwardJacobian_unit_mixed (G.lift η z) m
    hp.ne' hc hr ht hq (hg.chart_smooth.differentiable (by simp) _)

theorem positiveGeometry_jacobian_reference_formula {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {m : ℕ} (hm : G.Pos η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    G.atomRef η .jacobian m q =
      (((G.V η).right m - (G.V η).left m) /
        ((G.V η).physicalRight m - (G.V η).physicalLeft m)) *
        (mixedDerivative 1 0 (G.atomRef η .chartRadial m) q *
            (1 + mixedDerivative 0 1 (G.atomRef η .chartAngleDefect m) q) -
          mixedDerivative 1 0 (G.atomRef η .chartAngleDefect m) q *
            mixedDerivative 0 1 (G.atomRef η .chartRadial m) q) := by
  exact jacobianFormula_congr (G.atomRef_eq_zero η .jacobian m)
    (G.atomRef_eq_zero η .chartRadial m) (G.atomRef_eq_zero η .chartAngleDefect m) _ q
    (G.positiveGeometry_jacobian_atom_formula hA η
      (G.n04PrincipalPositive_sector_zero η base hA.2.1) hm hq)

theorem positiveGeometry_jacobian_pair {base : ℕ} {ε : ℝ}
    (hA : G.Admissible base ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (hR : G.n04PrincipalPositivePair η base ε
      (G.atomFamily η .chartRadial) (G.atomRef η .chartRadial))
    (hT : G.n04PrincipalPositivePair η base ε
      (G.atomFamily η .chartAngleDefect) (G.atomRef η .chartAngleDefect)) :
    G.n04PrincipalPositivePair η base ε
      (G.atomFamily η .jacobian) (G.atomRef η .jacobian) := by
  have hp := n07aParameterGrading_monotone (G.S η)
  have hI := G.n04PrincipalPositive_parameter_interpolation η
  have hU := isOpen_sectorNeighborhood (G.S η) base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hUne : (sectorNeighborhood (G.S η) base ε ε).Nonempty :=
    ⟨0, G.n04PrincipalPositive_sector_zero η base hA.2.1⟩
  have hE (m : {m : ℕ // G.Pos η m}) :
      1 ≤ G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)) := (G.cost_nonneg η).2.2 m.val
  have hW (m : {m : ℕ // G.Pos η m}) :
      0 < G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (G.n04PrincipalPositive_sample_height_pos η m.val) _
  have h1 := G.n04PrincipalPositive_const_pairBounds (b := base) (ε := ε) η 1
  have hRr := hR.firstMixed hΩ hUne true
  have hRt := hR.firstMixed hΩ hUne false
  have hTr := hT.firstMixed hΩ hUne true
  have hTt := h1.add (hT.firstMixed hΩ hUne false) hp hU hΩ hE (fun m => (hW m).le)
  have hdet := (hRr.mul hTt hp hI hU hΩ hE hW).sub
    (hTr.mul hRt hp hI hU hΩ hE hW) hp hU hΩ hE (fun m => (hW m).le)
  have hJ := (G.positiveGeometry_widthRatio_pair hA η).mul hdet hp hI hU hΩ hE hW
  exact hJ.congr hΩ
    (fun m z hz q hq => (G.positiveGeometry_jacobian_atom_formula hA η hz m.property hq).symm)
    (fun m q hq => (G.positiveGeometry_jacobian_reference_formula hA η m.property hq).symm)

end N04RealizationGauge

end ContinuousFlexibility.Analysis
