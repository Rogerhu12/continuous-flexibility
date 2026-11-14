import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData
import ContinuousFlexibility.Analysis.N04PrincipalDividedCore
import ContinuousFlexibility.Analysis.N07aParameterGrading

/-!
# Current jet data through the actual cubic quotient

The positive canonical intervals of the reference-gauged atlas are `(0,1)`.
The numerator is the actual principal difference. Its three zero jets at
each endpoint, supplied by an actual smooth representative, transfer the
current value and parameter estimates to the stored quotient with six
additional radial orders. Pieces on which the divided atom is zero are
handled in the same family, so the tower is defined on every piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

/-- Cubic division preserves the complete current-data interface. The
only extra input is the genuine endpoint representative of the numerator;
all parameter towers and their estimates come from the principal data. -/
theorem n04PrincipalDivided_currentData
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ} (P : ℕ → Prop)
    {f g : Parameter S → ℕ → PolarPoint → ℝ} {f₀ g₀ : ℕ → PolarPoint → ℝ}
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (href : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip ∧
      ∀ q ∈ unitStrip, f₀ m (q + (0, Real.pi)) = f₀ m q)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hrep : ∀ m, P m → ∀ z ∈ sectorNeighborhood S base ε ε,
      ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
        EqOn F (fun q => f z m q - f₀ m q) unitStrip ∧
        ∀ c : Bool, ∀ θ i, i ≤ 2 →
          iteratedDeriv i (fun t : ℝ => F (t, θ)) (if c then 1 else 0) = 0)
    (hfactor : ∀ m, P m → ∀ z ∈ sectorNeighborhood S base ε ε, ∀ q ∈ unitStrip,
      f z m q - f₀ m q = (q.1 * (1 - q.1)) ^ 3 * g z m q)
    (hzero : ∀ m, ¬ P m → ∀ z ∈ sectorNeighborhood S base ε ε,
      EqOn (g z m) (fun _ => 0) unitStrip)
    (hrefzero : ∀ m, g₀ m = fun _ => 0) :
    CurrentJetDataOn S T cell (fun _ => True) base ε g g₀ := by
  classical
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  have hzero₀ : g₀ = fun _ _ => (0 : ℝ) := funext hrefzero
  subst g₀
  exact n04PrincipalDivided_coreData
    (parameterGrading S) (n07aParameterGrading_withSeminorms S)
    (n07aParameterGrading_monotone S) (isOpen_sectorNeighborhood S base ε ε)
    (fun m => T.E0 (T.sample (cell m)))
    (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) P base h href hE
    (fun m => Real.rpow_nonneg (hH m) _) hrep hfactor hzero

end ContinuousFlexibility.Analysis
