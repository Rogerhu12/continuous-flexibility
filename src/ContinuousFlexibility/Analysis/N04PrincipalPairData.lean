import ContinuousFlexibility.Analysis.N04PrincipalPairAlgebra
import ContinuousFlexibility.Analysis.N04PrincipalFullTower

/-!
# Primitive paired bounds from the frozen interface

The spatial reference hypotheses are required only on the selected
pieces. This allows the positive physical coefficient formulas to use
their own reference bounds without imposing a negative-piece formula.
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

theorem CurrentJetDataOn.n04Principal_pairBounds
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (href : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (hrefb : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, P m →
      ∀ (q : unitStrip) (a b : ℕ), a + b ≤ s →
        |mixedDerivative a b (f₀ m) q.val| ≤ B * T.E0 (T.sample (cell m)) ^ B)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    {RH : ℝ} (hRH : 0 ≤ RH)
    (hheight : ∀ m, T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ RH) :
    N04PrincipalPairBounds (parameterGrading S)
      (fun m : {m : ℕ // P m} => T.E0 (T.sample (cell m.val)))
      (fun m : {m : ℕ // P m} => T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ))
      (U := sectorNeighborhood S base ε ε) (Ω := unitStrip)
      (fun m z => f z m.val) (fun m => f₀ m.val) := by
  let RR (m : {m : ℕ // P m}) :
      MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
        (fun _ => f₀ m.val) :=
    n04Realization_mixedJetRegularity_fixedSpatial
      (isOpen_sectorNeighborhood S base ε ε) (href m.val m.property)
  refine ⟨base, (fun m => h.n04Principal_familyRegularity href m.val m.property), RR,
    (fun m => h.n04Principal_differenceRegularity href m.val m.property),
    h.n04Principal_fullWeighted href hrefb hE hH hRH hheight, ?_,
    h.n04Principal_weightedDifference href⟩
  apply n04Principal_weightedTower_fixedSpatial (parameterGrading S) base
    (fun m : {m : ℕ // P m} => T.E0 (T.sample (cell m.val)))
    (fun m => hE m.val) (fun m => f₀ m.val) RR
  intro s
  refine ⟨(hrefb s).choose, (hrefb s).choose, ?_⟩
  intro m a b hab q hq
  exact (Real.norm_eq_abs _).trans_le
    ((hrefb s).choose_spec.2 m.val m.property ⟨q, hq⟩ a b hab)

end ContinuousFlexibility.Analysis
