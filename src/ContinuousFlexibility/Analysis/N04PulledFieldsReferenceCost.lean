module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
public import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# Recovering raw geometry costs from the same reference certificate

The difference estimate in `CurrentJetDataOn` and the estimate for the
actual reference have different roles.  Their sum bounds the raw spatial
jets without changing the family, its sample, or its neighborhood.  This
is the reference input required before moving-point composition.

This module does not assert that the qualitative reference-family
predicate supplies `ReferenceJets`.
-/

@[expose] public section

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

private theorem n04PulledFieldsReferenceCost_mono {A B E : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hE : 1 ≤ E) : A * E ^ A ≤ B * E ^ B :=
  mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hE hAB)
    (Real.rpow_nonneg (zero_le_one.trans hE) A) (hA.le.trans hAB)

/-- The raw bound uses both the difference and the actual reference.
Its spatial loss is exactly the loss of the difference estimate. -/
theorem n04PulledFields_currentData_rawSpatial
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hdata : CurrentJetDataOn S T cell P base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, P m → ∀ (q : unitStrip) (i j : ℕ),
      i + j ≤ s → |mixedDerivative i j (f₀ m) q.val| ≤
        B * T.E0 (T.sample (cell m)) ^ B) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
        |mixedDerivative i j (f z m) q.val| ≤
          B * T.E0 (T.sample (cell m)) ^ B *
            (1 + T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
              parameterGrading S (s + loss) z) := by
  have hv := hdata.2.choose_spec.1
  refine ⟨hv.choose, fun s => ?_⟩
  have hd := hv.choose_spec s
  have hr := href s
  let B : ℝ := max hd.choose hr.choose
  have hB : 0 < B := lt_max_of_lt_left hd.choose_spec.1
  refine ⟨B, hB, fun z hz m hm q i j hij => ?_⟩
  have hdiff := hd.choose_spec.2 z hz m hm q i j hij
  have hreference := hr.choose_spec.2 m hm q i j hij
  have hdB : hd.choose * T.E0 (T.sample (cell m)) ^ hd.choose ≤
      B * T.E0 (T.sample (cell m)) ^ B :=
    n04PulledFieldsReferenceCost_mono hd.choose_spec.1 (le_max_left _ _) (hE m)
  have hrB : hr.choose * T.E0 (T.sample (cell m)) ^ hr.choose ≤
      B * T.E0 (T.sample (cell m)) ^ B :=
    n04PulledFieldsReferenceCost_mono hr.choose_spec.1 (le_max_right _ _) (hE m)
  have hheight : 0 ≤ T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hH m) _
  have hweight : 0 ≤ parameterGrading S (s + hv.choose) z := apply_nonneg _ _
  have hdB' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdB hheight) hweight
  have hsub := mixedDerivative_sub_of_contDiffOn
    (isOpen_Ioo.prod isOpen_univ) (hdata.1 z hz m hm).1 (hreg m hm) i j q.property
  calc
    |mixedDerivative i j (f z m) q.val| =
        |mixedDerivative i j (fun y => f z m y - f₀ m y) q.val +
          mixedDerivative i j (f₀ m) q.val| := by rw [hsub, sub_add_cancel]
    _ ≤ |mixedDerivative i j (fun y => f z m y - f₀ m y) q.val| +
        |mixedDerivative i j (f₀ m) q.val| := abs_add_le _ _
    _ ≤ B * T.E0 (T.sample (cell m)) ^ B *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            parameterGrading S (s + hv.choose) z +
        B * T.E0 (T.sample (cell m)) ^ B :=
      add_le_add (hdiff.trans hdB') (hreference.trans hrB)
    _ = _ := by ring

/-- For the gauge's geometry atoms the missing raw reference estimate is
exactly the same-atlas `ReferenceJets` certificate already used by the
parent current obligation. -/
theorem n04PulledFields_geometry_rawSpatial
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    (hgeo : G.GeometryData η P base ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (a : Atom) (ha : atomIsGeometry a) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood (G.S η) base ε ε, ∀ m, P m →
      ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
        |mixedDerivative i j (G.atomFamily η a z m) q.val| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
            (1 + G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
              parameterGrading (G.S η) (s + loss) z) := by
  apply n04PulledFields_currentData_rawSpatial (hgeo.1 a ha)
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1
    (fun m _ => (href.1 m a).1)
  intro s
  have h := href.2 s
  exact ⟨h.choose, h.choose_spec.1, fun m _ q i j hij =>
    h.choose_spec.2 m a q.val q.property i j hij⟩

end ContinuousFlexibility.Analysis
