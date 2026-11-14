module

public import ContinuousFlexibility.Analysis.N04NegativeHeightReferenceLinear

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

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

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f g : Parameter S → ℕ → PolarPoint → ℝ} {f₀ g₀ : ℕ → PolarPoint → ℝ}

/-- Addition of actual reference differences preserves one common
height factor and one high state weight on the selected pieces. -/
theorem CurrentJetDataOn.height_add
    (hf : CurrentJetDataOn S T cell P base ε f f₀)
    (hg : CurrentJetDataOn S T cell P base ε g g₀)
    (hf₀ : N04HeightReferenceDataOn T cell P f₀)
    (hg₀ : N04HeightReferenceDataOn T cell P g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell P base ε (fun z m q => f z m q + g z m q)
      (fun m q => f₀ m q + g₀ m q) := by
  have hfv := hf.2.choose_spec.1
  have hgv := hg.2.choose_spec.1
  have hmono : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  have he (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => (f z m y + g z m y) - (f₀ m y + g₀ m y)) q.val =
        mixedDerivative i j (fun y => f z m y - f₀ m y) q.val +
          mixedDerivative i j (fun y => g z m y - g₀ m y) q.val :=
    n04NegativeHeight_mixed_add_difference (hf.1 z hz m hm).1 (hg.1 z hz m hm).1
      (hf₀.1 m hm).1 (hg₀.1 m hm).1 i j q.property
  let J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε) (fun z =>
        mixedDerivative i j
          (fun y => (f z m y + g z m y) - (f₀ m y + g₀ m y)) q.val) :=
    fun m hm i j q =>
      (smoothDirectionsAdd (hf.2.choose m hm i j q) (hg.2.choose m hm i j q)).congr
        (fun z hz => (he z hz m hm i j q).symm)
  have hJ (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip) (k : ℕ)
      (z : Parameter S) (v : Fin k → Parameter S) :
      (J m hm i j q).D k z v = (hf.2.choose m hm i j q).D k z v +
        (hg.2.choose m hm i j q).D k z v := rfl
  refine ⟨fun z hz m hm => ⟨(hf.1 z hz m hm).1.add (hg.1 z hz m hm).1,
    fun q hq => congrArg₂ (fun x y : ℝ => x + y)
      ((hf.1 z hz m hm).2 q hq) ((hg.1 z hz m hm).2 q hq)⟩,
    J, ⟨max hfv.choose hgv.choose, fun s => ?_⟩, fun k => ?_⟩
  · have hfs := hfv.choose_spec s
    have hgs := hgv.choose_spec s
    refine ⟨hfs.choose + hgs.choose, add_pos hfs.choose_spec.1 hgs.choose_spec.1,
      fun z hz m hm q i j hij => ?_⟩
    have hb := n04NegativeHeight_add_cost hfs.choose_spec.1.le hgs.choose_spec.1.le (hE m)
      (Real.rpow_nonneg (hH m) _) (apply_nonneg _ _) (apply_nonneg _ _)
      (hmono (Nat.add_le_add_left (le_max_left _ _) s) z)
      (hmono (Nat.add_le_add_left (le_max_right _ _) s) z)
      (hfs.choose_spec.2 z hz m hm q i j hij) (hgs.choose_spec.2 z hz m hm q i j hij)
    exact (congrArg abs (he z hz m hm i j q)).trans_le hb
  · have hft := hf.2.choose_spec.2 k
    have hgt := hg.2.choose_spec.2 k
    refine ⟨max hft.choose hgt.choose, fun s => ?_⟩
    have hfs := hft.choose_spec s
    have hgs := hgt.choose_spec s
    refine ⟨hfs.choose + hgs.choose, add_pos hfs.choose_spec.1 hgs.choose_spec.1,
      fun z hz v m hm q i j hij => ?_⟩
    have hb := n04NegativeHeight_add_cost hfs.choose_spec.1.le hgs.choose_spec.1.le (hE m)
      (Real.rpow_nonneg (hH m) _)
      (oneHighVariationWeight_nonneg _ _ _ _ _) (oneHighVariationWeight_nonneg _ _ _ _ _)
      (oneHighVariationWeight_mono hmono le_rfl
        (Nat.add_le_add_left (le_max_left _ _) s) z v)
      (oneHighVariationWeight_mono hmono le_rfl
        (Nat.add_le_add_left (le_max_right _ _) s) z v)
      (hfs.choose_spec.2 z hz v m hm q i j hij) (hgs.choose_spec.2 z hz v m hm q i j hij)
    exact (congrArg abs (hJ m hm i j q k z v)).trans_le hb

end ContinuousFlexibility.Analysis
