import ContinuousFlexibility.Analysis.N04NegativeHeightReferenceLinear

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

/-- Angular differentiation shifts the actual mixed derivatives of
both the current field and its reference difference by the same order. -/
theorem CurrentJetDataOn.height_angularPartial
    (hf : CurrentJetDataOn S T cell P base ε f f₀)
    (hf₀ : N04HeightReferenceDataOn T cell P f₀) :
    CurrentJetDataOn S T cell P base ε (fun z m => angularPartial (f z m))
      (fun m => angularPartial (f₀ m)) := by
  have hv := hf.2.choose_spec.1
  have hdiff (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => angularPartial (f z m) y - angularPartial (f₀ m) y) q.val =
        mixedDerivative i (j + 1) (fun y => f z m y - f₀ m y) q.val :=
    n04NegativeHeight_mixed_angular_difference (hf.1 z hz m hm).1
      (hf₀.1 m hm).1 i j q.property
  let J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε) (fun z =>
        mixedDerivative i j
          (fun y => angularPartial (f z m) y - angularPartial (f₀ m) y) q.val) :=
    fun m hm i j q => (hf.2.choose m hm i (j + 1) q).congr
      (fun z hz => (hdiff z hz m hm i j q).symm)
  refine ⟨fun z hz m hm =>
    ⟨n04NegativeHeight_angularPartial_smooth (hf.1 z hz m hm).1,
      n04NegativeHeight_angularPartial_periodic (hf.1 z hz m hm).1 (hf.1 z hz m hm).2⟩,
    J, ⟨hv.choose + 1, fun s => ?_⟩, fun k => ?_⟩
  · have hs := hv.choose_spec (s + 1)
    refine ⟨hs.choose, hs.choose_spec.1, fun z hz m hm q i j hij => ?_⟩
    have hb' := n04NegativeHeight_angular_loss_bound
      (fun n => parameterGrading S n z) _ s hv.choose
      (hs.choose_spec.2 z hz m hm q i (j + 1) (by omega))
    exact (congrArg abs (hdiff z hz m hm i j q)).trans_le hb'
  · have ht := hf.2.choose_spec.2 k
    refine ⟨ht.choose + 1, fun s => ?_⟩
    have hs := ht.choose_spec (s + 1)
    refine ⟨hs.choose, hs.choose_spec.1, fun z hz v m hm q i j hij => ?_⟩
    exact n04NegativeHeight_angular_loss_bound
      (fun n => oneHighVariationWeight (parameterGrading S) base n z v) _ s ht.choose
      (hs.choose_spec.2 z hz v m hm q i (j + 1) (by omega))

end ContinuousFlexibility.Analysis
