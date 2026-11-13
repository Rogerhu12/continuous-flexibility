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

/-- Equal selected fields have the same genuine difference towers. -/
theorem CurrentJetDataOn.height_congr
    (hf : CurrentJetDataOn S T cell P base ε f f₀)
    (hfg : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m → EqOn (f z m) (g z m) unitStrip)
    (hfg₀ : ∀ m, P m → EqOn (f₀ m) (g₀ m) unitStrip) :
    CurrentJetDataOn S T cell P base ε g g₀ := by
  have hv := hf.2.choose_spec.1
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have he (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (hm : P m) (i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => f z m y - f₀ m y) q.val =
        mixedDerivative i j (fun y => g z m y - g₀ m y) q.val :=
    n07a_mixedDerivative_eqOn hU
      (fun y hy => congrArg₂ (fun a b : ℝ => a - b) (hfg z hz m hm hy) (hfg₀ m hm hy))
      i j q.property
  let J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (fun y => g z m y - g₀ m y) q.val) :=
    fun m hm i j q => (hf.2.choose m hm i j q).congr (fun z hz => he z hz m hm i j q)
  refine ⟨fun z hz m hm => ⟨(hf.1 z hz m hm).1.congr
    (fun q hq => (hfg z hz m hm hq).symm), ?_⟩,
    J, ⟨hv.choose, fun s => ?_⟩, hf.2.choose_spec.2⟩
  · intro q hq
    have hs : q + (0, Real.pi) ∈ unitStrip :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
    exact (hfg z hz m hm hs).symm.trans
      (((hf.1 z hz m hm).2 q hq).trans (hfg z hz m hm hq))
  · have hs := hv.choose_spec s
    exact ⟨hs.choose, hs.choose_spec.1, fun z hz m hm q i j hij =>
      (congrArg abs (he z hz m hm i j q).symm).trans_le
        (hs.choose_spec.2 z hz m hm q i j hij)⟩

/-- A state-independent family has zero difference at every jet order. -/
theorem CurrentJetDataOn.height_fixed
    (hf₀ : N04HeightReferenceDataOn T cell P f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell P base ε (fun _ => f₀) f₀ := by
  have hU : IsOpen (sectorNeighborhood S base ε ε) := isOpen_sectorNeighborhood S base ε ε
  let J : ∀ m, P m → ∀ (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun (_z : Parameter S) => mixedDerivative i j (fun y => f₀ m y - f₀ m y) q.val) :=
    fun m _hm i j q => (smoothDirections_constant hU (0 : ℝ)).congr
      (fun (_z : Parameter S) _ => (n04NegativeHeight_mixed_self_sub_zero (f₀ m) i j q.val).symm)
  have hc (m : ℕ) : 0 ≤ (1 : ℝ) * T.E0 (T.sample (cell m)) ^ (1 : ℝ) *
      T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg zero_le_one
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (Real.rpow_nonneg (hH m) _)
  refine ⟨fun _ _ m hm => hf₀.1 m hm, J,
    ⟨0, fun _ => ⟨1, zero_lt_one, fun z _ m _ q i j _ => ?_⟩⟩,
    fun k => ⟨0, fun s => ⟨1, zero_lt_one, fun z hz v m hm q i j _ => ?_⟩⟩⟩
  · exact n04NegativeHeight_zero_bound (n04NegativeHeight_mixed_self_sub_zero (f₀ m) i j q.val)
      (mul_nonneg (hc m) (apply_nonneg _ z))
  · exact n04NegativeHeight_zero_bound (n04NegativeHeight_zeroTower_apply hU k z hz v)
      (mul_nonneg (hc m) (oneHighVariationWeight_nonneg _ _ _ _ _))

end ContinuousFlexibility.Analysis
