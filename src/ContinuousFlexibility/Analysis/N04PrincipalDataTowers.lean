import ContinuousFlexibility.Analysis.N04PrincipalWeightedPrefix
import ContinuousFlexibility.Analysis.N04PrincipalTowerValue

/-!
# Passing between the frozen current-data clause and weighted towers

The algebra is carried out on a fixed open parameter domain. The final
neighborhood restriction supplies the unit low-seminorm bound and the
value estimate, without changing the atlas or its reference family.
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

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- The difference tower of current data carries the full sampled height
weight, also at parameter order zero. -/
theorem CurrentJetDataOn.n04Principal_weightedDifference
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (href : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip) :
    N04PrincipalWeightedTowerBounds (parameterGrading S) base
      (fun m : {m : ℕ // P m} => T.E0 (T.sample (cell m.val)))
      (fun m : {m : ℕ // P m} => T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ))
      (fun m => h.n04Principal_differenceRegularity href m.val m.property) := by
  intro k
  have hb := h.2.choose_spec.2 k
  refine ⟨hb.choose, fun s => ⟨(hb.choose_spec s).choose,
    (hb.choose_spec s).choose_spec.1, ?_⟩⟩
  intro m a b hab q hq z hz _ v
  exact (Real.norm_eq_abs _).trans_le
    ((hb.choose_spec s).choose_spec.2 z hz v m.val m.property ⟨q, hq⟩ a b hab)

/-- Restrict a genuine mixed family without changing any of its jets. -/
def n04Principal_mixedRegularity_restrict
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U V : Set X} {Ω : Set PolarPoint} {g : X → PolarPoint → ℝ}
    (R : MixedJetRegularity U Ω g) (hV : IsOpen V) (hVU : V ⊆ U) :
    MixedJetRegularity V Ω g where
  spatial z hz := R.spatial z (hVU hz)
  parameter a b q hq := (R.parameter a b q hq).restrict hV hVU

/-- Weighted estimates on the pieces in `P`, together with a genuine
tower on every piece, give the exact frozen interface on a smaller
neighborhood. This respects the global tower quantifier even outside P. -/
theorem n04Principal_data_of_weightedDifference
    {newBase : ℕ} {δ : ℝ}
    (hbase : base ≤ newBase) (hδ : 0 < δ) (hδε : δ ≤ ε) (hδhalf : δ ≤ 1 / 2)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      ContDiffOn ℝ ∞ (f z m) unitStrip ∧
        ∀ q ∈ unitStrip, f z m (q + (0, Real.pi)) = f z m q)
    (hzero : ∀ m, P m → EqOn (f 0 m) (f₀ m) unitStrip)
    (J : ∀ m (a b : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative a b (fun y => f z m y - f₀ m y) q.val))
    (R : ∀ m : {m : ℕ // P m},
      MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
        (fun z q => f z m.val q - f₀ m.val q))
    (hb : N04PrincipalWeightedTowerBounds (parameterGrading S) newBase
      (fun m : {m : ℕ // P m} => T.E0 (T.sample (cell m.val)))
      (fun m : {m : ℕ // P m} => T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)) R) :
    CurrentJetDataOn S T cell P newBase δ f f₀ := by
  have hsub : sectorNeighborhood S newBase δ δ ⊆ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S hbase hδε hδε
  have hU : IsOpen (sectorNeighborhood S newBase δ δ) :=
    isOpen_sectorNeighborhood S newBase δ δ
  let J' : ∀ m (a b : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S newBase δ δ)
        (fun z => mixedDerivative a b (fun y => f z m y - f₀ m y) q.val) :=
    fun m a b q => (J m a b q).restrict hU hsub
  apply n04Principal_currentData_of_tower hδ hδhalf hE hH
    (fun z hz m hm => hreg z (hsub hz) m hm) hzero J'
  intro k
  have hbk := hb k
  refine ⟨hbk.choose, fun s => ⟨(hbk.choose_spec s).choose,
    (hbk.choose_spec s).choose_spec.1, ?_⟩⟩
  intro z hz v m hm q a b hab
  have hj : (J' m a b q).D k z =
      ((R ⟨m, hm⟩).parameter a b q.val q.property).D k z :=
    (J m a b q).unique ((R ⟨m, hm⟩).parameter a b q.val q.property) k z (hsub hz)
  rw [hj]
  exact (Real.norm_eq_abs _).symm.trans_le
    ((hbk.choose_spec s).choose_spec.2 ⟨m, hm⟩ a b hab q.val q.property z
      (hsub hz) (n04Principal_parameter_low_le_one hδhalf hz) v)

end ContinuousFlexibility.Analysis
