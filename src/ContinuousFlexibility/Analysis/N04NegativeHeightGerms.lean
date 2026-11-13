import ContinuousFlexibility.Analysis.N04NegativeHeightBasicData
import ContinuousFlexibility.Analysis.N04NegativeHeightProductData
import ContinuousFlexibility.Analysis.N04NegativeHeightNeighborhood

/-!
# Finite scalar constructions on one common state neighborhood

A current germ contains the actual reference field and one neighborhood
on which its complete current estimate holds. Each algebraic operation
shrinks that neighborhood finitely, independently of all derivative
orders. The final finite family can therefore be collected before any
auxiliary column is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped Topology ContDiff

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

def N04HeightCurrentGerm (S : PhysicalSpacesData) (T : MaterialData) (cell : ℕ → ℕ)
    (P : ℕ → Prop) (base : ℕ) (ε : ℝ)
    (f : Parameter S → ℕ → PolarPoint → ℝ) (f₀ : ℕ → PolarPoint → ℝ) : Prop :=
  N04HeightReferenceDataOn T cell P f₀ ∧
    (∀ m, P m → EqOn (f 0 m) (f₀ m) unitStrip) ∧
    ∃ b' : ℕ, ∃ ε' : ℝ, base ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell P b' ε' f f₀

namespace N04HeightCurrentGerm

variable {S : PhysicalSpacesData} {T : MaterialData} {D : ReferenceData}
  {cell : ℕ → ℕ} {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f g : Parameter S → ℕ → PolarPoint → ℝ} {f₀ g₀ : ℕ → PolarPoint → ℝ}

theorem of_data (hε : 0 < ε) (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : N04HeightReferenceDataOn T cell P f₀)
    (hz : ∀ m, P m → EqOn (f 0 m) (f₀ m) unitStrip) :
    N04HeightCurrentGerm S T cell P base ε f f₀ :=
  ⟨h₀, hz, base, ε, le_rfl, hε, le_rfl, h⟩

theorem fixed (hε : 0 < ε) (h₀ : N04HeightReferenceDataOn T cell P f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    N04HeightCurrentGerm S T cell P base ε (fun _ => f₀) f₀ :=
  of_data hε (CurrentJetDataOn.height_fixed h₀ hE hH) h₀ (fun _ _ _ _ => rfl)

theorem const (c : ℝ) (hε : 0 < ε)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    N04HeightCurrentGerm S T cell P base ε (fun _ _ _ => c) (fun _ _ => c) := by
  have hB : 0 < |c| + 1 := add_pos_of_nonneg_of_pos (abs_nonneg c) zero_lt_one
  apply fixed hε (n04HeightReferenceDataOn_pieceConstant (fun _ => c) hE ?_) hE hH
  exact ⟨|c| + 1, hB, fun m _ =>
    (le_add_of_nonneg_right zero_le_one).trans
      (le_mul_of_one_le_right hB.le (Real.one_le_rpow (hE m) hB.le))⟩

theorem common
    (hf : N04HeightCurrentGerm S T cell P base ε f f₀)
    (hg : N04HeightCurrentGerm S T cell P base ε g g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    ∃ b' : ℕ, ∃ ε' : ℝ, base ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell P b' ε' f f₀ ∧
        CurrentJetDataOn S T cell P b' ε' g g₀ := by
  obtain ⟨bf, ef, hbf, hef, hefe, hdf⟩ := hf.2.2
  obtain ⟨bg, eg, hbg, heg, hege, hdg⟩ := hg.2.2
  exact ⟨max bf bg, min ef eg, hbf.trans (le_max_left _ _), lt_min hef heg,
    (min_le_left _ _).trans hefe,
    hdf.mono (fun _ hm => hm) (le_max_left _ _) (min_le_left _ _)
      (fun m => zero_le_one.trans (hE m)) hH,
    hdg.mono (fun _ hm => hm) (le_max_right _ _) (min_le_right _ _)
      (fun m => zero_le_one.trans (hE m)) hH⟩

theorem add
    (hf : N04HeightCurrentGerm S T cell P base ε f f₀)
    (hg : N04HeightCurrentGerm S T cell P base ε g g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    N04HeightCurrentGerm S T cell P base ε
      (fun z m q => f z m q + g z m q) (fun m q => f₀ m q + g₀ m q) := by
  obtain ⟨b', ε', hb, he, hele, hdf, hdg⟩ := hf.common hg hE hH
  exact ⟨hf.1.height_add hg.1 hE,
    fun m hm q hq => congrArg₂ (fun x y : ℝ => x + y) (hf.2.1 m hm hq) (hg.2.1 m hm hq),
    b', ε', hb, he, hele, hdf.height_add hdg hf.1 hg.1 hE hH⟩

theorem mul
    (hf : N04HeightCurrentGerm S T cell P base ε f f₀)
    (hg : N04HeightCurrentGerm S T cell P base ε g g₀)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    N04HeightCurrentGerm S T cell P base ε
      (fun z m q => f z m q * g z m q) (fun m q => f₀ m q * g₀ m q) := by
  have hH (m : ℕ) : 0 ≤ T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le
  obtain ⟨b', ε', hb, he, hele, hdf, hdg⟩ := hf.common hg hE hH
  obtain ⟨b'', ε'', hb', he', hele', hprod⟩ :=
    hdf.height_mul hD hT hI he hE hdg hf.1 hg.1 hf.2.1 hg.2.1
  exact ⟨hf.1.height_mul hg.1 hE,
    fun m hm q hq => congrArg₂ (fun x y : ℝ => x * y) (hf.2.1 m hm hq) (hg.2.1 m hm hq),
    b'', ε'', hb.trans hb', he', hele'.trans hele, hprod⟩

theorem angularPartial (hf : N04HeightCurrentGerm S T cell P base ε f f₀) :
    N04HeightCurrentGerm S T cell P base ε
      (fun z m => angularPartial (f z m)) (fun m => angularPartial (f₀ m)) := by
  obtain ⟨b', ε', hb, he, hele, hd⟩ := hf.2.2
  refine ⟨hf.1.height_angularPartial, ?_, b', ε', hb, he, hele,
    hd.height_angularPartial hf.1⟩
  intro m hm q hq
  have heq : f 0 m =ᶠ[𝓝 q] f₀ m := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hq] with y hy
    exact hf.2.1 m hm hy
  exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) heq.fderiv_eq

theorem congr (hf : N04HeightCurrentGerm S T cell P base ε f f₀)
    (hfg : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m → EqOn (f z m) (g z m) unitStrip)
    (hfg₀ : ∀ m, P m → EqOn (f₀ m) (g₀ m) unitStrip) :
    N04HeightCurrentGerm S T cell P base ε g g₀ := by
  obtain ⟨b', ε', hb, he, hele, hd⟩ := hf.2.2
  have hε : 0 < ε := he.trans_le hele
  have hz₀ : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε :=
    ⟨(sectorGrading S base).map_zero'.trans_lt hε,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  exact ⟨hf.1.height_congr hfg₀,
    fun m hm q hq => (hfg 0 hz₀ m hm hq).symm.trans
      ((hf.2.1 m hm hq).trans (hfg₀ m hm hq)),
    b', ε', hb, he, hele, hd.height_congr
      (fun z hz => hfg z (sectorNeighborhood_mono S hb hele hele hz)) hfg₀⟩

end N04HeightCurrentGerm

end ContinuousFlexibility.Analysis
