import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData
import ContinuousFlexibility.Analysis.N04RealizationFixedSpatialProduct
import ContinuousFlexibility.Analysis.N07aParameterGrading

/-!
# Regularity retained by the current jet interface

The interface stores the genuine parameter tower of a difference. Adding
the fixed reference jets recovers the tower of the current family itself.
The selected tower is immaterial: uniqueness transports every estimate to
any other genuine tower of the same scalar jet.
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

/-- The difference has the actual mixed spatial/parameter tower. -/
def CurrentJetDataOn.n04Principal_differenceRegularity
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (href : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (m : ℕ) (hm : P m) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z q => f z m q - f₀ m q) where
  spatial z hz := (h.1 z hz m hm).1.sub (href m hm)
  parameter i j q hq := h.2.choose m hm i j ⟨q, hq⟩

/-- Recover the full current field without introducing a new family. -/
def CurrentJetDataOn.n04Principal_familyRegularity
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (href : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (m : ℕ) (hm : P m) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip (fun z => f z m) := by
  have hU := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  let R := (h.n04Principal_differenceRegularity href m hm).add
    (n04Realization_mixedJetRegularity_fixedSpatial hU (href m hm)) hU hΩ
  exact R.congr hΩ (fun z hz => (h.1 z hz m hm).1)
    (fun z hz q hq => sub_add_cancel (f z m q) (f₀ m q))

end ContinuousFlexibility.Analysis
