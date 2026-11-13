import ContinuousFlexibility.Analysis.N04PrincipalPositivePrincipalPairs
import ContinuousFlexibility.Analysis.N04PrincipalPositivePotential

/-!
# The positive potential preserves the principal pairs

The supplied principal pairs and reciprocal pulled-height pair form the
two genuine fluxes. One further coordinate derivative and multiplication
by the pulled height give the stored potential and its exact reference.
No potential estimate or potential tower is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
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

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04PrincipalPositive_potential_pairBounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (hH : G.n04PrincipalPositivePair η b ε (G.pulledHeight η) (G.pulledHeightRef η))
    (hV : G.n04PrincipalPositivePair η b ε
      (fun z m q => (G.pulledHeight η z m q)⁻¹) (fun m q => (G.pulledHeightRef η m q)⁻¹))
    (hP : ∀ v : Fin 3, G.n04PrincipalPositivePair η b ε
      (G.atomFamily η (n07aCubicPrincipalAtom v)) (G.atomRef η (n07aCubicPrincipalAtom v))) :
    G.n04PrincipalPositivePair η b ε (G.atomFamily η .potential) (G.atomRef η .potential) := by
  have hp := n07aParameterGrading_monotone (G.S η)
  have hI := G.n04PrincipalPositive_parameter_interpolation η
  have hU := isOpen_sectorNeighborhood (G.S η) b ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hz0 := G.n04PrincipalPositive_sector_zero η b h.2.1
  have hUne : (sectorNeighborhood (G.S η) b ε ε).Nonempty := ⟨0, hz0⟩
  have hE (m : {m : ℕ // G.Pos η m}) :
      1 ≤ G.W.U.E0 (G.W.U.sample ((G.V η).cell m.val)) := (G.cost_nonneg η).2.2 m.val
  have hW (m : {m : ℕ // G.Pos η m}) :
      0 < G.W.U.H (G.W.U.sample ((G.V η).cell m.val)) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (G.n04PrincipalPositive_sample_height_pos η m.val) _
  have ha := hP 0
  have hb := hP 1
  have hc := hP 2
  have hVr := hV.firstMixed hΩ hUne true
  have hVt := hV.firstMixed hΩ hUne false
  have hR := (ha.mul hVr hp hI hU hΩ hE hW).add
    (hb.mul hVt hp hI hU hΩ hE hW) hp hU hΩ hE (fun m => (hW m).le)
  have hT := (hb.mul hVr hp hI hU hΩ hE hW).add
    (hc.mul hVt hp hI hU hΩ hE hW) hp hU hΩ hE (fun m => (hW m).le)
  have hdiv := (hR.firstMixed hΩ hUne true).add (hT.firstMixed hΩ hUne false)
    hp hU hΩ hE (fun m => (hW m).le)
  have hpot := hH.mul hdiv hp hI hU hΩ hE hW
  apply hpot.congr hΩ
  · intro m z hz q hq
    exact (G.n04PrincipalPositive_potential_unit_formula h η hz m.property
      (ha.spatial m z hz) (hb.spatial m z hz) (hc.spatial m z hz) hq).symm
  · intro m q hq
    have hzero := G.n04PrincipalPositive_potential_unit_formula h η hz0 m.property
      (ha.spatial m 0 hz0) (hb.spatial m 0 hz0) (hc.spatial m 0 hz0) hq
    simpa only [atomFamily, atomRef, pulledHeight, pulledHeightRef,
      heightField, G.n04PrincipalPositive_lift_zero η, Bool.false_eq_true, ↓reduceIte]
      using hzero.symm

end N04RealizationGauge

end ContinuousFlexibility.Analysis
