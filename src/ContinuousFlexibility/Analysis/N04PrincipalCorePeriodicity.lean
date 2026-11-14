module

public import ContinuousFlexibility.Analysis.N04PrincipalCoreData
public import ContinuousFlexibility.Analysis.N04PrincipalPositivePeriodicity
public import ContinuousFlexibility.Analysis.N04PrincipalNegativePeriodicity

/-!
# Periodicity of the five principal fields on the whole atlas

The positive coefficient and flux formulas preserve the angular period.
On negative pieces the four principal coefficients are stationary, and
the pulled-height potential formula preserves the same period. The
paired bounds supply exactly the spatial regularity needed by the
positive flux identity.
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

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04Principal_core_periodic {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hg : G.GeometryData η (fun _ => True) b ε) (hf : G.FieldData η b ε)
    (hpair : ∀ i : Fin 5, G.n04PrincipalPair η b ε
      (G.atomFamily η (n04PrincipalCoreAtom i)) (G.atomRef η (n04PrincipalCoreAtom i))) :
    ∀ i : Fin 5, ∀ z ∈ sectorNeighborhood (G.S η) b ε ε,
      ∀ m q, q ∈ unitStrip →
        G.atomFamily η (n04PrincipalCoreAtom i) z m (q + (0, Real.pi)) =
          G.atomFamily η (n04PrincipalCoreAtom i) z m q := by
  have hgp : G.GeometryData η (G.Pos η) b ε :=
    G.geometryData_mono η hg (fun _ _ => trivial) le_rfl le_rfl
  have hgn : G.GeometryData η (G.Neg η) b ε :=
    G.geometryData_mono η hg (fun _ _ => trivial) le_rfl le_rfl
  intro i z hz m q hq
  have hsign : G.Pos η m ∨ G.Neg η m :=
    (Bool.dichotomy ((G.V η).positive m)).symm
  rcases hsign with hm | hm
  · have hp := G.n04PrincipalPositive_principal_periodic h η hgp hf hz hm q hq
    fin_cases i
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2.1
    · exact hp.2.2.2
    · exact G.n04PrincipalPositive_potential_periodic h η hgp hf hz hm
        ((hpair 0).spatial m z hz) ((hpair 2).spatial m z hz)
        ((hpair 3).spatial m z hz) q hq
  · fin_cases i
    · exact G.n04PrincipalNegative_stationary_periodic h η href hz hm .principalA
        (by simp only [n04PrincipalNegativeStationary, true_or, or_true]) q hq
    · exact G.n04PrincipalNegative_stationary_periodic h η href hz hm .principalAInverse
        (by simp only [n04PrincipalNegativeStationary, true_or, or_true]) q hq
    · exact G.n04PrincipalNegative_stationary_periodic h η href hz hm .principalB
        (by simp only [n04PrincipalNegativeStationary, true_or, or_true]) q hq
    · exact G.n04PrincipalNegative_stationary_periodic h η href hz hm .principalC
        (by simp only [n04PrincipalNegativeStationary, true_or, or_true]) q hq
    · exact G.n04PrincipalNegative_potential_periodic h η hgn hz hm q hq

end N04RealizationGauge

end ContinuousFlexibility.Analysis
