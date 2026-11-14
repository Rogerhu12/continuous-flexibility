module

public import ContinuousFlexibility.Analysis.N04PrincipalPairPieces
public import ContinuousFlexibility.Analysis.N04PrincipalPairNeighborhood
public import ContinuousFlexibility.Analysis.N04PrincipalPairCurrentData
public import ContinuousFlexibility.Analysis.N04PrincipalPositivePairInputs
public import ContinuousFlexibility.Analysis.N04PrincipalPositiveOrientation
public import ContinuousFlexibility.Analysis.N04PrincipalNegativePotentialPair

/-!
# Paired estimates on every piece of the same atlas

The positive and negative certificates are joined before the exact
current-data interface is reconstructed. In particular the resulting
smooth directional tower is defined on every piece, as the frozen
interface requires even when later restricted to a predicate.
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

abbrev n04PrincipalPair (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (b : ℕ) (ε : ℝ)
    (f : Parameter (G.S η) → ℕ → PolarPoint → ℝ) (f₀ : ℕ → PolarPoint → ℝ) : Prop :=
  N04PrincipalPairBounds (parameterGrading (G.S η))
    (fun m => G.W.U.E0 (G.W.U.sample ((G.V η).cell m)))
    (fun m => G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ))
    (U := sectorNeighborhood (G.S η) b ε ε) (Ω := unitStrip)
    (fun m z => f z m) f₀

theorem n04Principal_pair_union {b : ℕ} {ε : ℝ}
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {f : Parameter (G.S η) → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hp : G.n04PrincipalPositivePair η b ε f f₀)
    (hn : G.n04PrincipalNegativePairBounds η b ε f f₀) :
    G.n04PrincipalPair η b ε f f₀ :=
  hp.union_subtype hn (n07aParameterGrading_monotone (G.S η))
    (G.cost_nonneg η).2.2
    (fun m => Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _)
    (fun m => (Bool.dichotomy ((G.V η).positive m)).symm)

theorem n04Principal_atom_zero
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (a : Atom) (m : ℕ) :
    G.atomFamily η a 0 m = G.atomRef η a m := by
  unfold atomFamily atomRef
  rw [G.n04PrincipalPositive_lift_zero η]

theorem n04Principal_inverseA_pair {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hA : G.n04PrincipalPair η b ε
      (G.atomFamily η .principalA) (G.atomRef η .principalA)) :
    ∃ b' : ℕ, b ≤ b' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 / 2 ∧
      G.n04PrincipalPair η b' ε'
        (G.atomFamily η .principalAInverse) (G.atomRef η .principalAInverse) := by
  have hD : IsAccumulatingProfile G.W.D := G.W.radial.1
  have hT : IsMaterialData G.W.D G.W.U := isMaterialData_enlargedMaterialData hD G.W.hT
  have hzero : ∀ m, EqOn (G.atomFamily η .principalA 0 m)
      (G.atomRef η .principalA m) unitStrip := by
    intro m q _
    exact congrFun (G.n04Principal_atom_zero η .principalA m) q
  have hr : ∃ R : ℝ, 0 < R ∧ ∀ m q, q ∈ unitStrip →
      G.atomRef η .principalA m q ≠ 0 ∧
        |(G.atomRef η .principalA m q)⁻¹| ≤
          R * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ R := by
    have hb := href.2 0
    refine ⟨hb.choose, hb.choose_spec.1, ?_⟩
    intro m q hq
    refine ⟨(G.n04PrincipalPositive_reference_principalA_atom_pos h η m ⟨q, hq⟩).ne', ?_⟩
    have hi := hb.choose_spec.2 m .principalAInverse q hq 0 0 (by omega)
    rw [spaces_mixedDerivative_zero] at hi
    exact hi
  exact hA.inverse_neighborhood hD hT h.2.1
    (G.n04PrincipalPositive_parameter_interpolation η) (G.cost_nonneg η).2.2 hzero hr

end N04RealizationGauge

end ContinuousFlexibility.Analysis
