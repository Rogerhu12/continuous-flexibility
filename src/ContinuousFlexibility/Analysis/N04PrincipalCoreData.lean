import ContinuousFlexibility.Analysis.N04PrincipalAllPairs
import ContinuousFlexibility.Analysis.N04PrincipalCompleteData

/-!
# A common current-data neighborhood for the five undivided atoms

Each paired estimate has one fixed low order. A finite maximum makes
the five data clauses simultaneous, after which cubic division supplies
the remaining three atoms on exactly the same neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

private theorem n04Principal_currentData_finite
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {ι : Type*} [Fintype ι] {base : ℕ} {ε : ℝ}
    {f : ι → Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ι → ℕ → PolarPoint → ℝ}
    (hE : ∀ m, 0 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (h : ∀ i, ∃ b : ℕ, base ≤ b ∧
      CurrentJetDataOn S T cell (fun _ => True) b ε (f i) (f₀ i)) :
    ∃ b : ℕ, base ≤ b ∧ ∀ i,
      CurrentJetDataOn S T cell (fun _ => True) b ε (f i) (f₀ i) := by
  classical
  let b : ℕ := max base (∑ i, (h i).choose)
  refine ⟨b, le_max_left _ _, fun i => ?_⟩
  have hi : (h i).choose ≤ b := by
    have hs : (h i).choose ≤ ∑ j, (h j).choose :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((h j).choose)) (Finset.mem_univ i)
    exact hs.trans (le_max_right _ _)
  exact (h i).choose_spec.2.mono (fun _ ht => ht) hi le_rfl hE hH

/-- The five atoms before cubic division. -/
def n04PrincipalCoreAtom : Fin 5 → Atom :=
  ![.principalA, .principalAInverse, .principalB, .principalC, .potential]

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04Principal_data_from_core_pairs {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (hpair : ∀ i : Fin 5, G.n04PrincipalPair η b ε
      (G.atomFamily η (n04PrincipalCoreAtom i)) (G.atomRef η (n04PrincipalCoreAtom i)))
    (hperiodic : ∀ i : Fin 5, ∀ z ∈ sectorNeighborhood (G.S η) b ε ε,
      ∀ m q, q ∈ unitStrip →
        G.atomFamily η (n04PrincipalCoreAtom i) z m (q + (0, Real.pi)) =
          G.atomFamily η (n04PrincipalCoreAtom i) z m q) :
    ∃ b' : ℕ, b ≤ b' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ a : Atom, atomIsPrincipal a →
        G.Data η (fun _ => True) b' ε' (G.atomFamily η a) (G.atomRef η a) := by
  have hdata (i : Fin 5) : ∃ b' : ℕ, b ≤ b' ∧
      G.Data η (fun _ => True) b' (min ε (1 / 2))
        (G.atomFamily η (n04PrincipalCoreAtom i)) (G.atomRef η (n04PrincipalCoreAtom i)) :=
    (hpair i).to_currentData h.2.1 (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1
      (hperiodic i) (fun m q _ => congrFun
        (G.n04Principal_atom_zero η (n04PrincipalCoreAtom i) m) q)
  have hall := n04Principal_currentData_finite (G.cost_nonneg η).1
    (G.cost_nonneg η).2.1 hdata
  let b' : ℕ := hall.choose
  have hb' : b ≤ b' := hall.choose_spec.1
  let ε' : ℝ := min ε (1 / 2)
  have hε' : 0 < ε' := lt_min h.2.1 (by norm_num)
  have heps : ε' ≤ ε := min_le_left _ _
  have hA : G.Data η (fun _ => True) b' ε'
      (G.atomFamily η .principalA) (G.atomRef η .principalA) := hall.choose_spec.2 0
  have hAI : G.Data η (fun _ => True) b' ε'
      (G.atomFamily η .principalAInverse) (G.atomRef η .principalAInverse) := hall.choose_spec.2 1
  have hB : G.Data η (fun _ => True) b' ε'
      (G.atomFamily η .principalB) (G.atomRef η .principalB) := hall.choose_spec.2 2
  have hC : G.Data η (fun _ => True) b' ε'
      (G.atomFamily η .principalC) (G.atomRef η .principalC) := hall.choose_spec.2 3
  have hV : G.Data η (fun _ => True) b' ε'
      (G.atomFamily η .potential) (G.atomRef η .potential) := hall.choose_spec.2 4
  exact ⟨b', hb', ε', hε', heps,
    G.n04Principal_completeData (G.admissible_mono h hb' hε' heps) η href hA hAI hB hC hV⟩

end N04RealizationGauge

end ContinuousFlexibility.Analysis
