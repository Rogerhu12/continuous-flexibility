import ContinuousFlexibility.Analysis.N04RealizationLeadNegativeSplit
import ContinuousFlexibility.Analysis.N04NegativeGeometryPhysicalAtomTowers
import ContinuousFlexibility.Analysis.N04NegativeGeometryDataCollector
import ContinuousFlexibility.Analysis.N04NegativeGeometryAuxiliary

/-!
# Collecting the actual four negative chart atoms

The actual joint towers supply spatial regularity and all parameter jets.
Their value at zero is the stored reference atom, and their spatial period
is already proved on the whole fixed reference half. Thus the quantitative
input needed for the four-atom interface consists only of positive-order
parameter estimates. The first derivative recovers the reference difference.
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

theorem atomIsNegativeChart_geometry {a : Atom} (ha : atomIsNegativeChart a) :
    atomIsGeometry a := by
  cases a <;> first | trivial | exact ha.elim

theorem atomIsNegativeChart_physical {a : Atom} (ha : atomIsNegativeChart a) :
    negativePhysicalGeometryAtom a := by
  cases a <;> first | trivial | exact ha.elim

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- Every auxiliary choice has the same literal reference value at the
zero sector parameter. This statement needs no estimate. -/
theorem atomFamily_zero (η : (G.W.S.height (3 / 4 : ℝ)).Space) (a : Atom) :
    G.atomFamily η a 0 = G.atomRef η a := by
  have hz : liftSectorParameter G.W.S G.W.C (0 : Parameter G.W.S) =
      (G.W.C.referenceState, 0) :=
    (liftSectorParameter_eq_affine G.W.S G.W.C 0).trans
      ((congrArg (fun w : AnnularState G.W.S × ℝ => (G.W.C.referenceState, 0) + w)
        (ContinuousLinearMap.map_zero (sectorParameterInclusion G.W.S))).trans (add_zero _))
  funext m q
  exact congrArg (fun w => atom G.W.D G.W.U (G.S η) (G.C η) (G.L η)
    (G.V η) w m a q) hz

/-- Restrict the actual mixed tower to a smaller sector. The atom and
the fixed physical unit map are unchanged. -/
def negativeChartMixedRegularity
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (b : ℕ) (ε : ℝ)
    (hb : G.W.base ≤ b) (hε : ε ≤ G.W.ε)
    (m : ℕ) (hm : G.Neg η m) (a : Atom) (ha : atomIsNegativeChart a) :
    MixedJetRegularity (sectorNeighborhood G.W.S b ε ε) unitStrip
      (fun z => G.atomFamily η a z m) := by
  let J := G.negativePhysicalAtomMixedRegularity η m hm a
    (atomIsNegativeChart_physical ha)
  have hsub := sectorNeighborhood_mono G.W.S hb hε hε
  exact {
    spatial := fun z hz => J.spatial z (hsub hz)
    parameter := fun i j q hq => (J.parameter i j q hq).restrict
      (isOpen_sectorNeighborhood G.W.S b ε ε) hsub }

/-- Actual positive-order estimates assemble the full current-difference
data, including order zero and the spatial period. Constants are chosen
before the piece, so no compactness argument can hide a piece-dependent
loss or discard the sampled height factor. -/
theorem negativeChart_data_of_positive_bounds
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (b : ℕ) (ε : ℝ)
    (hb : G.W.base ≤ b) (hεpos : 0 < ε) (hε : ε ≤ G.W.ε)
    (hεhalf : ε ≤ 1 / 2)
    (hbound : ∀ a : Atom, atomIsNegativeChart a →
      ∀ k : ℕ, 0 < k → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m, G.Neg η m → ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood G.W.S b ε ε)
        (fun z => mixedDerivative i j (G.atomFamily η a z m) q),
      ∀ z ∈ sectorNeighborhood G.W.S b ε ε, ∀ v : Fin k → Parameter G.W.S,
        |J.D k z v| ≤ B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
          G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (parameterGrading G.W.S) b (s + loss) z v) :
    G.NegativeAtomData η atomIsNegativeChart b ε := by
  have hsub := sectorNeighborhood_mono G.W.S hb hε hε
  have hz₀ : (0 : Parameter G.W.S) ∈ sectorNeighborhood G.W.S b ε ε := by
    constructor
    · change sectorGrading G.W.S b 0 < ε
      exact (sectorGrading G.W.S b).map_zero'.trans_lt hεpos
    · change |(0 : ℝ)| < ε
      simpa only [abs_zero] using hεpos
  have hlow (z : Parameter G.W.S) (hz : z ∈ sectorNeighborhood G.W.S b ε ε) :
      parameterGrading G.W.S b z ≤ 1 := by
    rw [show parameterGrading G.W.S b z = sectorGrading G.W.S b z.1 + |z.2| from
      pairGrading_apply (E := StateDirections G.W.S) (F := ℝ)
        (sectorGrading G.W.S) realGrading b z]
    linarith only [hz.1, hz.2, hεhalf]
  intro a ha
  let RF := G.negativeChartMixedRegularity η b ε hb hε
  apply CurrentJetDataOn.of_positive_towers hεpos (G.cost_nonneg η).2.2
    (G.cost_nonneg η).2.1 (fun m hm => RF m hm a ha)
  · intro z hz m hm q hq
    exact (G.negative_geometry_spatial η z (hsub hz) m hm a
      (atomIsNegativeChart_geometry ha)).2 q hq
  · intro m hm
    simpa only [G.atomFamily_zero η a] using (RF m hm a ha).spatial 0 hz₀
  · intro m hm q hq
    exact congrFun (congrFun (G.atomFamily_zero η a) m) q
  · exact hlow
  · intro k hk
    obtain ⟨loss, hB⟩ := hbound a ha k hk
    refine ⟨loss, fun s => ?_⟩
    obtain ⟨B, hBpos, hBs⟩ := hB s
    exact ⟨B, hBpos, fun m hm q hq i j hij z hz v =>
      hBs m hm q hq i j hij ((RF m hm a ha).parameter i j q hq) z hz v⟩

/-- The same chart data works for every auxiliary source column. -/
theorem negativeChartData_auxiliary
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space) (b : ℕ) (ε : ℝ)
    (h : G.NegativeAtomData η₀ atomIsNegativeChart b ε) :
    G.NegativeAtomData η atomIsNegativeChart b ε :=
  fun a ha => G.geometryAtom_data_auxiliary η₀ η (G.Neg η₀) b ε a
    (atomIsNegativeChart_geometry ha) (h a ha)

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_data_of_positive_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_data_of_positive_bounds
