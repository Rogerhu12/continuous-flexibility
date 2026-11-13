import ContinuousFlexibility.Analysis.N04NegativeInverseGeometry
import ContinuousFlexibility.Analysis.N04NegativeInverseOneHigh
import ContinuousFlexibility.Analysis.N04NegativeGeometryAuxiliary

/-!
# Collect the actual negative inverse fields on one neighborhood

The raw quantitative input is used only at the zero auxiliary column.
The genuine joint towers supply all spatial and parameter regularity;
the exact value at parameter zero supplies the reference field. The
result is transported to every auxiliary column without changing the
neighborhood or any material cost.
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

/-- Raw positive prefixes of the actual mixed derivatives. The loss
shift is selected before the spatial order and uniform in the piece. -/
def N04NegativeInverseRawPrefixes
    (S : PhysicalSpacesData) (T : MaterialData) (cell : ℕ → ℕ)
    (P : ℕ → Prop) (base : ℕ) (ε : ℝ)
    (f : Parameter S → ℕ → PolarPoint → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ shift : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ m, P m → ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
    ∀ Q : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative i j (f z m) q),
    ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
    (∀ l, parameterGrading S base (v l) ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → parameterGrading S (base + s + shift * k + 1) z ≤ R →
      (∀ l, parameterGrading S (base + s + shift * k + 1) (v l) ≤ R) →
      |Q.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
        T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
          R ^ (((i + j + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1))

theorem n04NegativeInverse_parameter_low {S : PhysicalSpacesData}
    {base : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 2) {z : Parameter S}
    (hz : z ∈ sectorNeighborhood S base ε ε) : parameterGrading S base z ≤ 1 := by
  change sectorGrading S base z.1 + |z.2| ≤ 1
  have h₁ := hz.1
  have h₂ := hz.2
  linarith

/-- The actual joint tower and its exact reference value close all
qualitative clauses of the current-data collector. -/
theorem CurrentJetDataOn.negativeInverse_of_joint_prefixes
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 2)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (J : ∀ m, P m → SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
      (fun x : Parameter S × PolarPoint => f x.1 m x.2))
    (hperiod : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m → ∀ q ∈ unitStrip,
      f z m (q + (0, Real.pi)) = f z m q)
    (hzero : ∀ m, P m → ∀ q ∈ unitStrip, f 0 m q = f₀ m q)
    (hraw : N04NegativeInverseRawPrefixes S T cell P base ε f) :
    CurrentJetDataOn S T cell P base ε f f₀ := by
  let RF (m : ℕ) (hm : P m) := n04Realization_jointMixedRegularity (J m hm)
    (sectorNeighborhood_isOpen S base ε ε) (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex S base ε ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))
  have hz₀ : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε :=
    ⟨(sectorGrading S base).map_zero'.trans_lt hε,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  have href (m : ℕ) (hm : P m) : ContDiffOn ℝ ∞ (f₀ m) unitStrip :=
    ((RF m hm).spatial 0 hz₀).congr (fun q hq => (hzero m hm q hq).symm)
  apply CurrentJetDataOn.negativeInverse_of_positive_prefixes hε hE hH RF hperiod href
    hzero (fun _ hz => n04NegativeInverse_parameter_low hsmall hz)
  intro k hk
  obtain ⟨shift, hshift⟩ := hraw k hk
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hshift s
  exact ⟨B, hB, fun m hm q hq i j hij =>
    hb m hm q hq i j hij ((RF m hm).parameter i j q hq)⟩

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The final inverse interface follows from raw estimates for its
three actual fields at the zero auxiliary column. -/
theorem negativeInverse_collect
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε) (hsmall : ε ≤ 1 / 2)
    (hatom : ∀ a : Atom, atomIsNegativeInverse a →
      N04NegativeInverseRawPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
        (G.atomFamily 0 a))
    (hheight : N04NegativeInverseRawPrefixes (G.S 0) G.W.U (G.V 0).cell
      (G.Neg 0) b ε (G.pulledHeight 0)) :
    ∀ η, G.NegativeAtomData η atomIsNegativeInverse b ε ∧
      G.Data η (G.Neg η) b ε (G.pulledHeight η) (G.pulledHeightRef η) := by
  have hU : IsOpen (sectorNeighborhood G.W.S b ε ε) :=
    sectorNeighborhood_isOpen G.W.S b ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hsub : sectorNeighborhood G.W.S b ε ε ⊆
      sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε :=
    sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1
  have hlift : G.lift 0 (0 : Parameter (G.S 0)) = G.ref 0 :=
    (liftSectorParameter_eq_affine (G.S 0) (G.C 0) 0).trans
      ((congrArg (fun w : AnnularState (G.S 0) × ℝ => ((G.C 0).referenceState, 0) + w)
        (ContinuousLinearMap.map_zero (sectorParameterInclusion (G.S 0)))).trans (add_zero _))
  have hgeom (a : Atom) (ha : atomIsNegativeInverse a) : atomIsGeometry a := by
    cases a <;> first | trivial | exact ha.elim
  have hi : G.NegativeAtomData 0 atomIsNegativeInverse b ε := by
    intro a ha
    apply CurrentJetDataOn.negativeInverse_of_joint_prefixes hadm.2.1 hsmall
      (G.cost_nonneg 0).2.2 (G.cost_nonneg 0).2.1
      (fun m hm => (G.negativeInverseAtomJointTower 0 m hm a ha).restrict (hU.prod hΩ)
        (fun x hx => ⟨hsub hx.1, hx.2⟩))
    · intro z hz m hm q hq
      exact (G.negative_geometry_spatial 0 z (hsub hz) m hm a (hgeom a ha)).2 q hq
    · intro m hm q hq
      change atom G.W.D G.W.U (G.S 0) (G.C 0) (G.L 0) (G.V 0)
        (G.lift 0 0) m a q = atom G.W.D G.W.U (G.S 0) (G.C 0) (G.L 0) (G.V 0)
          (G.ref 0) m a q
      rw [hlift]
    · exact hatom a ha
  have hh : G.Data 0 (G.Neg 0) b ε (G.pulledHeight 0) (G.pulledHeightRef 0) := by
    apply CurrentJetDataOn.negativeInverse_of_joint_prefixes hadm.2.1 hsmall
      (G.cost_nonneg 0).2.2 (G.cost_nonneg 0).2.1
      (fun m hm => (G.negativePulledHeightJointTower 0 m hm).restrict (hU.prod hΩ)
        (fun x hx => ⟨hsub hx.1, hx.2⟩))
    · intro z hz m hm q hq
      exact G.negativePulledHeight_period 0 (hsub hz) m hm hq
    · intro m hm q hq
      change G.heightField 0 m (G.lift 0 0) (G.pulledPoint 0 (G.lift 0 0) m q) =
        G.heightField 0 m (G.ref 0) (G.pulledPoint 0 (G.ref 0) m q)
      rw [hlift]
    · exact hheight
  intro η
  exact ⟨fun a ha => G.geometryAtom_data_auxiliary 0 η (G.Neg 0) b ε a
    (hgeom a ha) (hi a ha), G.pulledHeight_data_auxiliary 0 η (G.Neg 0) b ε hh⟩

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_collect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_collect
