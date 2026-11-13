import ContinuousFlexibility.Analysis.N04PositiveGeometryAtomRegularity
import ContinuousFlexibility.Analysis.N04PositiveGeometryCurrentData

/-!
# Regularity on every positive piece of the chosen atlas

The admissible family gives a global positive range certificate on each
positive piece. Auxiliary-column replacement retains these exact fields.
Consequently both the geometric atoms and the pulled height meet the
spatial and reference clauses of the current-data constructor.
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

theorem n04PositiveGeometry_gaugeAtlas_range
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) → N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) (c d : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (href : ∀ i, PositiveChartRangeGeometry (ψ i) (χ i) (h₀ i)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (z : AnnularState S × ℝ)
    (hrelative : ∀ i, WholePositiveChartGeometry (σ z i) (τ z i)
      (wholePositiveChartHeight (σ z i) (Q z i))
      (n04PositiveLeft i) (n04PositiveRight i) (c i) (d i)) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    ∀ m, V.positive m = true →
      PositiveChartRangeGeometry (V.chart z m) (V.inverseChart z m) (V.height z m)
        (V.physicalLeft m) (V.physicalRight m) (V.left m) (V.right m) := by
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  intro m hm
  change PositiveChartRangeGeometry (V.chart z m) (V.inverseChart z m) (V.height z m)
    (V.physicalLeft m) (V.physicalRight m) (V.left m) (V.right m)
  cases hi : e m with
  | inl j =>
      have hnegative : V.positive m = false := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, hi]
      exact False.elim (Bool.false_ne_true (hnegative.symm.trans hm))
  | inr i =>
      have hf := n04WholeReferenceGaugeAtlasData_positive_fields
        C L K e cell ψ χ h₀ τ σ Q N z m i hi
      rw [hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1,
        hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.1, hf.2.2.2.1, hf.1, hf.2.1]
      exact wholePositiveReferenceGauge_geometry (href i) (hrelative i)

namespace N04RealizationGauge

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

theorem positiveRangeGeometry {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε)
    (z : Parameter (G.S η)) (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    (m : ℕ) (hm : G.Pos η m) :
    PositiveChartRangeGeometry ((G.V η).chart (G.lift η z) m)
      ((G.V η).inverseChart (G.lift η z) m) ((G.V η).height (G.lift η z) m)
      ((G.V η).physicalLeft m) ((G.V η).physicalRight m)
      ((G.V η).left m) ((G.V η).right m) := by
  refine Exists.elim hG.2.2.2.2.2 fun B hB => ?_
  refine Exists.elim hB fun lower hlower => ?_
  refine Exists.elim hlower fun upper hmatching => ?_
  have hs : stateSector G.W.S (G.lift η z).1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hzstate : G.lift η z ∈ stateNeighborhood G.W.S G.W.C b ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  exact n04PositiveGeometry_gaugeAtlas_range G.W.C G.W.L (G.W.A G.X.e₀)
    G.e G.X.cell (fun i => positiveReferenceCylinderChart (G.Y i))
    (fun i => positiveReferenceCylinderInverse (G.Y i)) (fun i p => G.H i p.1)
    G.τ G.σ G.Q G.N B.centerLeft B.centerRight (fun i => (hG.2.2.2.1 i).1)
    (G.lift η z) (fun i => wholePositiveChartGeometry_of_matching
      (hmatching.2 (G.lift η z) hzstate hs i)) m hm

theorem positiveAtom_regular {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε)
    (a : Atom) (ha : atomIsGeometry a) :
    ∀ z ∈ sectorNeighborhood (G.S η) b ε ε, ∀ m, G.Pos η m →
      ContDiffOn ℝ ∞ (G.atomFamily η a z m) unitStrip ∧
        ∀ q ∈ unitStrip, G.atomFamily η a z m (q + (0, Real.pi)) =
          G.atomFamily η a z m q := by
  intro z hz m hm
  have h := n04PositiveGeometry_atom_regular (D := G.W.D) (T := G.W.U)
    (G.C η) (G.L η) (G.V η) (G.lift η z) m
    (G.positiveRangeGeometry η hG z hz m hm) a ha
  exact ⟨h.1.contDiffOn, fun q _ => h.2 q⟩

theorem positivePulledHeight_regular {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε) :
    ∀ z ∈ sectorNeighborhood (G.S η) b ε ε, ∀ m, G.Pos η m →
      ContDiffOn ℝ ∞ (G.pulledHeight η z m) unitStrip ∧
        ∀ q ∈ unitStrip, G.pulledHeight η z m (q + (0, Real.pi)) =
          G.pulledHeight η z m q := by
  intro z hz m hm
  have h := n04PositiveGeometry_pulledHeight_regular (G.V η) (G.lift η z) m
    (G.positiveRangeGeometry η hG z hz m hm)
  exact ⟨h.1.contDiffOn, fun q _ => h.2 q⟩

theorem atomRef_eq_zero (a : Atom) (m : ℕ) :
    G.atomRef η a m = G.atomFamily η a 0 m := by
  change atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) (G.ref η) m a =
    atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) (G.lift η 0) m a
  rw [show G.lift η 0 = G.ref η from n07a_lift_zero_parameter]

theorem pulledHeightRef_eq_zero (m : ℕ) :
    G.pulledHeightRef η m = G.pulledHeight η 0 m := by
  change (fun q => (G.V η).height (G.ref η) m
      ((G.V η).inverseChart (G.ref η) m (canonicalUnitPoint (G.V η) m q))) =
    (fun q => (G.V η).height (G.lift η 0) m
      ((G.V η).inverseChart (G.lift η 0) m (canonicalUnitPoint (G.V η) m q)))
  rw [show G.lift η 0 = G.ref η from n07a_lift_zero_parameter]

/-- Once the actual positive parameter jets have been estimated, all
value, reference, periodicity and difference clauses follow on the same
neighborhood. This final collector does not change the chosen gauge. -/
theorem positiveGeometryData_of_parameterJets {b : ℕ} {ε : ℝ}
    (hG : G.Admissible b ε) (hε : ε ≤ 1 / 2)
    (J : ∀ a : Atom, atomIsGeometry a → ∀ m, G.Pos η m → ∀ i j (q : unitStrip),
      SmoothDirections (sectorNeighborhood (G.S η) b ε ε)
        (fun z => mixedDerivative i j (G.atomFamily η a z m) q.val))
    (hJ : ∀ a : Atom, ∀ ha : atomIsGeometry a, ∀ k : ℕ, 0 < k →
      ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ z ∈ sectorNeighborhood (G.S η) b ε ε, ∀ v : Fin k → Parameter (G.S η),
        ∀ m, ∀ hm : G.Pos η m, ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
          |(J a ha m hm i j q).D k z v| ≤
            B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
              G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
                oneHighVariationWeight (parameterGrading (G.S η)) b (s + loss) z v)
    (JH : ∀ m, G.Pos η m → ∀ i j (q : unitStrip),
      SmoothDirections (sectorNeighborhood (G.S η) b ε ε)
        (fun z => mixedDerivative i j (G.pulledHeight η z m) q.val))
    (hJH : ∀ k : ℕ, 0 < k → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood (G.S η) b ε ε, ∀ v : Fin k → Parameter (G.S η),
      ∀ m, ∀ hm : G.Pos η m, ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
        |(JH m hm i j q).D k z v| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
            G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (parameterGrading (G.S η)) b (s + loss) z v) :
    G.GeometryData η (G.Pos η) b ε := by
  have hlow (z : Parameter (G.S η)) (hz : z ∈ sectorNeighborhood (G.S η) b ε ε) :
      parameterGrading (G.S η) b z ≤ 1 := by
    have hsum := add_lt_add hz.1 hz.2
    simp only [parameterGrading, pairGrading_apply, realGrading,
      coe_normSeminorm, Real.norm_eq_abs]
    linarith only [hsum, hε]
  have hcost := G.cost_nonneg η
  constructor
  · intro a ha
    exact CurrentJetDataOn.of_positiveParameterJets hG.2.1 hcost.2.2 hcost.2.1 hlow
      (G.positiveAtom_regular η hG a ha) (fun m _ => G.atomRef_eq_zero η a m)
      (J a ha) (hJ a ha)
  · exact CurrentJetDataOn.of_positiveParameterJets hG.2.1 hcost.2.2 hcost.2.1 hlow
      (G.positivePulledHeight_regular η hG) (fun m _ => G.pulledHeightRef_eq_zero η m)
      JH hJH

end N04RealizationGauge

end ContinuousFlexibility.Analysis
