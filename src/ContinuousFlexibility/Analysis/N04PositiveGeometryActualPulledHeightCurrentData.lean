module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryActualPulledHeightSamplePrefix
public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledGauge
public import ContinuousFlexibility.Analysis.N04PositiveGeometryCurrentJointPowers
public import ContinuousFlexibility.Analysis.N04PositiveGeometryGaugeRegularity
public import ContinuousFlexibility.Analysis.N04PrincipalPositiveIndex

/-!
# Current data for the actual positive pulled height

The retained whole atlas has unit endpoints on each positive piece.
Its pulled height is therefore exactly the controlled field already
estimated at the fixed reference inverse. The same low neighborhood
works for every auxiliary column and every derivative order.
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

theorem n04PositiveGeometry_controlledGauge_pulledHeight_fields
    {W : N04RealizationStart} {X : N04RealizationChoice W}
    (F : N04PositiveGeometryControlledFamily W X 3)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (η : (W.S.height (3 / 4 : ℝ)).Space) (m : ℕ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (hi : e m = .inr i) :
    ((F.gauge e Y H₀).V η).cell m = X.cell i ∧
      ∀ z : StateDirections W.S × ℝ,
        (F.gauge e Y H₀).pulledHeight η z m =
          fun q => n04PositiveGeometry_controlledPulledHeight F Y H₀ i
            (liftSectorParameter W.S W.C z) q := by
  let G := F.gauge e Y H₀
  have fields (z : AnnularState W.S × ℝ) :=
    n04WholeReferenceGaugeAtlasData_positive_fields W.C W.L (W.A X.e₀) e X.cell
      (fun j => positiveReferenceCylinderChart (Y j))
      (fun j => positiveReferenceCylinderInverse (Y j)) (fun j p => H₀ j p.1)
      F.toN04PositiveGeometryControlData.τ F.toN04PositiveGeometryControlData.σ
      F.toN04PositiveGeometryControlData.Q F.buffer.region z m i hi
  refine ⟨(fields (W.C.referenceState, 0)).2.2.2.2.2.1, fun z => ?_⟩
  let state := liftSectorParameter W.S W.C z
  have hl : (G.V η).left m = 0 := (fields state).1
  have hr : (G.V η).right m = 1 := (fields state).2.1
  have hI : (G.V η).inverseChart state m =
      wholePositiveReferenceGaugeInverse (F.toN04PositiveGeometryControlData.τ state i)
        (positiveReferenceCylinderInverse (Y i)) := (fields state).2.2.2.2.2.2.2.2.1
  have hH : (G.V η).height state m =
      wholePositiveReferenceGaugeHeight (fun p => H₀ i p.1)
        (F.toN04PositiveGeometryControlData.σ state i)
        (F.toN04PositiveGeometryControlData.Q state i) := (fields state).2.2.2.2.2.2.2.2.2.1
  funext q
  change (G.V η).height state m ((G.V η).inverseChart state m
    ((G.V η).left m + ((G.V η).right m - (G.V η).left m) * q.1, q.2)) = _
  rw [hl, hr, sub_zero, one_mul, zero_add, hI, hH]
  rfl

/-- Actual current data, without a source-jet or reference-jet premise.
The low base and radius are selected before all parameter and spatial
orders, and are shared by every auxiliary-column replacement. -/
theorem n04PositiveGeometry_actualControlledPulledHeight_currentData
    {W : N04RealizationStart} {X : N04RealizationChoice W}
    (F : N04PositiveGeometryControlledFamily W X 3)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H₀)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hFb : F.base ≤ base) (hFε : ε ≤ F.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side) :
    ∃ low : ℕ, base ≤ low ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      ∀ η : (W.S.height (3 / 4 : ℝ)).Space,
        (F.gauge e Y H₀).Data η ((F.gauge e Y H₀).Pos η) low δ
          ((F.gauge e Y H₀).pulledHeight η) ((F.gauge e Y H₀).pulledHeightRef η) := by
  classical
  let G := F.gauge e Y H₀
  let data := n04PositiveGeometry_actualControlledPulledHeight_sample_prefix F le_rfl
    Y H₀ href hmaterial hb hε hεW hεone hFb hFε hflow hctx
  let low := data.choose
  let δ := min ε (1 / 2)
  have hlow : base ≤ low := data.choose_spec.1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hsub : sectorNeighborhood W.S low δ δ ⊆ sectorNeighborhood W.S base ε ε :=
    sectorNeighborhood_mono W.S hlow hδε hδε
  have hU : IsOpen (sectorNeighborhood W.S low δ δ) :=
    sectorNeighborhood_isOpen W.S low δ δ
  have hA : G.Admissible low δ := G.admissible_mono
    (F.gauge_admissible e Y H₀ href) (hFb.trans hlow) hδ (hδε.trans hFε)
  let RF (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :=
    n04PositiveGeometry_actualControlledPulledHeight_mixedJetRegularity F le_rfl Y H₀ href
      hb hε hεW hεone hFb hFε hflow hctx i
  refine ⟨low, hlow, δ, hδ, hδε, hδhalf, fun η => ?_⟩
  let index (m : ℕ) (hm : G.Pos η m) := (G.n04PrincipalDivided_positive_index η hm).choose
  have hindex (m : ℕ) (hm : G.Pos η m) : e m = .inr (index m hm) :=
    (G.n04PrincipalDivided_positive_index η hm).choose_spec
  have hfields (m : ℕ) (hm : G.Pos η m) :=
    n04PositiveGeometry_controlledGauge_pulledHeight_fields F e Y H₀ η m (index m hm)
      (hindex m hm)
  let J₀ (m : ℕ) (hm : G.Pos η m) (a b : ℕ) (q : unitStrip) :=
    (RF (index m hm)).parameter a b q.val (mem_univ _)
  let J : ∀ m, G.Pos η m → ∀ a b (q : unitStrip),
      SmoothDirections (sectorNeighborhood (G.S η) low δ δ)
        (fun z => mixedDerivative a b (G.pulledHeight η z m) q.val) := fun m hm a b q =>
    ((J₀ m hm a b q).restrict hU hsub).congrOn (fun z _ =>
      congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f q.val)
        ((hfields m hm).2 z).symm)
  have hcost := G.cost_nonneg η
  apply CurrentJetDataOn.of_positiveMixedUnitPower hδ hδhalf hcost.2.2 hcost.2.1
    (G.positivePulledHeight_regular η hA) (fun m _ => G.pulledHeightRef_eq_zero η m) J
  intro k hk
  let sd := data.choose_spec.2 k
  let shift := sd.choose
  refine ⟨shift, fun s => ?_⟩
  let bd := sd.choose_spec s
  let A := bd.choose
  refine ⟨A, zero_lt_one.trans_le bd.choose_spec.1, ?_⟩
  intro m hm z hz q a b hab R hR hzR v hv hvR
  have hzlow : pairGrading (sectorGrading W.S) realGrading low z ≤ 1 :=
    n04Principal_parameter_low_le_one (S := W.S) hδhalf hz
  have hb' := bd.choose_spec.2 (index m hm) k le_rfl a b hab q.val q.property
    (J₀ m hm a b q) z (hsub hz) hzlow v hv R hR hzR hvR
  have hvalue : |(J m hm a b q).D k z v| = ‖(J₀ m hm a b q).D k z v‖ :=
    (Real.norm_eq_abs _).symm
  have hscalar : A * W.U.E0 (W.U.sample (X.cell (index m hm))) ^ A *
      parameterHeightWeight (W.U.H (W.U.sample (X.cell (index m hm))) ^ (3 / 4 : ℝ)) k *
      R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) =
        A * W.U.E0 (W.U.sample ((G.V η).cell m)) ^ A *
          W.U.H (W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
          R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
    rw [(hfields m hm).1]
    simp only [parameterHeightWeight, Nat.ne_of_gt hk, if_false]
  exact hvalue.trans_le (hb'.trans_eq hscalar)

end ContinuousFlexibility.Analysis
