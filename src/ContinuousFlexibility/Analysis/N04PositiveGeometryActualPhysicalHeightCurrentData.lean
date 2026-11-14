module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryActualPhysicalHeightSamplePrefix
public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledGauge
public import ContinuousFlexibility.Analysis.N04PositiveGeometryCurrentJointPowers
public import ContinuousFlexibility.Analysis.N04PositiveGeometryGaugeRegularity
public import ContinuousFlexibility.Analysis.N04PrincipalPositiveIndex

/-!
# Current data for the actual physical height

The positive height atom is the physical unit pullback of the same
moving quotient. Its positive joint words give the required one-high
parameter estimates on one neighborhood, for every auxiliary column.
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

private theorem currentPhysicalHeight_pureDirections
    {E : Type*} [Zero E] {n : ℕ} (w : StateAngleWord n)
    (u : Fin n → E × PolarPoint)
    (h₀ : ∀ j, w.isState j = false → (u j).1 = 0)
    (h₁ : ∀ j, w.isState j = true → (u j).2 = 0) :
    ∀ j, if w.isState j then (u j).2 = 0 else (u j).1 = 0 := by
  intro j
  cases hj : w.isState j with
  | false => simpa only [hj, Bool.false_eq_true, ite_false] using h₀ j hj
  | true => simpa only [hj, ite_true] using h₁ j hj

private theorem currentPhysicalHeight_scalar
    (A E H R : ℝ) (angle shift s : ℕ) {a k : ℕ}
    (hk : 0 < k) (ha : a = k) :
    A * E ^ A * parameterHeightWeight H a *
        R ^ (((angle + shift * a : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) =
      A * E ^ A * H *
        R ^ (((angle + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
  subst a
  simp only [parameterHeightWeight, if_neg (Nat.ne_of_gt hk)]

theorem n04PositiveGeometry_controlledGauge_height_fields
    {W : N04RealizationStart} {X : N04RealizationChoice W}
    (F : N04PositiveGeometryControlledFamily W X 3)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (η : (W.S.height (3 / 4 : ℝ)).Space) (m : ℕ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (hi : e m = .inr i) :
    ((F.gauge e Y H₀).V η).cell m = X.cell i ∧
      ∀ z : StateDirections W.S × ℝ,
        (F.gauge e Y H₀).atomFamily η .height z m =
          fun q => n04PositiveGeometry_controlledUnitHeight F H₀ i
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
  have hl : (G.V η).physicalLeft m = n04PositiveLeft i := (fields state).2.2.1
  have hr : (G.V η).physicalRight m = n04PositiveRight i := (fields state).2.2.2.1
  have hH : (G.V η).height state m =
      wholePositiveReferenceGaugeHeight (fun p => H₀ i p.1)
        (F.toN04PositiveGeometryControlData.σ state i)
        (F.toN04PositiveGeometryControlData.Q state i) := (fields state).2.2.2.2.2.2.2.2.2.1
  funext q
  change (G.V η).height state m ((G.V η).physicalLeft m +
    ((G.V η).physicalRight m - (G.V η).physicalLeft m) * q.1, q.2) = _
  rw [hl, hr, hH]
  rfl

theorem n04PositiveGeometry_actualControlledPhysicalHeight_currentData_of_inverseWords
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
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (JS : ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × PolarPoint =>
          F.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C y.1) i y.2))
    (hσ : N04PositiveGeometryInverseTransportSamplePrefix F base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      ∀ η : (W.S.height (3 / 4 : ℝ)).Space,
        (F.gauge e Y H₀).Data η ((F.gauge e Y H₀).Pos η) low δ
          ((F.gauge e Y H₀).atomFamily η .height) ((F.gauge e Y H₀).atomRef η .height) := by
  classical
  let G := F.gauge e Y H₀
  let data := n04PositiveGeometry_actualControlledUnitHeight_sample_prefix_of_inverseWords
    F le_rfl Y H₀ href hmaterial hb hε hεW hεone hFb hFε hflow hctx JS hσ
  let low := data.choose
  let δ := min ε (1 / 2)
  have hlow : base ≤ low := data.choose_spec.1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hsub : sectorNeighborhood W.S low δ δ ⊆ sectorNeighborhood W.S base ε ε :=
    sectorNeighborhood_mono W.S hlow hδε hδε
  have hU := sectorNeighborhood_isOpen W.S low δ δ
  have hA : G.Admissible low δ := G.admissible_mono
    (F.gauge_admissible e Y H₀ href) (hFb.trans hlow) hδ (hδε.trans hFε)
  let J₀ (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :=
    n04PositiveGeometry_actualControlledUnitHeight_joint F H₀ i
      (n04PositiveGeometry_actualControlledPhysicalHeight_joint F le_rfl Y H₀ href
        hb hε hεW hεone hFb hFε hflow hctx i (JS i))
  refine ⟨low, hlow, δ, hδ, hδε, hδhalf, fun η => ?_⟩
  let index (m : ℕ) (hm : G.Pos η m) := (G.n04PrincipalDivided_positive_index η hm).choose
  have hindex (m : ℕ) (hm : G.Pos η m) : e m = .inr (index m hm) :=
    (G.n04PrincipalDivided_positive_index η hm).choose_spec
  have hfields (m : ℕ) (hm : G.Pos η m) :=
    n04PositiveGeometry_controlledGauge_height_fields F e Y H₀ η m (index m hm) (hindex m hm)
  let J : ∀ m, G.Pos η m → SmoothDirections
      (sectorNeighborhood (G.S η) low δ δ ×ˢ unitStrip)
      (fun y : (StateDirections W.S × ℝ) × PolarPoint => G.atomFamily η .height y.1 m y.2) :=
    fun m hm => ((J₀ (index m hm)).restrict (hU.prod (isOpen_Ioo.prod isOpen_univ))
      (fun y hy => ⟨hsub hy.1, hy.2⟩)).congrOn
        (fun y _ => congrFun ((hfields m hm).2 y.1).symm y.2)
  have hcost := G.cost_nonneg η
  apply CurrentJetDataOn.of_positiveJointUnitPower hδ hδhalf hcost.2.2 hcost.2.1
    (fun z hz m hm => (G.positiveAtom_regular η hA .height trivial z hz m hm).2)
    (fun m _ => G.atomRef_eq_zero η .height m) J
  intro k hk
  let sd := data.choose_spec.2 k
  let shift := sd.choose
  refine ⟨shift, fun s => ?_⟩
  let bd := sd.choose_spec s
  let A := bd.choose
  refine ⟨A, zero_lt_one.trans_le bd.choose_spec.1, ?_⟩
  intro m hm z hz q hq R hR hzR n hn w hw v hv hvR hvS hv0 hv1
  have hzlow := n04Principal_parameter_low_le_one (S := W.S) hδhalf hz
  have hnpos : 0 < n := by have hs := w.arity_sum; omega
  have hpure := currentPhysicalHeight_pureDirections w v hv0 hv1
  have hb' := bd.choose_spec.2 (index m hm) (J₀ (index m hm)) z (hsub hz) hzlow q hq R hR
    hzR n hnpos hn w (by omega) v hpure (fun j => ⟨hv j, hvR j, hvS j⟩)
  have hvalue : |(J m hm).D n (z, q) v| = ‖(J₀ (index m hm)).D n (z, q) v‖ :=
    (Real.norm_eq_abs _).symm
  have hscalar : A * W.U.E0 (W.U.sample (X.cell (index m hm))) ^ A *
      parameterHeightWeight (W.U.H (W.U.sample (X.cell (index m hm))) ^ (3 / 4 : ℝ)) w.stateArity *
      R ^ (((w.angleArity + shift * w.stateArity : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) =
        A * W.U.E0 (W.U.sample ((G.V η).cell m)) ^ A *
          W.U.H (W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
          R ^ (((w.angleArity + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
    exact (currentPhysicalHeight_scalar A
      (W.U.E0 (W.U.sample (X.cell (index m hm))))
      (W.U.H (W.U.sample (X.cell (index m hm))) ^ (3 / 4 : ℝ))
      R w.angleArity shift s hk hw).trans
      (congrArg (fun cell : ℕ => A * W.U.E0 (W.U.sample cell) ^ A *
        W.U.H (W.U.sample cell) ^ (3 / 4 : ℝ) *
        R ^ (((w.angleArity + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)))
        (hfields m hm).1.symm)
  exact hvalue.trans_le (hb'.trans_eq hscalar)

end ContinuousFlexibility.Analysis
