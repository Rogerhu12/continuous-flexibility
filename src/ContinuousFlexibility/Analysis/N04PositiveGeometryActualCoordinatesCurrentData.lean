import ContinuousFlexibility.Analysis.N04PositiveGeometryActualCoordinateUnitBounds
import ContinuousFlexibility.Analysis.N04PositiveGeometryReferenceChartSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryReferenceInverseSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryCurrentJointPowers
import ContinuousFlexibility.Analysis.N04PositiveGeometryGaugeRegularity
import ContinuousFlexibility.Analysis.N04PrincipalPositiveIndex

/-!
# Current data for all four actual positive coordinates

The two actual transport prefixes determine one low neighborhood before
all derivative orders. Fixed reference composition, unit coordinates,
angular defects and the inverse radial width are evaluated in the stored
whole atlas, with its original component and material sample.
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

theorem n04PositiveGeometry_actualControlledCoordinates_currentData_of_transportWords
    {W : N04RealizationStart} {X : N04RealizationChoice W}
    (F : N04PositiveGeometryControlledFamily W X 3)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H₀)
    {base : ℕ} {ε : ℝ} (hε : 0 < ε) (hFb : F.base ≤ base) (hFε : ε ≤ F.ε)
    (JT : ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
          F.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C z.1) i z.2))
    (JS : ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
          F.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C z.1) i z.2))
    (hτ : N04PositiveGeometryTransportSamplePrefix F false base ε)
    (hσ : N04PositiveGeometryTransportSamplePrefix F true base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 / 2 ∧
      ∀ η : (W.S.height (3 / 4 : ℝ)).Space, ∀ inverse angle : Bool,
        (F.gauge e Y H₀).Data η ((F.gauge e Y H₀).Pos η) low δ
          ((F.gauge e Y H₀).atomFamily η (n04PositiveGeometry_coordinateAtom inverse angle))
          ((F.gauge e Y H₀).atomRef η (n04PositiveGeometry_coordinateAtom inverse angle)) := by
  classical
  let G := F.gauge e Y H₀
  let fd := n04PositiveGeometry_controlledReferenceChart_sample_prefix
    F Y H₀ href hmaterial hFb hFε JS hσ
  let id := n04PositiveGeometry_controlledReferenceInverse_sample_prefix
    F Y H₀ href hmaterial JT hτ
  let low := max fd.choose id.choose
  let δ := min ε (1 / 2)
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  have hfLow : fd.choose ≤ low := le_max_left _ _
  have hiLow : id.choose ≤ low := le_max_right _ _
  have hlow : base ≤ low := fd.choose_spec.1.trans hfLow
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hsub : sectorNeighborhood W.S low δ δ ⊆ sectorNeighborhood W.S base ε ε :=
    sectorNeighborhood_mono W.S hlow hδε hδε
  have hU := sectorNeighborhood_isOpen W.S base ε ε
  have hUnew := sectorNeighborhood_isOpen W.S low δ δ
  have hV : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hc := (sectorNeighborhood_convex W.S base ε ε).prod
    ((convex_Ioo (0 : ℝ) 1).prod convex_univ)
  have hA : G.Admissible low δ := G.admissible_mono
    (F.gauge_admissible e Y H₀ href) (hFb.trans hlow) hδ (hδε.trans hFε)
  let JC (inverse angle : Bool) (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :=
    n04PositiveGeometry_controlledReferenceComponent_joint F Y H₀ href inverse angle i (JT i) (JS i)
  let JU (inverse angle : Bool) (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :=
    n04PositiveGeometry_controlledCoordinate_joint F Y inverse angle i (JC inverse angle i)
  let RUnit (inverse angle : Bool) (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :=
    n04Realization_jointMixedRegularity (JU inverse angle i) hU hV hc
  let widthData := n04PositiveGeometry_controlledFamily_material_bounds F
  let Cw := widthData.choose
  have hCw : 1 ≤ Cw := widthData.choose_spec.1
  let C : ℝ := max 1 (W.D.b - W.D.a)
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨low, hlow, δ, hδ, hδε, hδhalf, fun η inverse angle => ?_⟩
  let index (m : ℕ) (hm : G.Pos η m) := (G.n04PrincipalDivided_positive_index η hm).choose
  have hindex (m : ℕ) (hm : G.Pos η m) : e m = .inr (index m hm) :=
    (G.n04PrincipalDivided_positive_index η hm).choose_spec
  have hfields (m : ℕ) (hm : G.Pos η m) :=
    n04PositiveGeometry_controlledGauge_coordinate_fields F e Y H₀ η m (index m hm) (hindex m hm)
  have hcost := G.cost_nonneg η
  cases inverse with
  | false =>
      let J : ∀ m, G.Pos η m → SmoothDirections
          (sectorNeighborhood (G.S η) low δ δ ×ˢ unitStrip)
          (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
            G.atomFamily η (n04PositiveGeometry_coordinateAtom false angle) z.1 m z.2) := fun m hm =>
        ((JU false angle (index m hm)).restrict (hUnew.prod hV)
          (fun z hz => ⟨hsub hz.1, hz.2⟩)).congrOn
          (fun z _ => congrFun ((hfields m hm).2 false angle z.1).symm z.2)
      apply CurrentJetDataOn.of_positiveJointUnitPower hδ hδhalf hcost.2.2 hcost.2.1
        (fun z hz m hm => (G.positiveAtom_regular η hA _
          (n04PositiveGeometry_coordinateAtom_isGeometry false angle) z hz m hm).2)
        (fun m _ => G.atomRef_eq_zero η _ m) J
      intro k hk
      let sd := fd.choose_spec.2 k
      let shift := sd.choose
      refine ⟨shift, fun s => ?_⟩
      let bd := sd.choose_spec s
      let A := bd.choose
      let B := max A (C ^ (k + s + 1) * A)
      have hB : 1 ≤ B := bd.choose_spec.1.trans (le_max_left _ _)
      refine ⟨B, zero_lt_one.trans_le hB, ?_⟩
      intro m hm z hz q hq R hR hzR n hn w hw v hv hvR hvS hv0 hv1
      let i := index m hm
      let E := W.U.E0 (W.U.sample (X.cell i))
      let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
      let t := R ^ (1 / (((s + shift * k : ℕ) : ℝ) + 1))
      have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
      have hH : 0 ≤ H := Real.rpow_nonneg
        (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
      have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
      have hzlow : p low z ≤ 1 := n04Principal_parameter_low_le_one (S := W.S) hδhalf hz
      have hfHigh : fd.choose + s + shift * k + 1 ≤ low + s + shift * k + 1 := by omega
      have hgeo := n04PositiveComponent_bounds
        ((n04b_profileGeometry_of_through03 W.through03).2.2.1.1.continuous_deriv (by simp)) i
      have hspan : |n04PositiveRight i - n04PositiveLeft i| ≤ C := by
        rw [abs_of_pos (sub_pos.mpr hgeo.2.1)]
        exact (sub_le_sub hgeo.2.2 hgeo.1).trans (le_max_right _ _)
      have hpoint : (n04PositiveLeft i + (n04PositiveRight i - n04PositiveLeft i) * q.1, q.2) ∈
          Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) := by
        refine ⟨⟨lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hgeo.2.1) hq.1.1), ?_⟩, mem_univ _⟩
        have h := mul_lt_of_lt_one_right (sub_pos.mpr hgeo.2.1) hq.1.2
        linarith only [h]
      have hnpos : 0 < n := by have := w.arity_sum; omega
      have hwpos : 0 < w.stateArity := hw.symm ▸ hk
      have hraw := n04PositiveGeometry_controlledForwardCoordinate_word_bound F Y angle i
        (JC false angle i) (JU false angle i) hC hspan
        (p low) (p (low + s + shift * k + 1)) (zero_le_one.trans hR) n w hwpos z (hsub hz) q hq
        (fun u huL huH huS hu0 hu1 => (Real.norm_eq_abs _).trans_le
          (bd.choose_spec.2 i angle (JC false angle i) z (hsub hz)
            ((hp hfLow z).trans hzlow) _ hpoint R hR ((hp hfHigh z).trans hzR) n hnpos (by omega)
            w hwpos hw.le u
            (fun j => by
              cases hj : w.isState j with
              | false => simpa only [hj, if_false] using hu0 j hj
              | true => simpa only [hj, if_true] using hu1 j hj)
            (fun j => ⟨(hp hfLow (u j).1).trans (huL j),
              (hp hfHigh (u j).1).trans (huH j), huS j⟩)))
        v hv hvR hvS hv0 hv1
      have hpack : C ^ n * (A * E ^ A) ≤ B * E ^ B := by
        have hcoef : C ^ n * A ≤ B :=
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (by omega))
            (zero_le_one.trans bd.choose_spec.1)).trans (le_max_right _ _)
        calc
          _ = (C ^ n * A) * E ^ A := by ring
          _ ≤ _ := mul_le_mul hcoef
            (Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _))
            (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
      have hout : |(JU false angle i).D n (z, q) v| ≤
          B * E ^ B * parameterHeightWeight H w.stateArity * t ^ (w.angleArity + shift * w.stateArity) :=
        hraw.trans (by
          calc
            _ = (C ^ n * (A * E ^ A)) * parameterHeightWeight H w.stateArity *
                t ^ (w.angleArity + shift * w.stateArity) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpack (parameterHeightWeight_nonneg hH _))
              (pow_nonneg (zero_le_one.trans ht) _))
      have htpow (d : ℕ) : t ^ d = R ^ ((d : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
        dsimp only [t]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
        congr 1
        ring
      have hscalar : B * E ^ B * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + shift * w.stateArity) =
          B * W.U.E0 (W.U.sample ((G.V η).cell m)) ^ B *
            W.U.H (W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
            R ^ (((w.angleArity + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
        rw [htpow, hw, (hfields m hm).1]
        simp only [parameterHeightWeight, Nat.ne_of_gt hk, if_false]
      exact hout.trans_eq hscalar
  | true =>
      let J : ∀ m, G.Pos η m → ∀ a b (q : unitStrip),
          SmoothDirections (sectorNeighborhood (G.S η) low δ δ)
            (fun z => mixedDerivative a b
              (G.atomFamily η (n04PositiveGeometry_coordinateAtom true angle) z m) q.val) := fun m hm a b q =>
        (((RUnit true angle (index m hm)).parameter a b q.val q.property).restrict hUnew hsub).congrOn
          (fun z _ => congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f q.val)
            ((hfields m hm).2 true angle z).symm)
      apply CurrentJetDataOn.of_positiveMixedUnitPower hδ hδhalf hcost.2.2 hcost.2.1
        (G.positiveAtom_regular η hA _ (n04PositiveGeometry_coordinateAtom_isGeometry true angle))
        (fun m _ => G.atomRef_eq_zero η _ m) J
      intro k hk
      let sd := id.choose_spec.2 k
      let shift := sd.choose
      refine ⟨shift, fun s => ?_⟩
      let bd := sd.choose_spec s
      let A := bd.choose
      let B := max 1 (max (Cw * A) (Cw + A))
      have hB : 1 ≤ B := le_max_left _ _
      refine ⟨B, zero_lt_one.trans_le hB, ?_⟩
      intro m hm z hz q a b hab R hR hzR v hv hvR
      let i := index m hm
      let E := W.U.E0 (W.U.sample (X.cell i))
      let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
      have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
      have hH : 0 ≤ H := Real.rpow_nonneg
        (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
      have hzlow : p low z ≤ 1 := n04Principal_parameter_low_le_one (S := W.S) hδhalf hz
      have hiHigh : id.choose + s + shift * k + 1 ≤ low + s + shift * k + 1 := by omega
      let RF := n04Realization_jointMixedRegularity (JC true angle i) hU isOpen_univ
        ((sectorNeighborhood_convex W.S base ε ε).prod convex_univ)
      let JP := RF.parameter a b q.val (mem_univ _)
      let JQ := (RUnit true angle i).parameter a b q.val q.property
      have heval := n04PositiveGeometry_controlledInverseCoordinate_parameter_identity F Y angle i
        (JC true angle i) a b q.val JP JQ hk (hsub hz) v
      have hraw := bd.choose_spec.2 i angle k hk le_rfl a b hab q.val q.property JP z (hsub hz)
        ((hp hiLow z).trans hzlow) v (fun j => (hp hiLow (v j)).trans (hv j)) R hR
        ((hp hiHigh z).trans hzR) (fun j => (hp hiHigh (v j)).trans (hvR j))
      let c : ℝ := if angle then 1 else (n04PositiveRight i - n04PositiveLeft i)⁻¹
      have hc : |c| ≤ Cw * E ^ Cw := by
        cases angle
        · exact widthData.choose_spec.2.span_inverse i
        · simpa only [c, if_true, abs_one] using
            one_le_mul_of_one_le_of_one_le hCw
              (Real.one_le_rpow hE (zero_le_one.trans hCw))
      have hpack : (Cw * E ^ Cw) * (A * E ^ A) ≤ B * E ^ B := by
        calc
          _ = (Cw * A) * E ^ (Cw + A) := by
            rw [Real.rpow_add (zero_lt_one.trans_le hE)]
            ring
          _ ≤ _ := mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
            (Real.rpow_le_rpow_of_exponent_le hE ((le_max_right _ _).trans (le_max_right _ _)))
            (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
      have hout : |JQ.D k z v| ≤ B * E ^ B * parameterHeightWeight H k *
          R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
        calc
          _ = |c| * |JP.D k z v| := (congrArg abs heval).trans (abs_mul _ _)
          _ ≤ (Cw * E ^ Cw) * (A * E ^ A * parameterHeightWeight H k *
              R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1))) :=
            mul_le_mul hc hraw (abs_nonneg _)
              (mul_nonneg (zero_le_one.trans hCw) (Real.rpow_nonneg (zero_le_one.trans hE) _))
          _ = ((Cw * E ^ Cw) * (A * E ^ A)) * parameterHeightWeight H k *
              R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpack (parameterHeightWeight_nonneg hH _))
            (Real.rpow_nonneg (zero_le_one.trans hR) _)
      have hscalar : B * E ^ B * parameterHeightWeight H k *
          R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) =
          B * W.U.E0 (W.U.sample ((G.V η).cell m)) ^ B *
            W.U.H (W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
            R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
        rw [(hfields m hm).1]
        simp only [parameterHeightWeight, Nat.ne_of_gt hk, if_false]
      exact hout.trans_eq hscalar

end ContinuousFlexibility.Analysis
