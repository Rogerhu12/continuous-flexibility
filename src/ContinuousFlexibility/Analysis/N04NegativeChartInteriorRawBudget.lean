module

public import ContinuousFlexibility.Analysis.N04NegativeChartInteriorSectorControl
public import ContinuousFlexibility.Analysis.N04NegativeChartInteriorInterpolation
public import ContinuousFlexibility.Analysis.N04NegativeChartActualTransport
public import ContinuousFlexibility.Analysis.N04NegativeGeometryFlowBounds

/-! Fractional interior bounds for the actual raw speed and its reference difference. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

theorem n04NegativeChart_joint_restricted_parameter
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U V : Set E} {Ω : Set PolarPoint} {f : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ Ω) f) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hc : Convex ℝ (U ×ˢ Ω)) (hV : IsOpen V) (hsub : V ⊆ U)
    (n a b : ℕ) {x : E} (hx : x ∈ V) {q : PolarPoint} (hq : q ∈ Ω)
    (P : SmoothDirections V (fun y => mixedDerivative a b (fun p => f (y, p)) q))
    (v : Fin n → E) :
    P.D n x v = mixedDerivative a b (fun p => J.D n (x, p) (fun i => (v i, 0))) q := by
  let R := n04Realization_jointMixedRegularity J hU hΩ hc
  have he := congrArg (fun A : E [×n]→L[ℝ] ℝ => A v)
    (P.unique ((R.parameter a b q hq).restrict hV hsub) n x hx)
  exact he.trans (n04Realization_mixedParameter_eq_joint J hU hΩ hc
    a b n x (hsub hx) q hq (R.parameter a b q hq) v)

private theorem interior_raw_remove_height
    {x C E A H L R : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hL : 1 ≤ L) (hHL : H ≤ L) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ C * E ^ A * parameterHeightWeight H k * R) :
    ‖x‖ ≤ (C * L) * E ^ A * R := by
  have hw : parameterHeightWeight H k ≤ L := by
    unfold parameterHeightWeight
    split_ifs <;> assumption
  have h := hx.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw (mul_nonneg hC (Real.rpow_nonneg hE A))) hR)
  exact h.trans_eq (by ring)

private theorem interior_raw_difference_bound
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {f g : X → ℝ}
    (J : SmoothDirections U f) (Jd : SmoothDirections U g)
    (heq : ∀ y ∈ U, g y = f y - f 0)
    (p : ℕ → Seminorm ℝ X) (base high : ℕ)
    (hc : Convex ℝ U) (hzero : (0 : X) ∈ U)
    {k K : ℕ} (hk : k ≤ K) {x : X} (hx : x ∈ U) (hlow : p base x ≤ 1)
    (v : Fin k → X) (hv : ∀ i, p base (v i) ≤ 1)
    {Q M H R : ℝ} (hxQ : p high x ≤ Q) (hvQ : ∀ i, p high (v i) ≤ Q)
    (hb : ∀ j : ℕ, j ≤ max 1 K → ∀ y ∈ U, p base y ≤ 1 →
      ∀ u : Fin j → X, (∀ i, p base (u i) ≤ 1) → p high y ≤ Q →
        (∀ i, p high (u i) ≤ Q) →
          ‖J.D j y u‖ ≤ M * parameterHeightWeight H j * R) :
    ‖Jd.D k x v‖ ≤ M * H * R := by
  let JD := Jd.congrOn heq
  have h := n04NegativeChart_raw_reference_difference J JD p base high
    (k := k) (x := x) (R := Q) (M := M * H * R)
    hc hzero hx hlow v hv hxQ hvQ (fun j hj hjpos y hy hylow u hu hyQ huQ => by
      have hh := hb j (hj.trans (max_le_max le_rfl hk)) y hy hylow u hu hyQ huQ
      simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt hjpos)] using hh)
  exact h

namespace N04RealizationStart

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

local instance interiorRaw_parameterTopology (S : PhysicalSpacesData) :
    TopologicalSpace (Parameter S) := inferInstance

local instance interiorRaw_parameterAddGroup (S : PhysicalSpacesData) :
    IsTopologicalAddGroup (Parameter S) :=
  (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup

local instance interiorRaw_parameterSMul (S : PhysicalSpacesData) :
    ContinuousSMul ℝ (Parameter S) :=
  (n07aParameterGrading_withSeminorms S).continuousSMul

variable (W : N04RealizationStart) (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)

set_option backward.isDefEq.respectTransparency true in
set_option diagnostics true in
/-- Both estimates use the literal full-component towers. The raw
reference difference keeps one height factor also at state order zero. -/
theorem negativeInterior_raw_fractional
    {base loss : ℕ} {ε : ℝ} (hb : W.base ≤ base)
    (hε : 0 < ε) (hεW : ε ≤ W.ε) (hhalf : ε ≤ 1 / 2)
    (hρ : ∀ m side, 0 < ρ m side)
    (G : W.NegativeInteriorSpeedControl e ρ base loss ε) (K s : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ m side k, k ≤ K →
      ∀ a b, a + b ≤ s → ∀ q ∈ W.negativeInteriorPhysicalDomain ρ (m, side),
      ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ w : Parameter W.S,
      parameterGrading W.S base w ≤ 1 →
      let Q := 1 + parameterGrading W.S (s + loss) z + parameterGrading W.S (s + loss) w
      let E := W.T.E0 (W.negativeHalfSample e m side)
      let H := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
      |jointMixedDiagonal (W.negativeOriginalMinusJointTower m) k a b z w q| ≤
        C * E ^ A * Q ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) ∧
      |jointMixedDiagonal (W.negativeRawDefectJointTower m) k a b z w q| ≤
        C * E ^ A * H * Q ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  have hex := G.bounds (max 1 K) s
  let C : ℝ := hex.choose
  let A : ℝ := hex.choose_spec.choose
  have hC := hex.choose_spec.choose_spec.1
  have hA := hex.choose_spec.choose_spec.2.1
  have hbound := hex.choose_spec.choose_spec.2.2
  have hheightExists := materialHeight_E0_weight_bounded W.hT
    (γ := (3 / 4 : ℝ)) (by norm_num) 0
  let M : ℝ := hheightExists.choose
  have hheight := hheightExists.choose_spec.2
  let L : ℝ := max 1 M
  have hL : 1 ≤ L := le_max_left _ _
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  refine ⟨C * L, A, mul_pos hC0 (zero_lt_one.trans_le hL), hA, ?_⟩
  intro m side k hk a b hab q hq z hz w hw
  let U : Set (Parameter W.S) := sectorNeighborhood W.S W.base W.ε W.ε
  let V : Set (Parameter W.S) := sectorNeighborhood W.S base ε ε
  let Ω : Set PolarPoint := Ioo (W.C.left m) (W.C.right m) ×ˢ univ
  let p : ℕ → Seminorm ℝ (Parameter W.S) := parameterGrading W.S
  let H : ℝ := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
  let E : ℝ := W.T.E0 (W.negativeHalfSample e m side)
  let Q : ℝ := 1 + p (s + loss) z + p (s + loss) w
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S W.base W.ε W.ε
  have hV : IsOpen V := sectorNeighborhood_isOpen W.S base ε ε
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  have hc : Convex ℝ (U ×ˢ Ω) := (sectorNeighborhood_convex W.S W.base W.ε W.ε).prod
    ((convex_Ioo _ _).prod (convex_univ : Convex ℝ (univ : Set ℝ)))
  have hsub : V ⊆ U := sectorNeighborhood_mono W.S hb hεW hεW
  have hqΩ : q ∈ Ω := W.negativeInteriorPhysicalDomain_subset ρ hρ (m, side) hq
  have hzero : (0 : Parameter W.S) ∈ V :=
    ⟨(sectorGrading W.S base).map_zero'.trans_lt hε, (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hE : 0 ≤ E := zero_le_one.trans (W.floor _)
  have hHM : H ≤ M := by
    simpa only [H, M, Real.rpow_zero, mul_one] using
      hheight (W.negativeHalfSample e m side)
        (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)
  have hHL : H ≤ L := hHM.trans (le_max_right _ _)
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (s + loss)) z, apply_nonneg (p (s + loss)) w]
  have hzQ : p (s + loss) z ≤ Q := by dsimp only [Q]; linarith only [apply_nonneg (p (s + loss)) w]
  have hwQ : p (s + loss) w ≤ Q := by dsimp only [Q]; linarith only [apply_nonneg (p (s + loss)) z]
  let J := (G.regular (m, side)).parameter a b q hq
  have hraw (j : ℕ) (hj : j ≤ max 1 K) (y : Parameter W.S) (hy : y ∈ V)
      (hylow : p base y ≤ 1) (v : Fin j → Parameter W.S)
      (hv : ∀ i, p base (v i) ≤ 1) (hyQ : p (s + loss) y ≤ Q)
      (hvQ : ∀ i, p (s + loss) (v i) ≤ Q) :
      ‖J.D j y v‖ ≤ C * E ^ A * parameterHeightWeight H j *
        Q ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
    have hh :=
      hbound (m, side) j hj a b hab q hq J y hy
        (by simpa only [sub_zero] using hylow) v hv Q hQ
        (by simpa only [sub_zero] using hyQ) hvQ
    change (1 : ℝ) ^ a * ‖J.D j y v‖ ≤ C * E ^ A * parameterHeightWeight H j *
      Q ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) at hh
    simpa only [one_pow, one_mul] using hh
  have hzlow := n04NegativeGeometry_parameterGrading_le_one W.S base hhalf hz
  have hpoint := n04NegativeChart_joint_restricted_parameter
    (W.negativeOriginalMinusJointTower m) hU hΩ hc hV hsub k a b hz hqΩ J (fun _ => w)
  have hfirst := hraw k (hk.trans (le_max_right _ _)) z hz hzlow (fun _ => w)
    (fun _ => hw) hzQ (fun _ => hwQ)
  change |jointMixedDiagonal (W.negativeOriginalMinusJointTower m) k a b z w q| ≤
      (C * L) * E ^ A * Q ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) ∧
    |jointMixedDiagonal (W.negativeRawDefectJointTower m) k a b z w q| ≤
      (C * L) * E ^ A * H * Q ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
  constructor
  · have h := interior_raw_remove_height hC0.le hE hL hHL
      (Real.rpow_nonneg (zero_le_one.trans hQ) _) hfirst
    exact ((congrArg abs hpoint.symm).trans (Real.norm_eq_abs _).symm).trans_le h
  · let Rd := n04Realization_jointMixedRegularity (W.negativeRawDefectJointTower m) hU hΩ hc
    let Jd := (Rd.parameter a b q hqΩ).restrict hV hsub
    have heq (y : Parameter W.S) (hy : y ∈ V) :
        mixedDerivative a b (fun p =>
          minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
            (liftSectorParameter W.S W.C y)) p -
          minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
            (W.C.referenceState, 0)) p) q =
        mixedDerivative a b (minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (liftSectorParameter W.S W.C y))) q -
        mixedDerivative a b (minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (liftSectorParameter W.S W.C 0))) q := by
      have h := mixedDerivative_sub_of_contDiffOn hΩ
        ((W.negativeOriginalMinusJointTower m).spatial_value_contDiffOn hΩ y (hsub hy))
        ((W.negativeRawReferenceJointTower m).spatial_value_contDiffOn hΩ y (hsub hy)) a b hqΩ
      simpa only [liftSectorParameter, Prod.fst_zero, Prod.snd_zero,
        ZeroMemClass.coe_zero, add_zero] using h
    have hJD : ‖Jd.D k z (fun _ => w)‖ ≤
        (C * E ^ A) * H * Q ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
      interior_raw_difference_bound (X := Parameter W.S) (U := V) J Jd heq p base (s + loss)
      (M := C * E ^ A) (H := H) (Q := Q)
      (R := Q ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)))
      (sectorNeighborhood_convex W.S base ε ε) hzero hk hz hzlow
      (fun _ => w) (fun _ => hw) hzQ (fun _ => hwQ) hraw
    have hd := n04NegativeChart_joint_restricted_parameter
      (W.negativeRawDefectJointTower m) hU hΩ hc hV hsub k a b hz hqΩ Jd (fun _ => w)
    have hCE : C * E ^ A * H ≤ (C * L) * E ^ A * H := by
      apply mul_le_mul_of_nonneg_right _ hH
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC0.le hL) (by positivity)
    have hh := hJD.trans (mul_le_mul_of_nonneg_right hCE (Real.rpow_nonneg (zero_le_one.trans hQ) _))
    change ‖Jd.D k z (fun _ => w)‖ ≤ _ at hh
    exact ((congrArg abs hd.symm).trans (Real.norm_eq_abs _).symm).trans_le hh

end N04RealizationStart
end ContinuousFlexibility.Analysis
