import ContinuousFlexibility.Analysis.N04NegativeChartInteriorSectorControl
import ContinuousFlexibility.Analysis.N04NegativeChartInteriorInterpolation
import ContinuousFlexibility.Analysis.N04NegativeChartActualTransport
import ContinuousFlexibility.Analysis.N04NegativeGeometryFlowBounds

/-! Fractional interior bounds for the actual raw speed and its reference difference. -/

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

namespace N04RealizationStart

variable (W : N04RealizationStart) (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)

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
  have hHM : H ≤ M := by simpa only [Real.rpow_zero, mul_one] using
    hheight (W.negativeHalfSample e m side)
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)
  have hHL : H ≤ L := hHM.trans (le_max_right _ _)
  have hQ : 1 ≤ Q := by dsimp only [Q]; linarith only [apply_nonneg (p (s + loss)) z,
    apply_nonneg (p (s + loss)) w]
  have hzQ : p (s + loss) z ≤ Q := by dsimp only [Q]; linarith only [apply_nonneg (p (s + loss)) w]
  have hwQ : p (s + loss) w ≤ Q := by dsimp only [Q]; linarith only [apply_nonneg (p (s + loss)) z]
  let J := (G.regular (m, side)).parameter a b q hq
  have hraw (j : ℕ) (hj : j ≤ max 1 K) (y : Parameter W.S) (hy : y ∈ V)
      (hylow : p base y ≤ 1) (v : Fin j → Parameter W.S)
      (hv : ∀ i, p base (v i) ≤ 1) (hyQ : p (s + loss) y ≤ Q)
      (hvQ : ∀ i, p (s + loss) (v i) ≤ Q) :
      ‖J.D j y v‖ ≤ C * E ^ A * parameterHeightWeight H j *
        Q ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
    simpa only [one_pow, one_mul, sub_zero] using
      hbound (m, side) j hj a b hab q hq J y hy
        (by simpa only [sub_zero] using hylow) v hv Q hQ
        (by simpa only [sub_zero] using hyQ) hvQ
  have hzlow := n04NegativeGeometry_parameterGrading_le_one W.S base hhalf hz
  have hpoint := n04NegativeChart_joint_restricted_parameter
    (W.negativeOriginalMinusJointTower m) hU hΩ hc hV hsub k a b hz hqΩ J (fun _ => w)
  have hfirst := hraw k (hk.trans (le_max_right _ _)) z hz hzlow (fun _ => w)
    (fun _ => hw) hzQ (fun _ => hwQ)
  have hweight : parameterHeightWeight H k ≤ L := by
    unfold parameterHeightWeight
    split_ifs <;> assumption
  constructor
  · have h := hfirst.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hweight (by positivity)) (Real.rpow_nonneg (zero_le_one.trans hQ) _))
    simpa only [hpoint, Real.norm_eq_abs, jointMixedDiagonal, mul_assoc, mul_left_comm, mul_comm] using h
  · let Rd := n04Realization_jointMixedRegularity (W.negativeRawDefectJointTower m) hU hΩ hc
    let Jd := (Rd.parameter a b q hqΩ).restrict hV hsub
    let JD : SmoothDirections V (fun y =>
        mixedDerivative a b (minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (liftSectorParameter W.S W.C y))) q -
        mixedDerivative a b (minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (liftSectorParameter W.S W.C 0))) q) := Jd.congrOn (fun y hy => by
      have h := mixedDerivative_sub_of_contDiffOn hΩ
        ((W.negativeOriginalMinusJointTower m).spatial_value_contDiffOn hΩ y (hsub hy))
        ((W.negativeRawReferenceJointTower m).spatial_value_contDiffOn hΩ y (hsub hy)) a b hqΩ
      simpa only [liftSectorParameter, Prod.fst_zero, Prod.snd_zero,
        ZeroMemClass.coe_zero, add_zero] using h)
    have hJD := n04NegativeChart_raw_reference_difference J JD p base (s + loss)
      (sectorNeighborhood_convex W.S base ε ε) hzero hz hzlow (fun _ => w)
      (fun _ => hw) hzQ (fun _ => hwQ) (fun j hj hjpos y hy hylow v hv hyQ hvQ => by
        have hh := hraw j (hj.trans (max_le_max le_rfl hk)) y hy hylow v hv hyQ hvQ
        simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt hjpos)] using hh)
    have hd := n04NegativeChart_joint_restricted_parameter
      (W.negativeRawDefectJointTower m) hU hΩ hc hV hsub k a b hz hqΩ Jd (fun _ => w)
    have hCE : C * E ^ A * H ≤ (C * L) * E ^ A * H := by
      apply mul_le_mul_of_nonneg_right _ hH
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC0.le hL) (by positivity)
    have hh := hJD.trans (mul_le_mul_of_nonneg_right hCE (Real.rpow_nonneg (zero_le_one.trans hQ) _))
    change ‖Jd.D k z (fun _ => w)‖ ≤ _ at hh
    simpa only [hd, Real.norm_eq_abs, jointMixedDiagonal] using hh

end N04RealizationStart
end ContinuousFlexibility.Analysis
