import ContinuousFlexibility.Analysis.N04NegativeChartInteriorRawBudget
import ContinuousFlexibility.Analysis.N04NegativeChartInteriorMaterial
import ContinuousFlexibility.Analysis.N04NegativeChartTransportStateBudget
import ContinuousFlexibility.Analysis.N04NegativeChartRadialStateBounds
import ContinuousFlexibility.Analysis.JointMixedRadialScalar

/-! The genuine interior transport system with one common state-order budget. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

structure NegativeInteriorEvaluation (S : PhysicalSpacesData) where
  component : ℕ
  side : Bool
  state : Parameter S
  direction : Parameter S
  point : PolarPoint

namespace N04RealizationStart

set_option backward.isDefEq.respectTransparency true

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
  interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

variable (W : N04RealizationStart)

def negativeInteriorJet
    {f : ℕ → Parameter W.S × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
      (Ioo (W.C.left m) (W.C.right m) ×ˢ univ)) (f m))
    (k a b : ℕ) (x : NegativeInteriorEvaluation W.S) : ℝ :=
  jointMixedDiagonal (J x.component) k a b x.state x.direction x.point

def negativeInteriorBudgetDomain (ρ : ℕ → Bool → ℝ) (base : ℕ) (ε : ℝ) :
    Set (NegativeInteriorEvaluation W.S) := {x |
  x.state ∈ sectorNeighborhood W.S base ε ε ∧
  parameterGrading W.S base x.state ≤ 1 ∧ parameterGrading W.S base x.direction ≤ 1 ∧
  x.point ∈ W.negativeInteriorPhysicalDomain ρ (x.component, x.side)}

abbrev NegativeInteriorJetBound (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)
    (base : ℕ) (ε : ℝ) (K N D degree charge : ℕ)
    (f : NegativeInteriorEvaluation W.S → ℝ) : Prop :=
  HasWeightedJetBound
    (fun x => W.T.E0 (W.negativeHalfSample e x.component x.side))
    (fun x => W.T.H (W.negativeHalfSample e x.component x.side) ^ (3 / 4 : ℝ))
    (fun x => 1 + parameterGrading W.S (N + K * D + base + 1) x.state +
      parameterGrading W.S (N + K * D + base + 1) x.direction)
    (W.negativeInteriorBudgetDomain ρ base ε) ((N + K * D : ℕ) + 1 : ℝ) degree charge f

private theorem interiorAngular
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ) (hρ : ∀ m side, 0 < ρ m side)
    {base B D₀ D K N : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : ε ≤ W.ε)
    (hB : B ≤ base) (hD : D₀ ≤ D)
    {f : ℕ → Parameter W.S × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
      (Ioo (W.C.left m) (W.C.right m) ×ˢ univ)) (f m))
    (weight : ℕ → ℝ) (charge : ℕ)
    (hangular : ∀ N k : ℕ, k ≤ K → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m z, z ∈ sectorNeighborhood W.S W.base W.ε W.ε →
      ∀ w : Parameter W.S, parameterGrading W.S B z ≤ 1 →
      parameterGrading W.S B w ≤ 1 → ∀ q : PolarPoint,
      q.1 ∈ Ioo (W.C.left m) (W.C.right m) →
      |jointMixedDiagonal (J m) k 0 b z w q| ≤ C * weight m *
        (1 + parameterGrading W.S (N + K * D₀ + B + 1) z +
          parameterGrading W.S (N + K * D₀ + B + 1) w) ^
          (((b + k * D₀ : ℕ) : ℝ) / ((N + K * D₀ : ℕ) + 1 : ℝ)))
    {C P : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hweight : ∀ m side, weight m ≤ C * W.T.E0 (W.negativeHalfSample e m side) ^ P *
      (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) ^ charge)
    (k b : ℕ) (hk : k ≤ K) (hbn : b ≤ N) :
    W.NegativeInteriorJetBound e ρ base ε K N D (k * D + b) charge
      (W.negativeInteriorJet J k 0 b) := by
  obtain ⟨C₀, hC₀, hc⟩ := hangular (N + K * (D - D₀)) k hk b (by omega)
  refine ⟨C₀ * C, P, mul_nonneg hC₀ hC, hP, fun x hx => ?_⟩
  have hq := W.negativeInteriorPhysicalDomain_subset ρ hρ (x.component, x.side) hx.2.2.2
  have hg := hc x.component x.state (sectorNeighborhood_mono W.S hb hε hε hx.1)
    x.direction ((sectorPairGrading_monotone W.S hB x.state).trans hx.2.1)
    ((sectorPairGrading_monotone W.S hB x.direction).trans hx.2.2.1) x.point hq.1
  have hp := n04NegativeChart_angular_scale_mono (parameterGrading W.S)
    (sectorPairGrading_monotone W.S) hB hD x.state x.direction (K := K) (N := N) (k := k) (b := b)
  have hH : 0 ≤ W.T.H (W.negativeHalfSample e x.component x.side) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hE : 0 ≤ W.T.E0 (W.negativeHalfSample e x.component x.side) :=
    zero_le_one.trans (W.floor _)
  have h := hg.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (hweight x.component x.side) hC₀) hp
    (by positivity) (by positivity))
  simpa only [negativeInteriorJet, Nat.add_comm b (k * D), mul_assoc] using h

set_option diagnostics true in
/-- The actual corrected first integral has one fixed low order and
one height charge on every material-controlled interior. The prefix
retains its fractional powers for subsequent nonlinear compositions. -/
theorem negativeInterior_firstIntegral_fractional
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (hρb : ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side,
      (ρ m side)⁻¹ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ A) :
    ∃ base : ℕ, ∃ ε : ℝ, W.base ≤ base ∧ 0 < ε ∧ ε ≤ min W.ε (1 / 2 : ℝ) ∧
      ∀ K : ℕ, ∃ D : ℕ, ∀ N k a b : ℕ, k ≤ K → a + b ≤ N →
        W.NegativeInteriorJetBound e ρ base ε K N D (k * D + a + b) 1
          (W.negativeInteriorJet W.negativeFirstIntegralDefectJointTower k a b) := by
  have hrawExists := W.negativeInterior_stable_speedControl e ρ hρ hρb
  let Br : ℕ := hrawExists.choose
  let ε : ℝ := hrawExists.choose_spec.choose
  let loss : ℕ := hrawExists.choose_spec.choose_spec.choose
  have hBr := hrawExists.choose_spec.choose_spec.choose_spec.1
  have hε := hrawExists.choose_spec.choose_spec.choose_spec.2.1
  have hεW := hrawExists.choose_spec.choose_spec.choose_spec.2.2.1
  have hG := hrawExists.choose_spec.choose_spec.choose_spec.2.2.2
  have hAExists := W.negativeInverseSlope_angular_stateBudget
  let BA : ℕ := hAExists.choose
  have hBA := hAExists.choose_spec
  have hZExists := W.negativePulledCorrection_angular_stateBudget
  let BZ : ℕ := hZExists.choose
  have hBZ := hZExists.choose_spec
  have hFExists := W.negativeFirstIntegralDefect_angular_stateBudget
  let BF : ℕ := hFExists.choose
  have hBF := hFExists.choose_spec
  let base : ℕ := Br + loss + BA + BZ + BF
  have hbase : W.base ≤ base := hBr.trans (by dsimp only [base]; omega)
  let G := Classical.choice (hG base (by dsimp only [base]; omega) ε hε le_rfl)
  have hheightExists := W.negativeCircleSample_half_height e
  let CH : ℝ := hheightExists.choose
  let PH : ℝ := hheightExists.choose_spec.choose
  have hCH := hheightExists.choose_spec.choose_spec.1
  have hPH := hheightExists.choose_spec.choose_spec.2.1
  have hheight := hheightExists.choose_spec.choose_spec.2.2
  have hupperExists := materialSample_H_M_envelope W.hT W.radial.1
    (γ := (3 / 4 : ℝ)) (by norm_num) 0
  let MH : ℝ := hupperExists.choose
  have hMH := hupperExists.choose_spec.1
  have hupper := hupperExists.choose_spec.2
  refine ⟨base, ε, hbase, hε, hεW, fun K => ?_⟩
  have hDAExists := hBA K
  let DA := hDAExists.choose
  have hDA := hDAExists.choose_spec
  have hDZExists := hBZ K
  let DZ := hDZExists.choose
  have hDZ := hDZExists.choose_spec
  have hDFExists := hBF K
  let DF := hDFExists.choose
  have hDF := hDFExists.choose_spec
  let D : ℕ := DA + DZ + DF
  refine ⟨D, fun N => ?_⟩
  let Ω : Set (NegativeInteriorEvaluation W.S) := W.negativeInteriorBudgetDomain ρ base ε
  let E : NegativeInteriorEvaluation W.S → ℝ := fun x =>
    W.T.E0 (W.negativeHalfSample e x.component x.side)
  let H : NegativeInteriorEvaluation W.S → ℝ := fun x =>
    W.T.H (W.negativeHalfSample e x.component x.side) ^ (3 / 4 : ℝ)
  let Q : NegativeInteriorEvaluation W.S → ℝ := fun x =>
    1 + parameterGrading W.S (N + K * D + base + 1) x.state +
      parameterGrading W.S (N + K * D + base + 1) x.direction
  let d : ℝ := ((N + K * D : ℕ) + 1 : ℝ)
  let A := W.negativeInteriorJet W.negativeInverseSlopeJointTower
  let Z := W.negativeInteriorJet W.negativePulledCorrectionJointTower
  let L := W.negativeInteriorJet W.negativeOriginalMinusJointTower
  let C := W.negativeInteriorJet W.negativeCutoffDerivativeJointTower
  let T := W.negativeInteriorJet W.negativeMinusJointTower
  let Ld := W.negativeInteriorJet W.negativeRawDefectJointTower
  let F := W.negativeInteriorJet W.negativeFirstIntegralDefectJointTower
  let B := W.negativeInteriorJet W.negativeTransportForcingJointTower
  have hE (x : NegativeInteriorEvaluation W.S) (_ : x ∈ Ω) : 1 ≤ E x := W.floor _
  have hH (x : NegativeInteriorEvaluation W.S) (_ : x ∈ Ω) : 0 ≤ H x :=
    Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hQ (x : NegativeInteriorEvaluation W.S) (_ : x ∈ Ω) : 1 ≤ Q x := by
    dsimp only [Q]
    linarith only [apply_nonneg (parameterGrading W.S (N + K * D + base + 1)) x.state,
      apply_nonneg (parameterGrading W.S (N + K * D + base + 1)) x.direction]
  have hd : 0 < d := by dsimp only [d]; positivity
  have hs (x : NegativeInteriorEvaluation W.S) (hx : x ∈ Ω) :
      x.state ∈ sectorNeighborhood W.S W.base W.ε W.ε :=
    sectorNeighborhood_mono W.S hbase (hεW.trans (min_le_left _ _))
      (hεW.trans (min_le_left _ _)) hx.1
  have hq (x : NegativeInteriorEvaluation W.S) (hx : x ∈ Ω) :
      x.point ∈ Ioo (W.C.left x.component) (W.C.right x.component) ×ˢ (univ : Set ℝ) :=
    W.negativeInteriorPhysicalDomain_subset ρ (fun m side => (hρ m side).1) _ hx.2.2.2
  have hU : IsOpen (sectorNeighborhood W.S W.base W.ε W.ε) :=
    sectorNeighborhood_isOpen W.S W.base W.ε W.ε
  have hc (m : ℕ) : Convex ℝ (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
      (Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ))) :=
    (sectorNeighborhood_convex W.S W.base W.ε W.ε).prod
      ((convex_Ioo _ _).prod (convex_univ : Convex ℝ (univ : Set ℝ)))
  have hA0 (n b : ℕ) (hn : n ≤ K) (hb : b ≤ N) :
      HasWeightedJetBound E H Q Ω d (n * D + b) 0 (A n 0 b) :=
    W.interiorAngular e ρ (fun m side => (hρ m side).1) hbase (hεW.trans (min_le_left _ _))
      (by dsimp only [base]; omega) (by dsimp only [D]; omega)
      W.negativeInverseSlopeJointTower (fun _ => 1) 0 (hDA 1 zero_le_one)
      (C := 1) (P := 0) zero_le_one le_rfl
      (fun _ _ => by simp only [Real.rpow_zero, pow_zero, mul_one, le_refl]) n b hn hb
  have hZ0 (c : Fin 2) (n b : ℕ) (hn : n ≤ K) (hb : b ≤ N) :
      HasWeightedJetBound E H Q Ω d (n * D + b) c.val (Z n 0 b) := by
    fin_cases c
    · exact W.interiorAngular e ρ (fun m side => (hρ m side).1) hbase (hεW.trans (min_le_left _ _))
        (by dsimp only [base]; omega) (by dsimp only [D]; omega)
        W.negativePulledCorrectionJointTower (fun m => W.T.H (W.T.sample m) ^ (3 / 4 : ℝ))
        0 (hDZ 1 zero_le_one) hMH.le (P := 0) le_rfl
        (fun m _ => by simpa only [Real.rpow_zero, pow_zero, mul_one] using hupper m) n b hn hb
    · exact W.interiorAngular e ρ (fun m side => (hρ m side).1) hbase (hεW.trans (min_le_left _ _))
        (by dsimp only [base]; omega) (by dsimp only [D]; omega)
        W.negativePulledCorrectionJointTower (fun m => W.T.H (W.T.sample m) ^ (3 / 4 : ℝ))
        1 (hDZ 1 zero_le_one) hCH.le hPH
        (fun m side => by simpa only [pow_one] using hheight m side) n b hn hb
  have hF0 (n b : ℕ) (hn : n ≤ K) (hb : b ≤ N) :
      HasWeightedJetBound E H Q Ω d (n * D + b) 1 (F n 0 b) :=
    W.interiorAngular e ρ (fun m side => (hρ m side).1) hbase (hεW.trans (min_le_left _ _))
      (by dsimp only [base]; omega) (by dsimp only [D]; omega)
      W.negativeFirstIntegralDefectJointTower (fun m => W.T.H (W.T.sample m) ^ (3 / 4 : ℝ))
      1 (hDF 1 zero_le_one) hCH.le hPH
      (fun m side => by simpa only [pow_one] using hheight m side) n b hn hb
  have hrawBound := W.negativeInterior_raw_fractional e ρ hbase hε
    (hεW.trans (min_le_left _ _)) (hεW.trans (min_le_right _ _))
    (fun m side => (hρ m side).1) G K (N + K * D)
  let Cr := hrawBound.choose
  let Ar := hrawBound.choose_spec.choose
  have hCr := hrawBound.choose_spec.choose_spec.1
  have hAr := hrawBound.choose_spec.choose_spec.2.1
  have hr := hrawBound.choose_spec.choose_spec.2.2
  have hraw (n a b : ℕ) (hn : n ≤ K) (hab : a + b ≤ N) :
      HasWeightedJetBound E H Q Ω d (n * D + a + b) 0 (L n a b) ∧
      HasWeightedJetBound E H Q Ω d (n * D + a + b) 1 (Ld n a b) := by
    have hp (x : NegativeInteriorEvaluation W.S) (hx : x ∈ Ω) :
        (1 + parameterGrading W.S (N + K * D + loss) x.state +
          parameterGrading W.S (N + K * D + loss) x.direction) ^ (((a + b : ℕ) : ℝ) / d) ≤
          Q x ^ (((a + b : ℕ) : ℝ) / d) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact add_le_add (add_le_add le_rfl
        (sectorPairGrading_monotone W.S (by dsimp only [base]; omega) x.state))
        (sectorPairGrading_monotone W.S (by dsimp only [base]; omega) x.direction)
    have hpair (x : NegativeInteriorEvaluation W.S) (hx : x ∈ Ω) :=
      hr x.component x.side n hn a b (by omega) x.point hx.2.2.2 x.state hx.1
        x.direction hx.2.2.1
    constructor
    · apply HasWeightedJetBound.monoDegree (hW := hE) (hH := hH) (hQ := hQ)
        (hdenom := hd) (hde := show a + b ≤ n * D + a + b by omega)
      refine ⟨Cr, Ar, hCr.le, hAr, fun x hx => ?_⟩
      simpa only [pow_zero, mul_one] using ((hpair x hx).1.trans
        (mul_le_mul_of_nonneg_left (hp x hx)
          (mul_nonneg hCr.le (Real.rpow_nonneg (zero_le_one.trans (hE x hx)) _))))
    · apply HasWeightedJetBound.monoDegree (hW := hE) (hH := hH) (hQ := hQ)
        (hdenom := hd) (hde := show a + b ≤ n * D + a + b by omega)
      refine ⟨Cr, Ar, hCr.le, hAr, fun x hx => ?_⟩
      simpa only [pow_one] using ((hpair x hx).2.trans
        (mul_le_mul_of_nonneg_left (hp x hx)
          (mul_nonneg (mul_nonneg hCr.le (Real.rpow_nonneg (zero_le_one.trans (hE x hx)) _))
            (hH x hx))))
  have hC (n a b : ℕ) (_ : n ≤ K) (_ : a + b ≤ N) :
      HasWeightedJetBound E H Q Ω d (n * D) 0 (C n a b) := by
    have hcutExists := W.negativeCutoff_half_material e (a + 1)
    let Cc := hcutExists.choose
    let Ac := hcutExists.choose_spec.choose
    have hCc := hcutExists.choose_spec.choose_spec.1
    have hAc := hcutExists.choose_spec.choose_spec.2.1
    have hcut := hcutExists.choose_spec.choose_spec.2.2
    apply HasWeightedJetBound.monoDegree (hW := hE) (hH := hH) (hQ := hQ)
      (hdenom := hd) (hde := Nat.zero_le (n * D))
    refine ⟨Cc, Ac, hCc.le, hAc, fun x hx => ?_⟩
    have hh := jointMixedDiagonal_radial_deriv_abs_le
      (W.negativeCutoffDerivativeJointTower x.component) hU (isOpen_Ioo.prod isOpen_univ)
      (hc x.component) n a b x.state x.direction (hs x hx) (hq x hx) hCc.le
      (zero_le_one.trans (hE x hx)) (hcut x.component x.side x.point.1)
    simpa only [C, negativeInteriorJet, pow_zero, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one] using hh
  have hT (n a b : ℕ) (_ : n ≤ K) (_ : a + b ≤ N)
      (x : NegativeInteriorEvaluation W.S) (hx : x ∈ Ω) :
      T n a b x = L n a b x + diagonalJetProduct (diagonalJetProduct C A) Z n a b x := by
    simpa only [T, L, C, A, Z, negativeInteriorJet, diagonalJetProduct] using
      W.negativeTransport_speed_recurrence x.component n a b x.state x.direction (hs x hx) (hq x hx)
  have haz := n04NegativeChart_weighted_transport_stateBudget K N D hE hH hQ hd
    L C A T (fun _ => Z) (fun n a b hn hab => (hraw n a b hn hab).1) hC hA0 hZ0 hT
    (fun n a b _ _ x hx => by
      simpa only [A, L, negativeInteriorJet, diagonalJetProduct] using
        W.negativeTransport_slope_recurrence x.component n a b x.state x.direction (hs x hx) (hq x hx))
    (fun _ n a b _ _ x hx => by
      simpa only [Z, T, negativeInteriorJet, diagonalJetProduct] using
        W.negativeTransport_residual_recurrence x.component n a b x.state x.direction (hs x hx) (hq x hx))
  have product (X Y : ℕ → ℕ → ℕ → NegativeInteriorEvaluation W.S → ℝ) (cX cY : ℕ)
      (hX : ∀ n a b, n ≤ K → a + b ≤ N → HasWeightedJetBound E H Q Ω d (n * D + a + b) cX (X n a b))
      (hY : ∀ n a b, n ≤ K → a + b ≤ N → HasWeightedJetBound E H Q Ω d (n * D + a + b) cY (Y n a b))
      (n a b : ℕ) (hn : n ≤ K) (hab : a + b ≤ N) :
      HasWeightedJetBound E H Q Ω d (n * D + a + b) (cX + cY) (diagonalJetProduct X Y n a b) := by
    simpa only [Nat.add_zero] using n04NegativeChart_weighted_diagonalJetProduct hE hH hQ X Y
      D n a b 0 0 cX cY
      (fun k hk i hi j hj => by simpa only [Nat.add_zero] using hX k i j (hk.trans hn) (by omega))
      (fun k hk i hi j hj => by simpa only [Nat.add_zero] using hY k i j (hk.trans hn) (by omega))
  have hca := product C A 0 0
    (fun n a b hn hab => (hC n a b hn hab).monoDegree hE hH hQ hd (by omega))
    (fun n a b hn hab => (haz a n b hn hab).1)
  have hv (c : Fin 2) := product (diagonalJetProduct C A) Z 0 c.val hca
    (fun n a b hn hab => (haz a n b hn hab).2 c)
  have hTb (n a b : ℕ) (hn : n ≤ K) (hab : a + b ≤ N) :
      HasWeightedJetBound E H Q Ω d (n * D + a + b) 0 (T n a b) :=
    ((hraw n a b hn hab).1.add hE hH hQ (hv 0 n a b hn hab)).congr (hT n a b hn hab)
  have hBb (n a b : ℕ) (hn : n ≤ K) (hab : a + b ≤ N) :
      HasWeightedJetBound E H Q Ω d (n * D + a + b) 1 (B n a b) := by
    apply ((hraw n a b hn hab).2.add hE hH hQ (hv 1 n a b hn hab)).congr
    intro x hx
    simpa only [B, Ld, C, A, Z, negativeInteriorJet, diagonalJetProduct] using
      W.negativeTransport_forcing_recurrence x.component n a b x.state x.direction (hs x hx) (hq x hx)
  intro n a b hn hab
  exact n04NegativeChart_weighted_firstIntegral_radial K N D hE hH hQ hd T B F hTb hBb hF0
    (fun n a b _ _ x hx => by
      simpa only [F, T, B, negativeInteriorJet, diagonalJetProduct] using
        W.negativeTransport_firstIntegral_recurrence x.component n a b x.state x.direction (hs x hx) (hq x hx))
    a n b hn hab

end N04RealizationStart
end ContinuousFlexibility.Analysis
