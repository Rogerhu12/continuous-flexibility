import ContinuousFlexibility.Analysis.N04NegativeChartInteriorTravelBand
import ContinuousFlexibility.Analysis.N04NegativeChartPhysicalBounds

/-! Positive parameter jets of the two actual physical coordinates on the
material interior. The scalar power uses the one common travel value band.
The angular coordinate uses only the positive jets of its reference defect. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

private theorem interior_rootHalf_scaled (T t : ℝ) (side : Bool) :
    n04bRootHalfCoordinate T side t =
      ((3 / 2 : ℝ) * n04bTravelOrientation T side t) ^ (2 / 3 : ℝ) := by
  unfold n04bRootHalfCoordinate n04bRootCoordinate
  congr 1
  ring

private theorem interior_angle_spatial
    {Ω : Set PolarPoint} {f g : PolarPoint → ℝ} (hΩ : IsOpen Ω)
    (hmap : ∀ q ∈ Ω, (q.1, -q.2) ∈ Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (heq : ∀ q ∈ Ω, g q = q.2 + (f q - f (q.1, -q.2)) / 2)
    (a b : ℕ) {q : PolarPoint} (hq : q ∈ Ω) :
    mixedDerivative a b g q = mixedDerivative a b Prod.snd q +
      (1 / 2 : ℝ) * mixedDerivative a b f q +
        (-(1 / 2 : ℝ) * (-1 : ℝ) ^ b) * mixedDerivative a b f (q.1, -q.2) := by
  have hr : ContDiffOn ℝ ∞ (fun p : PolarPoint => f (p.1, -p.2)) Ω :=
    hf.comp (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn (fun q hq => hmap q hq)
  have he : ∀ p ∈ Ω, g p = p.2 + (1 / 2 : ℝ) * f p +
      (-(1 / 2 : ℝ)) * f (p.1, -p.2) := by
    intro p hp
    rw [heq p hp]
    ring
  rw [mixedDerivative_congr_on_open hΩ he a b hq,
    mixedDerivative_add_on_open hΩ (contDiff_snd.contDiffOn.add (contDiffOn_const.mul hf))
      (contDiffOn_const.mul hr) a b hq,
    mixedDerivative_add_on_open hΩ contDiff_snd.contDiffOn (contDiffOn_const.mul hf) a b hq,
    mixedDerivative_const_mul, mixedDerivative_const_mul, mixedDerivative_reflect_angle]
  ring

private theorem interior_affine_budget {t x y α β C E A H V : ℝ}
    (hα : |α| ≤ 1) (hβ : |β| ≤ 1)
    (hx : |x| ≤ C * E ^ A * H * V) (hy : |y| ≤ C * E ^ A * H * V)
    (ht : t = α * x + β * y) :
    |t| ≤ (2 * C) * E ^ A * H * V := by
  have hx' : |α * x| ≤ C * E ^ A * H * V := by
    rw [abs_mul]
    exact (mul_le_mul hα hx (abs_nonneg x) zero_le_one).trans_eq (one_mul _)
  have hy' : |β * y| ≤ C * E ^ A * H * V := by
    rw [abs_mul]
    exact (mul_le_mul hβ hy (abs_nonneg y) zero_le_one).trans_eq (one_mul _)
  rw [ht]
  exact ((abs_add_le _ _).trans (add_le_add hx' hy')).trans_eq (by ring)

private theorem interior_enlarge_cost {x C A B E H V : ℝ}
    (hE : 1 ≤ E) (hB : 0 ≤ B) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hCB : C ≤ B) (hAB : A ≤ B)
    (hx : |x| ≤ C * E ^ A * H * V) : |x| ≤ B * E ^ B * H * V :=
  hx.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul hCB (Real.rpow_le_rpow_of_exponent_le hE hAB)
      (Real.rpow_nonneg (zero_le_one.trans hE) A) hB) hH) hV)

namespace N04RealizationStart

set_option backward.isDefEq.respectTransparency true
attribute [local instance] interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

variable (W : N04RealizationStart)

theorem negativeChart_radial_scaledTravel (m : ℕ) (side : Bool)
    {z : Parameter W.S} (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {q : PolarPoint} (hq : q ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side q).1 =
        W.negativeScaledOrientedTravel m side z q ^ (2 / 3 : ℝ) := by
  have h := ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m side).component_chart_germ hq).self_of_nhds
  exact (congrArg Prod.fst h).trans (interior_rootHalf_scaled _ _ side)

private def negativeInteriorDefectRegularity (m : ℕ)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : ε ≤ W.ε) :
    MixedJetRegularity (sectorNeighborhood W.S base ε ε)
      (Ioo (W.C.left m) (W.C.right m) ×ˢ univ)
      (fun z => W.negativeFirstIntegralDefect z m) := by
  let R := n04Realization_jointMixedRegularity (W.negativeFirstIntegralDefectJointTower m)
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε) (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex W.S W.base W.ε W.ε).prod ((convex_Ioo _ _).prod convex_univ))
  have hsub := sectorNeighborhood_mono W.S hb hε hε
  exact ⟨fun x hx => R.spatial x (hsub hx), fun a b q hq =>
    (R.parameter a b q hq).restrict (sectorNeighborhood_isOpen W.S base ε ε) hsub⟩

/-- The physical positive bound restricted to the closed material interior. -/
def NegativeInteriorPhysicalPositiveBounds
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ) (base : ℕ) (ε : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ m (side radial : Bool) q, q ∈ W.negativeInteriorPhysicalDomain ρ (m, side) →
    ∀ a b : ℕ, a + b ≤ s →
    ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun z => mixedDerivative a b (fun p => if radial then
        (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side p).1 else
        (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side p).2) q),
    ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ v : Fin n → Parameter W.S,
      |J.D n z v| ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
        W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) *
          oneHighVariationWeight (parameterGrading W.S) base (s + loss) z v

set_option diagnostics true in
/-- Both literal projections use one state sector before every derivative
order. The radial power has its true current lower bound on the indexed
interior; qualitative positivity remains on the full component. -/
theorem negativeInterior_physical_positive_bounds
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (hρb : ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧ ∀ m side,
      (ρ m side)⁻¹ ≤ C * W.T.E0 (W.negativeHalfSample e m side) ^ P) :
    ∃ base : ℕ, ∃ ε : ℝ, W.base ≤ base ∧ 0 < ε ∧ ε ≤ min W.ε (1 / 2 : ℝ) ∧
      W.NegativeInteriorPhysicalPositiveBounds e ρ base ε := by
  let G : W.NegativeInteriorTravelControl e ρ :=
    Classical.choice (W.negativeInteriorTravelControl_nonempty e ρ hρ hρb)
  have hFex := W.negativeInterior_firstIntegral_prefix e ρ hρ hρb
  let bF := hFex.choose
  let εF := hFex.choose_spec.choose
  have hFs := hFex.choose_spec.choose_spec
  let base := max G.base bF
  let ε := min G.ε εF
  have hbW : W.base ≤ base := G.base_le.trans (le_max_left _ _)
  have hεW : ε ≤ W.ε := (min_le_left _ _).trans (G.ε_le.trans (min_le_left _ _))
  have hhalf : ε ≤ 1 / 2 := (min_le_left _ _).trans (G.ε_le.trans (min_le_right _ _))
  have hsubG := sectorNeighborhood_mono W.S (le_max_left G.base bF)
    (min_le_left G.ε εF) (min_le_left G.ε εF)
  have hsubF := sectorNeighborhood_mono W.S (le_max_right G.base bF)
    (min_le_right G.ε εF) (min_le_right G.ε εF)
  have hsubW := sectorNeighborhood_mono W.S hbW hεW hεW
  have hτ := NegativeInteriorScaledTravelPrefix.mono W (fun m side => (hρ m side).1)
    G.«prefix» G.base_le (G.ε_le.trans (min_le_left _ _))
    (le_max_left G.base bF) (min_le_left G.ε εF)
  have hhEx := materialHeight_E0_weight_bounded W.hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  let RH := hhEx.choose
  refine ⟨base, ε, hbW, lt_min G.ε_pos hFs.2.1, le_min hεW hhalf, fun n hn => ?_⟩
  have hτD := hτ n
  let Dτ := hτD.choose
  have hFD := hFs.2.2.2 n
  let DF := hFD.choose
  let loss := max (Dτ * n + base + 1) (n * DF + bF + 1)
  refine ⟨loss, fun s => ?_⟩
  have hτB := hτD.choose_spec s
  let Cτ := hτB.choose
  have hFB := hFD.choose_spec s
  let BF := hFB.choose
  have hpEx := n04NegativeChart_positivePower_positive_oneHigh (X := Parameter W.S)
    n s Dτ RH (2 / 3 : ℝ) G.lower_pos G.upper_nonneg
    G.lowerPower_nonneg G.upperPower_nonneg hτB.choose_spec.1.le hτB.choose_spec.1.le
  let BR := hpEx.choose
  let B := 1 + BR + 2 * BF
  have hBR : 0 < BR := hpEx.choose_spec.1
  have hBF : 0 < BF := hFB.choose_spec.1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBRB : BR ≤ B := by dsimp only [B]; linarith only [hBF]
  have hBFB : BF ≤ B := by dsimp only [B]; linarith only [hBR, hBF]
  have h2BFB : 2 * BF ≤ B := by dsimp only [B]; linarith only [hBR]
  refine ⟨B, hB, fun m side radial q hq a b hab J z hz v => ?_⟩
  let U : Set (Parameter W.S) := sectorNeighborhood W.S base ε ε
  let Ω : Set PolarPoint := Ioo (W.C.left m) (W.C.right m) ×ˢ univ
  let E := W.T.E0 (W.negativeHalfSample e m side)
  let H := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
  let V := oneHighVariationWeight (parameterGrading W.S) base (s + loss) z v
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S base ε ε
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  have hqΩ := W.negativeInteriorPhysicalDomain_subset ρ (fun m side => (hρ m side).1) (m, side) hq
  have hE : 1 ≤ E := W.floor _
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hV : 0 ≤ V := oneHighVariationWeight_nonneg _ _ _ _ _
  have hHR : H ≤ RH := by
    simpa only [H, RH, Real.rpow_zero, mul_one] using hhEx.choose_spec.2
      (W.negativeHalfSample e m side)
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)
  cases radial with
  | true =>
    let F := W.negativeScaledOrientedTravelMixedRegularity m side hbW hεW
    let JP : SmoothDirections U (fun y => mixedDerivative a b
        (fun p => W.negativeScaledOrientedTravel m side y p ^ (2 / 3 : ℝ)) q) :=
      J.congr (fun y hy => mixedDerivative_congr_on_open hΩ
        (fun p hp => W.negativeChart_radial_scaledTravel m side (hsubW hy) hp) a b hqΩ)
    have hval := G.values m side q hq z (hsubG hz)
    have hp := hpEx.choose_spec.2 (parameterGrading W.S) 0 base (s + Dτ * n + base + 1)
      U hU Ω hΩ (W.negativeScaledOrientedTravel m side) F
      (fun y hy p hp => W.negativeScaledOrientedTravel_pos m side (hsubW hy) hp)
      q hqΩ E H hE hH hHR z hz
      (by simpa only [sub_zero] using n04NegativeGeometry_parameterGrading_le_one W.S base hhalf hz)
      hval.1 hval.2 (fun j hj u w huw slots hslots R hR hzR hsR => by
        have ht := hτB.choose_spec.2 j u w hj huw m side q hq (F.parameter u w q hqΩ)
          z hz slots hslots R hR (by simpa only [sub_zero] using hzR) hsR
        simpa only [Real.norm_eq_abs] using ht)
      n le_rfl hn a b hab JP v
    have hp' : |J.D n z v| ≤ BR * E ^ BR * H *
        oneHighVariationWeight (parameterGrading W.S) base (s + Dτ * n + base + 1) z v := by
      simpa only [JP, SmoothDirections.congr, sub_zero, Real.norm_eq_abs] using hp
    have hweight := oneHighVariationWeight_mono (n07aParameterGrading_monotone W.S)
      (le_rfl : base ≤ base) (show s + Dτ * n + base + 1 ≤ s + loss from by dsimp only [loss]; omega) z v
    exact interior_enlarge_cost hE hB.le hH hV hBRB hBRB
      (hp'.trans (mul_le_mul_of_nonneg_left hweight
        (mul_nonneg (mul_nonneg hBR.le (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH)))
  | false =>
    let F := W.negativeInteriorDefectRegularity m hFs.1 (hFs.2.2.1.trans (min_le_left _ _))
    have hqr : (q.1, -q.2) ∈ W.negativeInteriorPhysicalDomain ρ (m, side) := by
      rcases hq with ⟨p, hp, rfl⟩
      exact ⟨(p.1, -p.2), ⟨hp.1, mem_univ _⟩, rfl⟩
    have hreflect : ∀ p ∈ Ω, (p.1, -p.2) ∈ Ω := fun _ hp => ⟨hp.1, mem_univ _⟩
    let JF := F.parameter a b q hqΩ
    let JR := F.parameter a b (q.1, -q.2) (hreflect q hqΩ)
    have hbudget (p : PolarPoint) (hp : p ∈ W.negativeInteriorPhysicalDomain ρ (m, side))
        (K : SmoothDirections (sectorNeighborhood W.S bF εF εF)
          (fun y => mixedDerivative a b (W.negativeFirstIntegralDefect y m) p)) :
        |K.D n z v| ≤ BF * E ^ BF * H * V := by
      have hβ : ((n * DF + a + b : ℕ) : ℝ) / ((s + n * DF : ℕ) + 1 : ℝ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast (show n * DF + a + b ≤ s + n * DF + 1 from by omega)
      have hnrm := n04NegativeChart_fractional_oneHigh (K.D n z) (parameterGrading W.S)
        bF (s + n * DF + bF + 1) z
        (mul_nonneg (mul_nonneg hBF.le (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH) hβ
        (fun slots hslots R hR hzR hsR => hFB.choose_spec.2 n a b le_rfl hab m side p hp K
          z (hsubF hz) slots hslots R hR hzR hsR) v
      have hw := oneHighVariationWeight_mono (n07aParameterGrading_monotone W.S)
        (le_max_right G.base bF)
        (show s + n * DF + bF + 1 ≤ s + loss from by dsimp only [loss]; omega) z v
      exact hnrm.trans (mul_le_mul_of_nonneg_left hw
        (mul_nonneg (mul_nonneg hBF.le (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH))
    have hformula (y : Parameter W.S) (hy : y ∈ U) :=
      interior_angle_spatial
        (g := fun p => (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C y) m side p).2)
        hΩ hreflect (F.spatial y (hsubF hy))
        (fun p hp => congrArg Prod.snd (W.negativeChart_firstIntegralDefect y (hsubW hy) m side p hp))
        a b hqΩ
    have hj := n04NegativeChart_affine_two_parameterJet J
      (JF.restrict hU hsubF) (JR.restrict hU hsubF) (mixedDerivative a b Prod.snd q)
      (1 / 2 : ℝ) (-(1 / 2 : ℝ) * (-1 : ℝ) ^ b) hformula n hz v
    have hj' : J.D n z v = (1 / 2 : ℝ) * JF.D n z v +
        (-(1 / 2 : ℝ) * (-1 : ℝ) ^ b) * JR.D n z v := by
      simpa only [if_neg (Nat.ne_of_gt hn), zero_add, SmoothDirections.restrict_D] using hj
    have hc : |-(1 / 2 : ℝ) * (-1 : ℝ) ^ b| ≤ 1 := by
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      norm_num
    exact interior_enlarge_cost hE hB.le hH hV h2BFB hBFB
      (interior_affine_budget (by norm_num : |(1 / 2 : ℝ)| ≤ 1) hc
        (hbudget q hq JF) (hbudget (q.1, -q.2) hqr JR) hj')

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_physical_positive_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_physical_positive_bounds
