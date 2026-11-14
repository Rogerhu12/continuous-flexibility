import ContinuousFlexibility.Analysis.N04NegativeChartInteriorPrefix
import ContinuousFlexibility.Analysis.N04NegativeChartInteriorReferenceJets
import ContinuousFlexibility.Analysis.N04RealizationCubicRegularity
import ContinuousFlexibility.Analysis.FlatMixedDiagonalOperations

/-!
# The actual positive travel input on the material interior

The scalar input for the radial power is three halves of the oriented
actual travel. Its joint tower and positivity belong to the full original
component. The quantitative prefix uses the actual selected half sample,
the first-integral defect and its angular reflection. Positive parameter
orders retain exactly one height weight; order zero uses the fixed
reference material bound and the global height ceiling.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

private theorem scaledOrientation_add (T t x y : ℝ) (side : Bool) :
    (3 / 2 : ℝ) * n04bTravelOrientation T side (t + (x + y) / 2) =
      (3 / 2 : ℝ) * n04bTravelOrientation T side t +
        (if side then -(3 / 4 : ℝ) else 3 / 4) * (x + y) := by
  cases side <;> simp only [n04bTravelOrientation, Bool.false_eq_true, ↓reduceIte] <;> ring

private theorem mixed_affine_reflection
    {Ω : Set PolarPoint} {f g r : PolarPoint → ℝ} (hΩ : IsOpen Ω)
    (hmap : ∀ q ∈ Ω, (q.1, -q.2) ∈ Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hr : ContDiffOn ℝ ∞ r Ω) (c : ℝ)
    (heq : ∀ q ∈ Ω, g q = r q + c * (f q + f (q.1, -q.2)))
    (a b : ℕ) {q : PolarPoint} (hq : q ∈ Ω) :
    mixedDerivative a b g q = mixedDerivative a b r q +
      c * mixedDerivative a b f q +
        (c * (-1 : ℝ) ^ b) * mixedDerivative a b f (q.1, -q.2) := by
  have hfr : ContDiffOn ℝ ∞ (fun p : PolarPoint => f (p.1, -p.2)) Ω :=
    hf.comp (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn (fun q hq => hmap q hq)
  rw [mixedDerivative_congr_on_open hΩ heq a b hq,
    mixedDerivative_add_on_open hΩ hr (contDiffOn_const.mul (hf.add hfr)) a b hq,
    mixedDerivative_const_mul, mixedDerivative_add_on_open hΩ hf hfr a b hq,
    mixedDerivative_reflect_angle]
  ring

theorem n04NegativeChart_affine_two_parameterJet
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {f g h : X → ℝ}
    (J : SmoothDirections U f) (K : SmoothDirections U g) (L : SmoothDirections U h)
    (c α β : ℝ) (heq : ∀ x ∈ U, f x = c + α * g x + β * h x)
    (k : ℕ) {x : X} (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v = (if k = 0 then c else 0) + α * K.D k x v + β * L.D k x v := by
  let JC := smoothDirections_constant J.open_domain c
  let KA : SmoothDirections U (fun y => α * g y) :=
    (smoothDirections_postcompCLM K (α • ContinuousLinearMap.id ℝ ℝ)).congr
      (fun _ _ => by simp only [Function.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul])
  let LB : SmoothDirections U (fun y => β * h y) :=
    (smoothDirections_postcompCLM L (β • ContinuousLinearMap.id ℝ ℝ)).congr
      (fun _ _ => by simp only [Function.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul])
  let JS := (smoothDirectionsAdd (smoothDirectionsAdd JC KA) LB).congr
    (fun y hy => (heq y hy).symm)
  have hj := congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) (J.unique JS k x hx)
  have hj' : J.D k x v = JC.D k x v + KA.D k x v + LB.D k x v := by
    simpa only [JS, SmoothDirections.congr, smoothDirectionsAdd, add_apply] using hj
  have hc : JC.D k x v = if k = 0 then c else 0 := by
    by_cases hk : k = 0
    · subst k
      simpa only [ite_true] using smoothDirections_D_zero_apply JC hx v
    · simpa only [if_neg hk] using smoothDirections_D_constant JC (Nat.pos_of_ne_zero hk) hx v
  rw [hj', hc, n04Realization_smoothDirections_D_const_mul K KA α (fun _ _ => rfl) k hx v,
    n04Realization_smoothDirections_D_const_mul L LB β (fun _ _ => rfl) k hx v]

private theorem affine_two_height_budget
    {k : ℕ} {t c α β x y M N H RH Q : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hH : 0 ≤ H) (hRH : 0 ≤ RH)
    (hHR : H ≤ RH) (hQ : 1 ≤ Q) (hα : |α| ≤ 1) (hβ : |β| ≤ 1)
    (hc : |c| ≤ M) (hx : |x| ≤ N * H * Q) (hy : |y| ≤ N * H * Q)
    (ht : t = (if k = 0 then c else 0) + α * x + β * y) :
    |t| ≤ (M + 2 * N * (1 + RH)) * parameterHeightWeight H k * Q := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hx' : |α * x| ≤ N * H * Q := by
    rw [abs_mul]
    exact (mul_le_mul hα hx (abs_nonneg x) zero_le_one).trans_eq (one_mul _)
  have hy' : |β * y| ≤ N * H * Q := by
    rw [abs_mul]
    exact (mul_le_mul hβ hy (abs_nonneg y) zero_le_one).trans_eq (one_mul _)
  have hc' : |if k = 0 then c else 0| ≤ if k = 0 then M else 0 := by
    by_cases hk : k = 0
    · simpa only [if_pos hk] using hc
    · simp only [if_neg hk, abs_zero, le_refl]
  have htri : |t| ≤ (if k = 0 then M else 0) + N * H * Q + N * H * Q := by
    rw [ht]
    exact (abs_add_le ((if k = 0 then c else 0) + α * x) (β * y)).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add hc' hx')) hy')
  by_cases hk : k = 0
  · simp only [hk, parameterHeightWeight, ite_true, mul_one] at htri ⊢
    have hMQ : M ≤ M * Q := le_mul_of_one_le_right hM hQ
    have hNH : N * H * Q ≤ N * RH * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHR hN) hQ0
    nlinarith only [htri, hMQ, hNH, mul_nonneg hN hQ0]
  · simp only [parameterHeightWeight, if_neg hk, zero_add] at htri ⊢
    have hcoef : 2 * N ≤ M + 2 * N * (1 + RH) := by
      nlinarith only [hM, mul_nonneg hN hRH]
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hH) hQ0
    nlinarith only [htri, hmul]

private theorem travel_material_envelope
    {E C A B RH : ℝ} (hE : 1 ≤ E) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hRH : 0 ≤ RH) :
    (3 / 2 : ℝ) * (C * E ^ A) + 2 * (B * E ^ B) * (1 + RH) ≤
      ((3 / 2 : ℝ) * C + 2 * B * (1 + RH)) * E ^ (A + B) := by
  have hc : C * E ^ A ≤ C * E ^ (A + B) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hB)) hC
  have hb := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hE
      (show B ≤ A + B from le_add_of_nonneg_left hA)) hB
  have h := add_le_add (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 3 / 2))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2))
      (by linarith only [hRH] : 0 ≤ 1 + RH))
  exact h.trans_eq (by ring)

namespace N04RealizationStart

set_option backward.isDefEq.respectTransparency true
attribute [local instance] interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

variable (W : N04RealizationStart)

/-- The literal scalar whose two-thirds power is the physical radial chart. -/
def negativeScaledOrientedTravel (m : ℕ) (side : Bool)
    (z : Parameter W.S) (q : PolarPoint) : ℝ :=
  (3 / 2 : ℝ) * n04bTravelOrientation (W.C.travel m) side
    (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m q).1

def negativeScaledOrientedTravelJointTower (m : ℕ) (side : Bool) :
    SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
      (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : Parameter W.S × PolarPoint => W.negativeScaledOrientedTravel m side x.1 x.2) := by
  have hg : ContDiff ℝ ∞ (fun p : PolarPoint =>
      (3 / 2 : ℝ) * n04bTravelOrientation (W.C.travel m) side p.1) := by
    cases side
    · exact contDiff_const.mul contDiff_fst
    · exact contDiff_const.mul (contDiff_const.sub contDiff_fst)
  exact (W.negativeTravelJointTower m).comp_contDiff isOpen_univ hg.contDiffOn
    (fun _ _ => mem_univ _)

/-- All mixed towers are restrictions of the same actual joint family. -/
def negativeScaledOrientedTravelMixedRegularity (m : ℕ) (side : Bool)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : ε ≤ W.ε) :
    MixedJetRegularity (sectorNeighborhood W.S base ε ε)
      (Ioo (W.C.left m) (W.C.right m) ×ˢ univ) (W.negativeScaledOrientedTravel m side) :=
  n04Realization_jointMixedRegularity
    ((W.negativeScaledOrientedTravelJointTower m side).restrict
      ((sectorNeighborhood_isOpen W.S base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
      (fun _ hx => ⟨sectorNeighborhood_mono W.S hb hε hε hx.1, hx.2⟩))
    (sectorNeighborhood_isOpen W.S base ε ε) (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex W.S base ε ε).prod ((convex_Ioo _ _).prod convex_univ))

theorem negativeScaledOrientedTravel_pos (m : ℕ) (side : Bool)
    {z : Parameter W.S} (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {q : PolarPoint} (hq : q ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    0 < W.negativeScaledOrientedTravel m side z q := by
  have ht := (n04b_actualTravelChart_bijOn W.through03 W.hS W.hT W.field
    (liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m).mapsTo hq
  exact mul_pos (by norm_num : (0 : ℝ) < 3 / 2)
    (n04b_travelOrientation_pos_of_fullStrip side ht.1)

theorem negativeScaledOrientedTravel_reference (m : ℕ) (side : Bool)
    {q : PolarPoint} (hq : q ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    W.negativeScaledOrientedTravel m side 0 q = (3 / 2 : ℝ) *
      n04bTravelOrientation (W.C.travel m) side (opticalTravel W.D.w (W.C.left m) q.1) := by
  simp only [negativeScaledOrientedTravel, liftSectorParameter, Prod.fst_zero,
    Prod.snd_zero, ZeroMemClass.coe_zero, add_zero]
  rw [n04b_reference_actualTravelChart W.through03.1.1.2.2.1 W.field m
    ⟨hq.1.1.le, hq.1.2.le⟩ q.2]

theorem negativeScaledOrientedTravel_firstIntegral (m : ℕ) (side : Bool)
    (z : Parameter W.S) (q : PolarPoint) :
    W.negativeScaledOrientedTravel m side z q =
      (3 / 2 : ℝ) * n04bTravelOrientation (W.C.travel m) side
        (opticalTravel W.D.w (W.C.left m) q.1) +
      (if side then -(3 / 4 : ℝ) else 3 / 4) *
        (W.negativeFirstIntegralDefect z m q + W.negativeFirstIntegralDefect z m (q.1, -q.2)) := by
  have h := congrArg Prod.fst (W.negativeTravel_firstIntegralDefect z m q)
  change _ = opticalTravel W.D.w (W.C.left m) q.1 +
    (W.negativeFirstIntegralDefect z m q + W.negativeFirstIntegralDefect z m (q.1, -q.2)) / 2 at h
  rw [negativeScaledOrientedTravel, h]
  exact scaledOrientation_add _ _ _ _ side

private theorem negativeInterior_reflect_mem (ρ : ℕ → Bool → ℝ) (m : ℕ) (side : Bool)
    {q : PolarPoint} (hq : q ∈ W.negativeInteriorPhysicalDomain ρ (m, side)) :
    (q.1, -q.2) ∈ W.negativeInteriorPhysicalDomain ρ (m, side) := by
  rcases hq with ⟨p, hp, rfl⟩
  exact ⟨(p.1, -p.2), ⟨hp.1, mem_univ _⟩, rfl⟩

set_option diagnostics true in
/-- The common sector precedes every parameter and spatial order.
The finite prefix keeps the exact fractional interpolation exponent and
applies to every genuine tower, including arbitrary parameter slots. -/
theorem negativeInterior_scaledTravel_prefix
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (hρb : ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧ ∀ m side,
      (ρ m side)⁻¹ ≤ C * W.T.E0 (W.negativeHalfSample e m side) ^ P) :
    ∃ base : ℕ, ∃ ε : ℝ, W.base ≤ base ∧ 0 < ε ∧ ε ≤ min W.ε (1 / 2 : ℝ) ∧
      ∀ K : ℕ, ∃ D : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k a b : ℕ, k ≤ K → a + b ≤ s → ∀ m side q,
      q ∈ W.negativeInteriorPhysicalDomain ρ (m, side) →
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun z => mixedDerivative a b (W.negativeScaledOrientedTravel m side z) q),
      ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ v : Fin k → Parameter W.S,
      (∀ i, parameterGrading W.S base (v i) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      parameterGrading W.S (s + D * K + base + 1) z ≤ R →
      (∀ i, parameterGrading W.S (s + D * K + base + 1) (v i) ≤ R) →
      |J.D k z v| ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
        parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
          R ^ (((a + b + D * k : ℕ) : ℝ) / ((s + D * K : ℕ) + 1 : ℝ)) := by
  have hex := W.negativeInterior_firstIntegral_prefix e ρ hρ hρb
  let base : ℕ := hex.choose
  let ε : ℝ := hex.choose_spec.choose
  have hs := hex.choose_spec.choose_spec
  have hheightExists := materialHeight_E0_weight_bounded W.hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  let RH : ℝ := hheightExists.choose
  have hRH := hheightExists.choose_spec.1
  have hheight := hheightExists.choose_spec.2
  refine ⟨base, ε, hs.1, hs.2.1, hs.2.2.1, fun K => ?_⟩
  have hexD := hs.2.2.2 K
  let D : ℕ := hexD.choose
  have hD := hexD.choose_spec
  refine ⟨D, fun s => ?_⟩
  have hexF := hD s
  let BF : ℝ := hexF.choose
  have hBF := hexF.choose_spec.1
  have hF := hexF.choose_spec.2
  have hexR := W.negativeInterior_referenceTravel_mixed_bounds e ρ hρ hρb s
  let CR : ℝ := hexR.choose
  let AR : ℝ := hexR.choose_spec.choose
  have hRjet := hexR.choose_spec.choose_spec
  have hpackExists := coefficientEnvelope_pack
    ((3 / 2 : ℝ) * CR + 2 * BF * (1 + RH)) (AR + BF)
  let B : ℝ := hpackExists.choose
  have hB := hpackExists.choose_spec.1
  have hpack := hpackExists.choose_spec.2
  refine ⟨B, hB, fun k a b hk hab m side q hq J z hz v hv R hR hzR hvR => ?_⟩
  let U : Set (Parameter W.S) := sectorNeighborhood W.S base ε ε
  let U₀ : Set (Parameter W.S) := sectorNeighborhood W.S W.base W.ε W.ε
  let Ω : Set PolarPoint := Ioo (W.C.left m) (W.C.right m) ×ˢ univ
  let E : ℝ := W.T.E0 (W.negativeHalfSample e m side)
  let H : ℝ := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
  let Q : ℝ := R ^ (((a + b + D * k : ℕ) : ℝ) / ((s + D * K : ℕ) + 1 : ℝ))
  let c : ℝ := if side then -(3 / 4 : ℝ) else 3 / 4
  let r : PolarPoint → ℝ := fun p => (3 / 2 : ℝ) * n04bTravelOrientation (W.C.travel m) side
    (opticalTravel W.D.w (W.C.left m) p.1)
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S base ε ε
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  have hsub : U ⊆ U₀ := sectorNeighborhood_mono W.S hs.1
    (hs.2.2.1.trans (min_le_left _ _)) (hs.2.2.1.trans (min_le_left _ _))
  have hqΩ : q ∈ Ω := W.negativeInteriorPhysicalDomain_subset ρ
    (fun m side => (hρ m side).1) (m, side) hq
  have hqr := W.negativeInterior_reflect_mem ρ m side hq
  have hreflect : ∀ p ∈ Ω, (p.1, -p.2) ∈ Ω := fun _ hp => ⟨hp.1, mem_univ _⟩
  let F₀ := n04Realization_jointMixedRegularity (W.negativeFirstIntegralDefectJointTower m)
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε) hΩ
    ((sectorNeighborhood_convex W.S W.base W.ε W.ε).prod ((convex_Ioo _ _).prod convex_univ))
  let F : MixedJetRegularity U Ω (fun x => W.negativeFirstIntegralDefect x m) :=
    ⟨fun x hx => F₀.spatial x (hsub hx),
      fun u w p hp => (F₀.parameter u w p hp).restrict hU hsub⟩
  let JF := F.parameter a b q hqΩ
  let JG := F.parameter a b (q.1, -q.2) (hreflect q hqΩ)
  have hzero : (0 : Parameter W.S) ∈ U :=
    ⟨(sectorGrading W.S base).map_zero'.trans_lt hs.2.1,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hs.2.1⟩
  have hr : ContDiffOn ℝ ∞ r Ω :=
    ((W.negativeScaledOrientedTravelMixedRegularity m side hs.1
      (hs.2.2.1.trans (min_le_left _ _))).spatial 0 hzero).congr
        (fun p hp => (W.negativeScaledOrientedTravel_reference m side hp).symm)
  have hformula (x : Parameter W.S) (hx : x ∈ U) :
      mixedDerivative a b (W.negativeScaledOrientedTravel m side x) q =
        mixedDerivative a b r q + c * mixedDerivative a b (W.negativeFirstIntegralDefect x m) q +
          (c * (-1 : ℝ) ^ b) * mixedDerivative a b (W.negativeFirstIntegralDefect x m) (q.1, -q.2) :=
    mixed_affine_reflection hΩ hreflect (F.spatial x hx) hr c
      (fun p _ => W.negativeScaledOrientedTravel_firstIntegral m side x p) a b hqΩ
  have hjet := n04NegativeChart_affine_two_parameterJet J JF JG (mixedDerivative a b r q) c (c * (-1 : ℝ) ^ b)
    hformula k hz v
  have hE : 1 ≤ E := W.floor _
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hHR : H ≤ RH := by
    simpa only [H, RH, Real.rpow_zero, mul_one] using
      hheight (W.negativeHalfSample e m side)
        (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)
  have hQ : 1 ≤ Q := Real.one_le_rpow hR (by positivity)
  have hc : |c| ≤ 1 := by cases side <;> norm_num [c]
  have hc' : |c * (-1 : ℝ) ^ b| ≤ 1 := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one] using hc
  have hrb : |mixedDerivative a b r q| ≤ (3 / 2 : ℝ) * (CR * E ^ AR) := by
    dsimp only [r]
    rw [mixedDerivative_const_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    exact mul_le_mul_of_nonneg_left (hRjet.2.2 m side q hq a b hab) (by norm_num)
  have hf (p : PolarPoint) (hp : p ∈ W.negativeInteriorPhysicalDomain ρ (m, side))
      (JP : SmoothDirections U (fun x => mixedDerivative a b (W.negativeFirstIntegralDefect x m) p)) :
      |JP.D k z v| ≤ (BF * E ^ BF) * H * Q := by
    have h := hF k a b hk hab m side p hp JP z hz v hv R hR
      (by simpa only [Nat.mul_comm D K] using hzR)
      (fun i => by simpa only [Nat.mul_comm D K] using hvR i)
    simpa only [BF, E, H, Q, D, Nat.mul_comm K hexD.choose,
      (by ring : k * hexD.choose + a + b = a + b + hexD.choose * k)] using h
  have hbound := affine_two_height_budget
    (show 0 ≤ (3 / 2 : ℝ) * (CR * E ^ AR) from mul_nonneg (by norm_num)
      (mul_nonneg hRjet.1.le (Real.rpow_nonneg (zero_le_one.trans hE) _)))
    (show 0 ≤ BF * E ^ BF from mul_nonneg hBF.le (Real.rpow_nonneg (zero_le_one.trans hE) _))
    hH hRH.le hHR hQ hc hc' hrb (hf q hq JF) (hf (q.1, -q.2) hqr JG) hjet
  have hcost := (travel_material_envelope hE hRjet.1.le hRjet.2.1 hBF.le hRH.le).trans
    (hpack E hE)
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost (parameterHeightWeight_nonneg hH k)) (zero_le_one.trans hQ))

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_scaledTravel_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_scaledTravel_prefix
