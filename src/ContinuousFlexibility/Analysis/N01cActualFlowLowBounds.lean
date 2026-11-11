import ContinuousFlexibility.Analysis.N01cActualFlowLowGeometry
import ContinuousFlexibility.Analysis.N01cActualLinearSpeedJets
import ContinuousFlexibility.Analysis.N01cActualLinearCoefficientBounds

/-!
# One common low bound for all actual flow variations

The physical angular speed jets through order four choose one fixed
base. The reference speed has no angular dependence. The actual
all-angle singleton head consequently has a uniform third Sobolev norm,
and the previously proved composition estimate bounds the genuine
linear coefficient integral for every parameter variation order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

theorem componentCosineSpeed_positive_jet_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base s : ℕ} {ε M : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    {x : AnnularState S × ℝ} (hx : x ∈ stateNeighborhood S C base ε)
    (hM : 0 ≤ M)
    (hbound : ∀ m n p, n ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      |characteristicSpeedFamily D S C 0 n p x| ≤ M)
    (m n : ℕ) (hn : 0 < n) (hns : n ≤ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi) (θ : ℝ) :
    |iteratedDeriv n (fun η => componentCosineSpeed D S C m (x, (t, η))) θ| ≤
      (D.b - D.a) / 2 * M := by
  have he : (fun η => componentCosineSpeed D S C m (x, (t, η))) =
      fun η => componentCosineSpeed D S C m ((C.referenceState, 0), (t, 0)) +
        (componentCosineSpeed D S C m (x, (t, η)) -
          componentCosineSpeed D S C m ((C.referenceState, 0), (t, η))) := by
    funext η
    rw [componentCosineSpeed_reference_angle hS hT hA hε hB m t η]
    ring
  rw [he, iteratedDeriv_const_add hn]
  exact componentCosineSpeedDifference_jet_le hS hT hA hε hB hx hM hbound m n hns ht θ

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Blueprint

open Set MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- All low data are uniform before every parameter prefix. This includes
the actual integrated coefficient of every finite-plot variational equation. -/
theorem n01_exists_stable_actualFlow_lowBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ, base ≤ base₀ ∧ 0 < ε₀ ∧
      ε₀ ≤ min ε (1 / 2) ∧ ∃ c M Mlin : ℝ, 0 < c ∧ 0 < M ∧ 0 < Mlin ∧
      ∀ base' : ℕ, base₀ ≤ base' → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
      ∀ hB' : N01PartB D S C base' ε',
      ∀ hpos : (∀ z ∈ stateNeighborhood S C base' ε', ∀ i r,
        r ∈ Icc (C.left i) (C.right i) →
          0 < twoRootDivided (componentOpticalSquare D S C i z)
            (C.left i) (C.right i) r),
      ∀ m, ∀ J : ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
        (componentCosineSpeed D S C m),
      ∀ d : ℕ, ∀ x : AnnularState S × ℝ,
      ∀ hx : x ∈ stateNeighborhood S C base' ε',
      ∀ L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ),
        (∀ t θ, c ≤ deriv (ordinaryFlowFiniteAngle m x hx L t) θ) ∧
        (∀ t, circleRealSobolevNorm 3
          (ordinaryFlowFiniteDefectJet hS hT hA hB' hpos m J x hx L t 0) ≤ M) ∧
        ∀ n : ℕ, ∀ v : Fin (n + 1) → (Fin d → ℝ),
          (ordinaryFlowCircleVariationData hS hT hA hB' hpos m J x hx L n v).coefficientSize 1 ≤ Mlin := by
  obtain ⟨bg, eg, hbg, heg, hege, c, M, hc, hM, hgeom⟩ :=
    n01_exists_stable_actualFlow_lowGeometry hS hT hA hε hB hG hSpeed
  obtain ⟨bs, hbs, Ms, hMs, hspeed⟩ :=
    n01_speedDifference_fixedOrder_uniform hT hA.1.1 hSpeed 4
  obtain ⟨Mt, hMt, htime⟩ := exists_circleFlowCompactTime_deriv_bound 0 Real.pi
  have hwidth : 0 < D.b - D.a := sub_pos.mpr
    ((hA.2.2.1.1 0).1.trans ((hA.2.2.1.1 0).2.1.trans (hA.2.2.1.1 0).2.2))
  let W : ℝ := (D.b - D.a) / 2 * Ms
  have hW : 0 < W := mul_pos (div_pos hwidth (by norm_num)) hMs
  let B : ℝ := (2 : ℝ) ^ (3 : ℕ) * (Mt * W + Mt * W)
  have hBpos : 0 < B := by dsimp only [B]; positivity
  let Mlin : ℝ := circleLiftCompositionConstant Real.pi c M 1 * (B + B * M)
  have hMlin : 0 < Mlin := mul_pos
    (zero_lt_one.trans_le (circleLiftCompositionConstant_one_le Real.pi c M 1))
    (add_pos hBpos (mul_pos hBpos hM))
  refine ⟨max bg bs, eg, hbg.trans (le_max_left _ _), heg, hege,
    c, M, Mlin, hc, hM, hMlin, ?_⟩
  intro base' hb ε' hε' he hB' hpos m J d x hx L
  have hlow := hgeom base' ((le_max_left bg bs).trans hb) ε' hε' he
    hB' hpos m J d x hx L
  have hxs : x ∈ stateNeighborhood S C bs (min ε (1 / 2)) :=
    stateNeighborhood_subset ((le_max_right bg bs).trans hb) (he.trans hege) hx
  have hphysical := hspeed x hxs
  have houter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      circleRealSobolevNorm 3
        (ordinaryFlowSpeedOuterJet hS hT hA hB' hpos m x hx L
          (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice 0) ≤ B := by
    let O : ℕ → C(AddCircle Real.pi, ℝ) :=
      ordinaryFlowSpeedOuterJet hS hT hA hB' hpos m x hx L
        (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice
    have hpoint (b : ℕ) (hb : b ≤ 3) (θ : ℝ) :
        |O b (θ : AddCircle Real.pi)| ≤ Mt * W := by
      rw [ordinaryFlowSpeedOuterJet_angle_coe_apply hS hT hA hB' hpos m x hx L J,
        abs_mul]
      exact mul_le_mul (htime t ht)
        (componentCosineSpeed_positive_jet_le hS hT hA hε' hB' hx hMs.le
          hphysical m (b + 1) (by omega) (by omega)
          (circleFlowCompactTime_mem Real.pi_pos.le t) θ)
        (abs_nonneg _) hMt.le
    exact circle_sobolevNorm_le_pointwiseJetBounds O
      (periodicCircleJet_hasDerivAt _ _ _) 3 (mul_pos hMt hW).le (mul_pos hMt hW).le
      (hpoint 0 (by decide)) (hpoint 3 le_rfl)
  refine ⟨fun t => (hlow t).1, fun t => (hlow t).2, ?_⟩
  intro n v
  exact ordinaryFlowCircleVariationData_coefficientSize_one_le
    hS hT hA hB' hpos m J x hx L n v hc hM.le hBpos.le
    (fun t _ => (hlow t).1) (fun t _ => (hlow t).2) houter

end ContinuousFlexibility.Blueprint
