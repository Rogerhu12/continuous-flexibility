import ContinuousFlexibility.Analysis.N04PositiveGeometryMixedJointWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledMovingWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFamilyMaterial
import ContinuousFlexibility.Analysis.N04PositiveGeometryReferencePullbackCosts
import ContinuousFlexibility.Analysis.WholePositiveReferenceGauge

/-!
# The physical height in the retained fixed reference gauge

The fixed reference multiplier and the actual reciprocal Taylor height
are estimated before moving by the actual inverse transport. The exact
mixed expansion keeps the original parameter prefix. Both literal
height choices share one sampled polynomial envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PositiveGeometry_controlledReferenceHeight_unit_word_bound
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (G : N04PositiveGeometryControlledFamily W X order)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H₀)
    (N : ℕ) (A RH : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
    ∀ (U : Set E), IsOpen U → Convex ℝ U →
    ∀ state : E → AnnularState W.S × ℝ,
    ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w), ∀ inv : Bool,
    ∀ RQ : MixedJetRegularity U univ (fun x p => if !inv then
      (G.toN04PositiveGeometryControlData.Q (state x) i p)⁻¹
      else G.toN04PositiveGeometryControlData.Q (state x) i p),
    ∀ JQ : SmoothDirections (U ×ˢ univ) (fun y : E × PolarPoint => if !inv then
      (G.toN04PositiveGeometryControlData.Q (state y.1) i y.2)⁻¹
      else G.toN04PositiveGeometryControlData.Q (state y.1) i y.2),
    ∀ JS : SmoothDirections (U ×ˢ univ) (fun y : E × PolarPoint =>
      G.toN04PositiveGeometryControlData.σ (state y.1) i y.2),
    ∀ J : SmoothDirections (U ×ˢ univ) (fun y : E × PolarPoint => if inv then
      (wholePositiveReferenceGaugeHeight (fun p => H₀ i p.1)
        (G.toN04PositiveGeometryControlData.σ (state y.1) i)
        (G.toN04PositiveGeometryControlData.Q (state y.1) i) y.2)⁻¹
      else wholePositiveReferenceGaugeHeight (fun p => H₀ i p.1)
        (G.toN04PositiveGeometryControlData.σ (state y.1) i)
        (G.toN04PositiveGeometryControlData.Q (state y.1) i) y.2),
    ∀ x ∈ U, ∀ y : PolarPoint, ∀ p q : Seminorm ℝ E, ∀ R : ℝ, 0 ≤ R →
    ∀ H t : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ t → ∀ K shift : ℕ, 1 ≤ shift →
    (∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b + k ≤ N →
      ∀ v : Fin k → E, (∀ j, p (v j) ≤ 1 ∧ q (v j) ≤ R) →
      ‖(RQ.parameter a b (G.toN04PositiveGeometryControlData.σ (state x) i y)
        (mem_univ _)).D k x v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
          parameterHeightWeight H k * t ^ (a + b + shift * k)) →
    (∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → E × PolarPoint,
      (∀ j, if w.isState j then (v j).2 = 0 else (v j).1 = 0) →
      (∀ j, p (v j).1 ≤ 1 ∧ q (v j).1 ≤ R ∧ ‖(v j).2‖ ≤ 1) →
      ‖JS.D n (x, y) v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight H w.stateArity * t ^ (w.angleArity + shift * w.stateArity - 1)) →
    ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
    ∀ v : Fin n → E × PolarPoint,
    (∀ j, if w.isState j then (v j).2 = 0 else (v j).1 = 0) →
    (∀ j, p (v j).1 ≤ 1 ∧ q (v j).1 ≤ R ∧ ‖(v j).2‖ ≤ 1) →
      ‖J.D n (x, y) v‖ ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
        parameterHeightWeight H w.stateArity * t ^ (w.angleArity + shift * w.stateArity) := by
  classical
  obtain ⟨Br, hBr, hrefjets⟩ := n04PositiveGeometry_reference_prefix_material_cost W.floor hmaterial N
  let D := max 1 (max A (max Br RH))
  have hD : 1 ≤ D := le_max_left _ _
  have hAD : A ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hBrD : Br ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hRHD : RH ≤ D := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  choose cm hcm hmoving using fun n : Fin (N + 1) =>
    n04PositiveGeometry_movingPoint_unit_word_bound (E := E) (V := PolarPoint) (Z := ℝ) n.val
  let Cm := 1 + ∑ n : Fin (N + 1), cm n
  have hCm : 1 ≤ Cm := le_add_of_nonneg_right
    (Finset.sum_nonneg fun n _ => zero_le_one.trans (hcm n))
  have hcmCm (n : Fin (N + 1)) : cm n ≤ Cm :=
    (Finset.single_le_sum (fun n _ => zero_le_one.trans (hcm n)) (Finset.mem_univ n)).trans
      (le_add_of_nonneg_left zero_le_one)
  let P₀ : ℝ := (4 : ℝ) ^ N
  have hP₀ : 1 ≤ P₀ := one_le_pow₀ (by norm_num)
  obtain ⟨B₀, hB₀, hpack⟩ := n04PositiveGeometry_polynomial_sample_pack
    (Cm * P₀ ^ (2 * N + 2)) D (4 * N + 4)
  let B := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have hB₀B : B₀ ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro U hU hcU state i inv RQ JQ JS J x hx y p q R hR H t hH hHR ht K shift hshift
    hrawQ hrawS n hn hnN w hw v hpure hbox
  let E₀ := W.U.E0 (W.U.sample (X.cell i))
  let M := D * E₀ ^ D
  let M' := P₀ * M ^ 2
  have hE₀ : 1 ≤ E₀ := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hDM : D ≤ M := le_mul_of_one_le_right (zero_le_one.trans hD)
    (Real.one_le_rpow hE₀ (zero_le_one.trans hD))
  have hM : 1 ≤ M := hD.trans hDM
  have hM' : 1 ≤ M' := one_le_mul_of_one_le_of_one_le hP₀ (one_le_pow₀ hM)
  have hMM' : M ≤ M' := by
    calc
      M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 2 := pow_le_pow_right₀ hM (by omega)
      _ ≤ P₀ * M ^ 2 := le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hM) _) hP₀
  have hHM' : H ≤ M' := hHR.trans (hRHD.trans (hDM.trans hMM'))
  have hraise {a : ℝ} (ha : a ≤ D) : a * E₀ ^ a ≤ M :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE₀ ha)
      (Real.rpow_nonneg (zero_le_one.trans hE₀) _) (zero_le_one.trans hD)
  let Q : E → PolarPoint → ℝ := fun z p => if !inv then
    (G.toN04PositiveGeometryControlData.Q (state z) i p)⁻¹
    else G.toN04PositiveGeometryControlData.Q (state z) i p
  let S₁ : E × PolarPoint → PolarPoint := fun z =>
    G.toN04PositiveGeometryControlData.σ (state z.1) i z.2
  let hfix : PolarPoint → ℝ := fun p => if inv then (H₀ i p.1)⁻¹ else H₀ i p.1
  have hsmooth := n04PositiveGeometry_reference_scalar_geometry (href i).1
  have hheight : ContDiff ℝ ∞ (fun p : PolarPoint => H₀ i p.1) :=
    hsmooth.2.2.1.comp contDiff_fst
  have hhfix : ContDiffOn ℝ ∞ hfix univ := by
    cases inv with
    | false => exact hheight.contDiffOn
    | true =>
        exact hheight.contDiffOn.inv (fun p _ => (hsmooth.2.2.2 p.1).ne')
  let RF : MixedJetRegularity U univ (fun x p => hfix p * Q x p) :=
    (n04Realization_mixedJetRegularity_fixedSpatial hU hhfix).mul RQ hU isOpen_univ
  let L : (E × PolarPoint) →L[ℝ] PolarPoint := ContinuousLinearMap.snd ℝ E PolarPoint
  let Jfix : SmoothDirections (U ×ˢ univ) (fun z : E × PolarPoint => hfix z.2) :=
    (((smoothDirectionsLinear L).restrict (hU.prod isOpen_univ) (subset_univ _)).comp_contDiff
      isOpen_univ hhfix (fun _ _ => mem_univ _)).congrOn (fun z _ => by
        simp only [Function.comp_apply, L, ContinuousLinearMap.coe_snd'])
  let JF := Jfix.mul JQ
  let JO : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => hfix (S₁ z) * Q z.1 (S₁ z)) := J.congr (fun z _ => by
    cases inv <;> simp only [hfix, Q, S₁, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_false, if_true, wholePositiveReferenceGaugeHeight_eq, div_eq_mul_inv,
      mul_inv_rev, inv_inv] <;> ring)
  have hfixed (a b : ℕ) (hab : a + b ≤ N) : |mixedDerivative a b hfix (S₁ (x, y))| ≤ M := by
    have ha : a ≤ N := by omega
    cases inv
    · rw [show hfix = fun p : PolarPoint => H₀ i p.1 by rfl,
        mixedDerivative_radialFunction]
      split_ifs with hb
      · exact ((hrefjets i a ha (S₁ (x, y)).1).2.2.1).trans (hraise hBrD)
      · simpa only [abs_zero] using zero_le_one.trans hM
    · rw [show hfix = fun p : PolarPoint => (fun r : ℝ => (H₀ i r)⁻¹) p.1 by rfl,
        mixedDerivative_radialFunction]
      split_ifs with hb
      · exact ((hrefjets i a ha (S₁ (x, y)).1).2.2.2).trans (hraise hBrD)
      · simpa only [abs_zero] using zero_le_one.trans hM
  have houter (j : ℕ) (_hj : 0 < j) (hjn : j ≤ n) (u : StateAngleWord j) (hu : u.stateArity ≤ K)
      (a : Fin j → E × PolarPoint)
      (ha : ∀ l, if u.isState l then (a l).2 = 0 else (a l).1 = 0)
      (hb : ∀ l, p (a l).1 ≤ 1 ∧ q (a l).1 ≤ R ∧ ‖(a l).2‖ ≤ 1) :
      ‖JF.D j (x, S₁ (x, y)) a‖ ≤ M' * parameterHeightWeight H u.stateArity *
        t ^ (u.angleArity + shift * u.stateArity) := by
    let Z := (2 : ℝ) ^ u.angleArity * M * M * parameterHeightWeight H u.stateArity *
      t ^ (u.angleArity + shift * u.stateArity)
    have hZ : 0 ≤ Z := mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans hM))
        (zero_le_one.trans hM)) (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _)
    have hbound := n04PositiveGeometry_joint_word_bound_of_mixed JF RF hU isOpen_univ
      (hcU.prod convex_univ) (fun v => p v ≤ 1 ∧ q v ≤ R) u hx (mem_univ _) hZ
      (fun a b hab v hv => by
        have h := n04PositiveGeometry_fixedSpatialProduct_power_bound isOpen_univ hhfix RQ
          a b u.stateArity shift (mem_univ _)
          (RF.parameter a b (S₁ (x, y)) (mem_univ _)) hx v
          (zero_le_one.trans hM) (zero_le_one.trans hM) hH ht
          (fun r s hrs => hfixed r s (by have := u.arity_sum; omega))
          (fun r s hrs => (hrawQ u.stateArity hu r s
            (by have := u.arity_sum; omega) v hv).trans
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hraise hAD) (parameterHeightWeight_nonneg hH _))
                (pow_nonneg (zero_le_one.trans ht) _)))
        simpa only [hab, Z] using h) a ha
      (fun l => ⟨⟨(hb l).1, (hb l).2.1⟩, (hb l).2.2⟩)
    have htwo : (2 : ℝ) ^ u.angleArity * 2 ^ u.angleArity ≤ P₀ := by
      rw [← mul_pow]
      norm_num only [show (2 : ℝ) * 2 = 4 by norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by have := u.arity_sum; omega)
    calc
      _ ≤ Z * 2 ^ u.angleArity := hbound
      _ = ((2 : ℝ) ^ u.angleArity * 2 ^ u.angleArity * M ^ 2) *
          parameterHeightWeight H u.stateArity * t ^ (u.angleArity + shift * u.stateArity) := by
        dsimp only [Z]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htwo
          (pow_nonneg (zero_le_one.trans hM) _)) (parameterHeightWeight_nonneg hH _))
        (pow_nonneg (zero_le_one.trans ht) _)
  let ni : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hnN⟩
  have hm := hmoving ni (U ×ˢ univ) (U ×ˢ univ)
    (fun z : E × PolarPoint => hfix z.2 * Q z.1 z.2) S₁ JF JS JO
    (x, y) ⟨hx, mem_univ _⟩ ⟨hx, mem_univ _⟩ p q R hR M' H t hM' hH hHM' ht
    K shift hshift houter (fun j hj hjn u hu a ha hb =>
      (hrawS j hj (hjn.trans hnN) u hu a ha hb).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ((hraise hAD).trans hMM') (parameterHeightWeight_nonneg hH _))
          (pow_nonneg (zero_le_one.trans ht) _))) hn w hw v hpure hbox
  have hcost : cm ni * M' ^ (2 * n + 2) ≤ B * E₀ ^ B := by
    calc
      _ ≤ Cm * M' ^ (2 * N + 2) := mul_le_mul (hcmCm ni)
        (pow_le_pow_right₀ hM' (by omega)) (pow_nonneg (zero_le_one.trans hM') _)
        (zero_le_one.trans hCm)
      _ = (Cm * P₀ ^ (2 * N + 2)) * M ^ (4 * N + 4) := by
        dsimp only [M']
        rw [mul_pow, ← pow_mul, show 2 * (2 * N + 2) = 4 * N + 4 by omega]
        ring
      _ ≤ B₀ * E₀ ^ B₀ := hpack E₀ hE₀
      _ ≤ B * E₀ ^ B := mul_le_mul hB₀B (Real.rpow_le_rpow_of_exponent_le hE₀ hB₀B)
        (Real.rpow_nonneg (zero_le_one.trans hE₀) _) (zero_le_one.trans hB)
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost (parameterHeightWeight_nonneg hH _))
    (pow_nonneg (zero_le_one.trans ht) _))

end ContinuousFlexibility.Analysis
