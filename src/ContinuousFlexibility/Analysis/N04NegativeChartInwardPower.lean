import ContinuousFlexibility.Analysis.N04NegativeChartOpticalPowerControl
import ContinuousFlexibility.Analysis.N04NegativeGeometryNormalizedFactorBounds
import ContinuousFlexibility.Analysis.N01cMaterialShiftComparison

/-!
# Inward coordinates and the actual negative-half sample

The inward affine map has slope of absolute value one, so its complete
mixed parameter jets have the same norms as the original physical jets.
The two material comparisons preserve the exact height exponent. This
places the actual normalized factors in the same power algebra as the
divided optical speed, with no radial endpoint denominator.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- Both endpoint orientations have the same absolute spatial cost. -/
theorem n04NegativeChart_mixedDerivative_inward
    (f : PolarPoint → ℝ) (l h : ℝ) (side : Bool) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b
      (fun q => f (inwardComponentPoint l h side q.1, q.2)) p =
      n01ComponentRootOrientation side ^ a *
        mixedDerivative a b f (inwardComponentPoint l h side p.1, p.2) := by
  cases side <;> simp only [mixedDerivative, inwardComponentPoint,
    n01ComponentRootOrientation, Bool.false_eq_true, ↓reduceIte,
    iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_sub,
    smul_eq_mul, one_pow, one_mul]

namespace N04RealizationStart

variable (W : N04RealizationStart)

abbrev negativeHalfSample (e : ℕ ≃ N04PieceIndex W.D) (m : ℕ) (side : Bool) : ℝ :=
  W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))

/-- Transfer from a physical component point to the exact sample of its
selected half. The height power is unchanged in both comparisons. -/
theorem negativeHalf_point_weights (e : ℕ ≃ N04PieceIndex W.D) (γ A : ℝ) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧ ∀ m side r,
      r ∈ Ioo (W.C.left m) (W.C.right m) →
      W.T.H r ^ γ * W.T.E0 r ^ A ≤
        C * (W.T.H (W.negativeHalfSample e m side) ^ γ *
          W.T.E0 (W.negativeHalfSample e m side) ^ P) := by
  obtain ⟨C₀, P₀, hC₀, hP₀, hb₀⟩ := materialCell_weight_comparison W.hT W.radial.1 γ A
  obtain ⟨C₁, P₁, hC₁, hP₁, hb₁⟩ :=
    n04bActualTypedAtlas_negative_host_sample_weights W.hT W.hS W.through03 W.field
      e γ 0 P₀ hP₀.le
  refine ⟨C₀ * C₁, P₁, mul_pos hC₀ hC₁, hP₁, fun m side r hr => ?_⟩
  have hhost : W.T.H (W.T.sample (W.C.cell m)) ^ γ *
      W.T.E0 (W.T.sample (W.C.cell m)) ^ P₀ ≤
        C₁ * (W.T.H (W.negativeHalfSample e m side) ^ γ *
          W.T.E0 (W.negativeHalfSample e m side) ^ P₁) := by
    simpa only [Real.rpow_zero, mul_one] using
      hb₁ (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
        (W.C.cell m) (W.host m)
  calc
    _ ≤ C₀ * (W.T.H (W.T.sample (W.C.cell m)) ^ γ *
        W.T.E0 (W.T.sample (W.C.cell m)) ^ P₀) := by
      simpa only [mul_assoc] using (hb₀ (W.C.cell m) r (W.host m hr)).1
    _ ≤ C₀ * (C₁ * (W.T.H (W.negativeHalfSample e m side) ^ γ *
        W.T.E0 (W.negativeHalfSample e m side) ^ P₁)) :=
      mul_le_mul_of_nonneg_left hhost hC₀.le
    _ = _ := by ring

private theorem negativeHalf_parameter_weights (e : ℕ ≃ N04PieceIndex W.D) (A : ℝ) :
    ∃ C P : ℝ, 1 ≤ C ∧ 0 ≤ P ∧ ∀ m side r,
      r ∈ Ioo (W.C.left m) (W.C.right m) → ∀ k : ℕ,
      W.T.E0 r ^ A * parameterHeightWeight (W.T.H r ^ (3 / 4 : ℝ)) k ≤
        C * W.T.E0 (W.negativeHalfSample e m side) ^ P *
          parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k := by
  obtain ⟨C₀, P₀, hC₀, hP₀, hzero⟩ := W.negativeHalf_point_weights e 0 A
  obtain ⟨C₁, P₁, hC₁, hP₁, hpos⟩ := W.negativeHalf_point_weights e (3 / 4 : ℝ) A
  let C := 1 + C₀ + C₁
  let P := P₀ + P₁
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨C, P, hC, add_nonneg hP₀ hP₁, fun m side r hr k => ?_⟩
  have hE := W.floor (W.negativeHalfSample e m side)
  have hH : 0 ≤ W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  by_cases hk : k = 0
  · have hh : W.T.E0 r ^ A ≤ C₀ * W.T.E0 (W.negativeHalfSample e m side) ^ P₀ := by
      simpa only [Real.rpow_zero, one_mul] using hzero m side r hr
    simpa only [parameterHeightWeight, if_pos hk, mul_one] using hh.trans
      (mul_le_mul (show C₀ ≤ C by dsimp only [C]; linarith)
        (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hP₁))
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hC))
  · have hh := hpos m side r hr
    have he : C₁ * (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) *
        W.T.E0 (W.negativeHalfSample e m side) ^ P₁) ≤
      C * (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) *
        W.T.E0 (W.negativeHalfSample e m side) ^ P) :=
      mul_le_mul (show C₁ ≤ C by dsimp only [C]; linarith)
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hP₀)) hH)
        (mul_nonneg hH (Real.rpow_nonneg (zero_le_one.trans hE) _))
        (zero_le_one.trans hC)
    simpa only [parameterHeightWeight, if_neg hk, mul_assoc, mul_left_comm, mul_comm]
      using hh.trans he

/-- One actual physical power-controlled family pulls back to every
inward half at the original fixed indices. -/
def negativeHalf_inward_powerControl
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (e : ℕ ≃ N04PieceIndex W.D)
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ} {U : Set X}
    {f : X → PolarPoint → ℝ}
    (RF : MixedJetRegularity U (annularOpen W.D) f)
    (hf : MixedPowerBounds p center base loss U (annularOpen W.D)
      (fun q => W.T.H q.1 ^ (3 / 4 : ℝ)) (fun q => W.T.E0 q.1) f) :
    EndpointPowerControl p center base loss U
      (fun i : ℕ × Bool => Ioo (0 : ℝ) (W.negativeOpticalWidth i.1 i.2) ×ˢ univ)
      (fun _ _ => 1)
      (fun i _ => W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ))
      (fun i _ => W.T.E0 (W.negativeHalfSample e i.1 i.2))
      (fun i x q => f x (W.negativeInwardPoint i.1 i.2 q)) := by
  let Ω : ℕ × Bool → Set PolarPoint := fun i =>
    Ioo 0 (W.negativeOpticalWidth i.1 i.2) ×ˢ univ
  have hmap (i : ℕ × Bool) {q : PolarPoint} (hq : q ∈ Ω i) :
      W.negativeInwardPoint i.1 i.2 q ∈ annularOpen W.D :=
    W.negativeInwardPoint_mem_annular i.1 i.2 ⟨hq.1.1.le, hq.1.2.le⟩
  have hcomponent (i : ℕ × Bool) {q : PolarPoint} (hq : q ∈ Ω i) :
      (W.negativeInwardPoint i.1 i.2 q).1 ∈ Ioo (W.C.left i.1) (W.C.right i.1) := by
    have hh := hq.1.2.trans (W.negativeOpticalWidth_lt_component i.1 i.2)
    cases hside : i.2 <;> simp only [negativeInwardPoint, inwardComponentPoint,
      hside, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith only [hq.1.1, hh]
  let RG (i : ℕ × Bool) : MixedJetRegularity U (Ω i)
      (fun x q => f x (W.negativeInwardPoint i.1 i.2 q)) := {
    spatial := fun x hx => (RF.spatial x hx).comp
      (W.negativeInwardPoint_contDiff i.1 i.2).contDiffOn (fun q hq => hmap i hq)
    parameter := fun a b q hq =>
      (smoothDirections_postcompCLM (RF.parameter a b _ (hmap i hq))
        (n01ComponentRootOrientation i.2 ^ a • ContinuousLinearMap.id ℝ ℝ)).congr
          (fun x hx => by
            simpa only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using
              (n04NegativeChart_mixedDerivative_inward (f x)
                (W.C.left i.1) (W.C.right i.1) i.2 a b q).symm) }
  refine ⟨RG, ?_⟩
  intro K s
  obtain ⟨Cf, Af, hCf, hAf, hb⟩ := hf K s
  obtain ⟨Cw, Aw, hCw, hAw, hw⟩ := W.negativeHalf_parameter_weights e Af
  refine ⟨Cf * Cw, Aw, one_le_mul_of_one_le_of_one_le hCf hCw, hAw, ?_⟩
  intro i k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  let J0 := RF.parameter a b (W.negativeInwardPoint i.1 i.2 q) (hmap i hq)
  have he : J.D k x v = n01ComponentRootOrientation i.2 ^ a * J0.D k x v := by
    apply (congrArg (fun A : X [×k]→L[ℝ] ℝ => A v)
      (J.unique ((RG i).parameter a b q hq) k x hx)).trans
    change (smoothDirections_postcompCLM J0
      (n01ComponentRootOrientation i.2 ^ a • ContinuousLinearMap.id ℝ ℝ)).D k x v = _
    simp only [smoothDirections_postcompCLM_D_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
  have hσ : |n01ComponentRootOrientation i.2| = 1 := by
    cases i.2 <;> norm_num [n01ComponentRootOrientation]
  have hnorm : ‖J.D k x v‖ = ‖J0.D k x v‖ := by
    rw [he, norm_mul, Real.norm_eq_abs, abs_pow, hσ, one_pow, one_mul]
  have hraw := hb k hk a b hab _ (hmap i hq) J0 x hx hlow v hv R hR hhigh hvhigh
  have hcost := hw i.1 i.2 (W.negativeInwardPoint i.1 i.2 q).1 (hcomponent i hq) k
  change (1 : ℝ) ^ a * ‖J.D k x v‖ ≤ _
  rw [one_pow, one_mul, hnorm]
  exact hraw.trans (by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcost (zero_le_one.trans hCf))
      (Real.rpow_nonneg (zero_le_one.trans hR) (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)))
    simpa only [mul_assoc] using hh)

end N04RealizationStart

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeHalf_inward_powerControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeHalf_inward_powerControl
