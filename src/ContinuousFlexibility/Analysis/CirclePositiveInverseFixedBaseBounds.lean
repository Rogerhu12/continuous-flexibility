import ContinuousFlexibility.Analysis.CircleShiftedForwardFixedBaseBounds
import ContinuousFlexibility.Analysis.TameInverseFixedBaseBounds
import ContinuousFlexibility.Analysis.CircleInverseCompositionGrowth
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.N01cStateSeminorms

/-!
# Fixed low-base bounds for the genuine positive circle inverse

Only the already given genuine forward and inverse towers are used. The
inverse value bound comes from actual inverse composition; its source is
normalized as a continuous linear map. The fixed-base inverse theorem is
applied once at zero travel, and translation transports the same estimate
to every given tower of the literal positive inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

local instance circleFixedBaseInversePairSMul (M : CircleModelData) :
    SMul ℝ (M.Space × M.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

include hI in
/-- The true zero-travel inverse has a source-linear one-high value bound,
with base and loss fixed before the spatial order and the low-box radius. -/
theorem circlePositiveInverseComposeLinear_zero_fixedBase_value
    (JP : SmoothDirections (circlePositiveLiftDomain M ×ˢ univ)
      (fun z : M.Space × M.Space =>
        circlePositiveInverseComposeLinear hM hT hD hγ (fun _ => 0) z.1 z.2))
    (a : ℝ) (ha : 0 < a) :
    ∃ base loss : ℕ, ∀ R : ℝ, 1 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ e : M.Space,
        (∀ m θ, a ≤ deriv (circleAffineLift (fun _ => 0) (M.decode e) 1 m) θ) →
        M.grading base e ≤ R → ∀ y : M.Space,
          M.grading s (circlePositiveInverseComposeLinear hM hT hD hγ
            (fun _ => 0) e y) ≤ C *
              ((1 + M.grading (s + loss) e) * M.grading base y +
                M.grading (s + loss) y) := by
  classical
  obtain ⟨b₀, ell, hinterp⟩ := hI
  let base : ℕ := max b₀ (ell + 2)
  let loss : ℕ := base + ell + 2
  have hq : Monotone M.grading := gradedSeminorm_monotone _ _
  obtain ⟨A, hA, hHA⟩ := material_circle_power_upper hT hD hγ
  have hw := material_circle_sample_weights_pos hT hD
  refine ⟨base, loss, fun R hR => ?_⟩
  let I := {z : M.Space × M.Space //
    (∀ m θ, a ≤ deriv (circleAffineLift (fun _ => 0) (M.decode z.1) 1 m) θ) ∧
      M.grading base z.1 ≤ R ∧ M.grading base z.2 ≤ 1}
  let e : I → M.Space := fun i => i.val.1
  let u : I → M.Space := fun i => i.val.2
  have hgrow (s : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i : I,
      circleNorm T γ s (fun m => M.decode (u i) m ∘
        circleAffineInverse (fun _ => 0) (e i) m) ≤
          C * (1 + M.grading (s + loss) (e i) + M.grading (s + loss) (u i)) :=
    circleNorm_inverseCompose_family_growth hM hw.1 hw.2 hA hHA
      base ell (le_max_right _ _)
      (fun b c hb hc => hinterp base b c (le_max_left _ _) hb hc)
      R (zero_le_one.trans hR) e u
      (fun i => i.property.2.1) (fun i => i.property.2.2.trans hR)
      (fun _ => 0) (fun i => circleAffineInverse (fun _ => 0) (e i)) ha
      (fun i => i.property.1)
      (fun i => circleAffineInverse_left (fun _ => 0) (e i) ha i.property.1)
      (fun i => circleAffineInverse_right hM hT hD hγ (fun _ => 0) (e i)) s
  choose C hC hc using hgrow
  intro s
  let B : ℝ := ∑ j ∈ Finset.range (s + 1), C j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨B, hB, fun x hx hxR y => ?_⟩
  have hxW : x ∈ circlePositiveLiftDomain M :=
    (circlePositiveLiftDomain_iff hM (fun _ => 0) x).mpr
      (fun m θ => ha.trans_le (hx m θ))
  let P := circlePositiveInverseComposeLinear hM hT hD hγ (fun _ => 0)
  let L : M.Space →L[ℝ] M.Space :=
    inverseFamilyContinuousLinearMap P JP.continuousOn x
  have hL (v : M.Space) : L v = P x v :=
    inverseFamilyContinuousLinearMap_apply P JP.continuousOn hxW v
  have hunit (v : M.Space) (hv : M.grading base v < 1) :
      M.grading s (L v) ≤ B *
        (1 + M.grading (s + loss) x + M.grading (s + loss) v) := by
    have hsize : 0 ≤ 1 + M.grading (s + loss) x + M.grading (s + loss) v :=
      add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _)
    apply (circleGrading_le_iff_circleNorm hM s _ (mul_nonneg hB hsize)).mpr
    intro j hj
    have hdecode : M.decode (L v) =
        fun m θ => M.decode v m (circleAffineInverse (fun _ => 0) x m θ) := by
      rw [hL]
      exact circlePositiveInverseComposeLinear_decode hM hT hD hγ
        (fun _ => 0) x v hxW
    rw [hdecode]
    have hjC : C j ≤ B := Finset.single_le_sum (f := C) (fun k _ => hC k)
      (Finset.mem_range.mpr (by omega))
    have hhigh : 1 + M.grading (j + loss) x + M.grading (j + loss) v ≤
        1 + M.grading (s + loss) x + M.grading (s + loss) v :=
      add_le_add (add_le_add le_rfl (hq (Nat.add_le_add_right hj loss) x))
        (hq (Nat.add_le_add_right hj loss) v)
    exact (hc j ⟨(x, v), hx, hxR, hv.le⟩).trans
      ((mul_le_mul_of_nonneg_left hhigh (hC j)).trans
        (mul_le_mul_of_nonneg_right hjC hsize))
  let F : M.Space [×1]→L[ℝ] M.Space :=
    ContinuousMultilinearMap.ofSubsingleton ℝ M.Space M.Space (0 : Fin 1) L
  have hF (v : Fin 1 → M.Space) : F v = L (v 0) := by
    simp only [F, ContinuousMultilinearMap.ofSubsingleton_apply_apply]
  have hn := multilinear_bound_of_unitBall F (M.grading s) (M.grading base)
    (M.grading (s + loss)) (a := 1 + M.grading (s + loss) x) hB
    (fun v hv => by simpa only [hF, Fin.sum_univ_one] using hunit (v 0) (hv 0))
    (fun _ : Fin 1 => y)
  rw [hF, hL] at hn
  have he0 : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  simpa only [P, multilinearTameSize, Fin.prod_univ_one, Fin.sum_univ_one,
    he0, Finset.prod_empty, mul_one] using hn

include hM in
private theorem circleFixedBase_decode_deriv_smul
    (c : ℝ) (e : M.Space) (m : ℕ) (θ : ℝ) :
    deriv (M.decode (c • e) m) θ = c * deriv (M.decode e m) θ := by
  have he : HasDerivAt (M.decode e m) (deriv (M.decode e m) θ) θ :=
    (((hM.2.2.2.1 e).1 m).1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hf : M.decode (c • e) m = fun t => c * M.decode e m t := by
    funext t
    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun (congrFun (M.decode.map_smul c e) m) t
  exact (congrArg (fun f : ℝ → ℝ => deriv f θ) hf).trans (he.const_mul c).deriv

include hD hT hγ hM in
private theorem circleFixedBase_common_lower_domain (a : ℝ) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : Set M.Space, IsOpen U ∧
      U ⊆ circlePositiveLiftDomain M ∧
      (∀ e : M.Space,
        (∀ m θ, a ≤ deriv (circleAffineLift (fun _ => 0) (M.decode e) 1 m) θ) → e ∈ U) ∧
      ∀ e ∈ U, ∀ m θ,
        c ≤ deriv (circleAffineLift (fun _ => 0) (M.decode e) 1 m) θ := by
  let c : ℝ := min a 1 / 2
  let t : ℝ := 1 - c
  have hc : 0 < c := half_pos (lt_min ha zero_lt_one)
  have hca : c < a := (half_lt_self (lt_min ha zero_lt_one)).trans_le (min_le_left _ _)
  have ht : 0 < t := by
    have hmin : min a 1 ≤ 1 := min_le_right _ _
    dsimp only [t, c]
    linarith
  let U : Set M.Space := (fun e : M.Space => t⁻¹ • e) ⁻¹' circlePositiveLiftDomain M
  have hU : IsOpen U := (circlePositiveLiftDomain_isOpen hM hT hD hγ).preimage
    (continuous_const.smul continuous_id)
  have hprod (d : ℝ) : (1 + t⁻¹ * d) * t = t + d := by
    calc
      _ = t + (t⁻¹ * t) * d := by ring
      _ = t + d := by rw [inv_mul_cancel₀ ht.ne', one_mul]
  have hlow (e : M.Space) (he : e ∈ U) (m : ℕ) (θ : ℝ) :
      c < 1 + deriv (M.decode e m) θ := by
    have hh : 0 < 1 + deriv (M.decode (t⁻¹ • e) m) θ := he m θ
    rw [circleFixedBase_decode_deriv_smul hM] at hh
    have hp := mul_pos hh ht
    rw [hprod] at hp
    dsimp only [t] at hp
    linarith
  refine ⟨c, hc, U, hU, ?_, ?_, ?_⟩
  · intro e he m θ
    exact hc.trans (hlow e he m θ)
  · intro e he
    change ∀ m θ, 0 < 1 + deriv (M.decode (t⁻¹ • e) m) θ
    intro m θ
    rw [circleFixedBase_decode_deriv_smul hM]
    by_contra hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) ht.le
    rw [hprod] at hp
    have hh := he m θ
    rw [circleAffineLift_deriv hM] at hh
    dsimp only [t] at hp
    linarith
  · intro e he m θ
    rw [circleAffineLift_deriv hM]
    exact (hlow e he m θ).le

include hI in
/-- The given true inverse towers for all travel satisfy one common low
base. Only the derivative loss depends on the parameter order. -/
theorem circlePositiveInverseComposeLinear_fixedBase_oneHigh
    (JF : SmoothDirections univ (fun z : M.Space × M.Space =>
      circleShiftedChartComposeContinuousLinear hM hT hD hγ (fun _ => 0) z.1 z.2))
    (JP₀ : SmoothDirections (circlePositiveLiftDomain M ×ˢ univ)
      (fun z : M.Space × M.Space =>
        circlePositiveInverseComposeLinear hM hT hD hγ (fun _ => 0) z.1 z.2))
    (a : ℝ) (ha : 0 < a) :
    ∃ base : ℕ, ∀ n : ℕ, ∃ loss : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (travel : ℕ → ℝ)
        (JP : SmoothDirections (circlePositiveLiftDomain M ×ˢ univ)
          (fun z : M.Space × M.Space =>
            circlePositiveInverseComposeLinear hM hT hD hγ travel z.1 z.2)),
        ∀ x : M.Space × M.Space,
          (∀ m θ, a ≤ deriv (circleAffineLift travel (M.decode x.1) 1 m) θ) →
          pairGrading M.grading M.grading base x ≤ R → ∀ v : Fin n → M.Space × M.Space,
            M.grading s (JP.D n x v) ≤
              C * tameJetSize (pairGrading M.grading M.grading) n s loss base x v := by
  classical
  obtain ⟨c, hc, U, hU, hsub, hAU, hlow⟩ :=
    circleFixedBase_common_lower_domain hD hT hγ hM a ha
  obtain ⟨bv, lv, hv⟩ :=
    circlePositiveInverseComposeLinear_zero_fixedBase_value hD hT hγ hM hI JP₀ c hc
  obtain ⟨bf, lf, hf⟩ :=
    circleShiftedChartCompose_orderedJets_fixedBase_bound hD hT hγ hM hI
  let b : ℕ := max bv bf
  have hq : Monotone M.grading := gradedSeminorm_monotone _ _
  let L := circleShiftedChartComposeContinuousLinear hM hT hD hγ (fun _ => 0)
  let P := circlePositiveInverseComposeLinear hM hT hD hγ (fun _ => 0)
  let J : SmoothDirections (U ×ˢ univ) (fun z : M.Space × M.Space => L z.1 z.2) :=
    JF.restrict (hU.prod isOpen_univ) (subset_univ _)
  have hcont : ContinuousOn (fun z : M.Space × M.Space => P z.1 z.2) (U ×ˢ univ) :=
    JP₀.continuousOn.mono (fun x hx => ⟨hsub hx.1, hx.2⟩)
  let V : M.Space → M.Space →L[ℝ] M.Space := inverseFamilyContinuousLinearMap P hcont
  have hV (e : M.Space) (he : e ∈ U) (y : M.Space) : V e y = P e y :=
    inverseFamilyContinuousLinearMap_apply P hcont he y
  have hVc : ContinuousOn (fun z : M.Space × M.Space => V z.1 z.2) (U ×ˢ univ) :=
    continuousOn_inverseFamilyContinuousLinearMap P hcont
  have hleft (e : M.Space) (he : e ∈ U) (y : M.Space) : V e (L e y) = y := by
    have hp := circlePositiveInverseComposeLinear_eq_fixed hM hT hD hγ
      (fun _ => 0) c hc e (hlow e he)
    calc
      _ = P e (L e y) := hV e he _
      _ = circleInverseComposeLinear hM hT hD hγ (fun _ => 0) c hc e (L e y) :=
        congrArg (fun A : M.Space →ₗ[ℝ] M.Space => A (L e y)) hp
      _ = y := circleInverseComposeLinear_left_inverse hM hT hD hγ
        (fun _ => 0) c hc e y (hlow e he)
  have hright (e : M.Space) (he : e ∈ U) (y : M.Space) : L e (V e y) = y := by
    have hp := circlePositiveInverseComposeLinear_eq_fixed hM hT hD hγ
      (fun _ => 0) c hc e (hlow e he)
    calc
      _ = L e (P e y) := congrArg (L e) (hV e he y)
      _ = L e (circleInverseComposeLinear hM hT hD hγ (fun _ => 0) c hc e y) :=
        congrArg (fun A : M.Space →ₗ[ℝ] M.Space => L e (A y)) hp
      _ = y := circleInverseComposeLinear_right_inverse hM hT hD hγ
        (fun _ => 0) c hc e y (hlow e he)
  have hVB : ∀ R : ℝ, 1 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ e ∈ U, M.grading b e ≤ R → ∀ y : M.Space,
        M.grading s (V e y) ≤ C *
          ((1 + M.grading (s + lv) e) * M.grading b y + M.grading (s + lv) y) := by
    intro R hR s
    obtain ⟨C, hC, hb⟩ := hv R hR s
    refine ⟨C, hC, fun e he heR y => ?_⟩
    rw [hV e he y]
    exact (hb e (hlow e he) ((hq (le_max_left _ _) e).trans heR) y).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (hq (le_max_left _ _) y)
          (add_nonneg zero_le_one (apply_nonneg _ _))) le_rfl) hC)
  have hFB : ∀ n (R : ℝ), 1 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ e ∈ U, M.grading b e ≤ R → ∀ v : Fin n → M.Space,
        (∀ i, M.grading b (v i) ≤ R) → ∀ y : M.Space,
        M.grading s (inverseForwardJet J n e v y) ≤ C *
          ((1 + M.grading (s + (n + lf)) e + ∑ i, M.grading (s + (n + lf)) (v i)) *
            M.grading b y + M.grading (s + (n + lf)) y) := by
    intro n R hR s
    obtain ⟨C, hC, hb⟩ := hf n R hR s
    refine ⟨C, hC, fun e he heR v hv y => ?_⟩
    have h := hb (fun _ => 0) U hU J e he
      ((hq (le_max_right _ _) e).trans heR) v
      (fun i => (hq (le_max_right _ _) (v i)).trans (hv i)) y
    have hz : 0 ≤ 1 + M.grading (s + (n + lf)) e +
        ∑ i, M.grading (s + (n + lf)) (v i) :=
      add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
        (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (hq (le_max_right _ _) y) hz) le_rfl) hC)
  let JV := inverseFamilySmoothDirections J hU V hleft hright hVc
  let Jactual : SmoothDirections (U ×ˢ univ) (fun z : M.Space × M.Space => P z.1 z.2) :=
    JV.congr (fun x hx => hV x.1 hx.1 x.2)
  obtain ⟨base, hbase⟩ := inverseFamilySmoothDirections_fixedBase_oneHigh
    M.grading hq J V b lv lf hVB hFB
    (coordinate_hasInterpolation_pair hq hq hI hI) hU hleft hright hVc
  refine ⟨base, fun n => ?_⟩
  obtain ⟨loss, hloss⟩ := hbase n
  refine ⟨loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hb⟩ := hloss R hR s
  refine ⟨C, hC, fun travel JP x hx hxR v => ?_⟩
  have hxU : x ∈ U ×ˢ univ := ⟨hAU x.1 (by
    simpa only [circleAffineLift_deriv hM] using hx), mem_univ _⟩
  let τ := circleTranslationContinuousLinear hM hT hD hγ (fun m => -travel m)
  let JT : SmoothDirections (U ×ˢ univ) (fun z : M.Space × M.Space =>
      circlePositiveInverseComposeLinear hM hT hD hγ travel z.1 z.2) :=
    (solveSmoothDirectionsPostcomp Jactual τ).congr (fun z hz =>
      (circlePositiveInverseComposeLinear_eq_zero_travel hM hT hD hγ
        travel z.1 z.2 (hsub hz.1)).symm)
  have hjet := HasProjectiveJetsOn.unique (hU.prod isOpen_univ)
    (JP.restrict (hU.prod isOpen_univ)
      (fun z hz => ⟨hsub hz.1, hz.2⟩)).hasProjectiveJetsOn JT.hasProjectiveJetsOn n x hxU
  have hvalue : JP.D n x v = τ (JV.D n x v) := by
    simpa only [JT, SmoothDirections.congr, solveSmoothDirectionsPostcomp,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, Jactual] using
      congrArg (fun A : (M.Space × M.Space) [×n]→L[ℝ] M.Space => A v) hjet
  rw [hvalue]
  exact (circleTranslationContinuousLinear_grading_le hM hT hD hγ
    (fun m => -travel m) s (JV.D n x v)).trans (hb x hxU hxR v)

end ContinuousFlexibility.Statements
