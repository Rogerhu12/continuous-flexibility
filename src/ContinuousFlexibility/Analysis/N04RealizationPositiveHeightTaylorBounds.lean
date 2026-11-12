import ContinuousFlexibility.Analysis.N04RealizationPositiveTracePrefix
import ContinuousFlexibility.Analysis.N04RealizationTaylorCorrectionBounds
import ContinuousFlexibility.Analysis.EndpointHeightValueBounds

/-!
# Quantitative jets of the actual positive Taylor height and reciprocal

The fixed collar, genuine raw endpoint towers and the retained low
Taylor control determine the existing height. Logarithmic trace bounds
and the fixed Taylor operator control its exponent. The exponential
amplitude is obtained from the original low collar estimate, so no
high-state envelope is exponentiated. Both reciprocal choices use the
same proof and the same parameter domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem n04Realization_signedExp_outer (inv : Bool) (a b : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ a (iteratedDeriv b
      (fun x : ℝ => if inv then Real.exp (-x) else Real.exp x)) y‖ =
      if inv then Real.exp (-y) else Real.exp y := by
  cases inv with
  | false => exact n04Realization_exp_outer_derivatives a b y
  | true =>
      change ‖iteratedFDeriv ℝ a (iteratedDeriv b (fun x : ℝ => Real.exp (-x))) y‖ = _
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, circle_iteratedDeriv_iteratedDeriv]
      have he : (fun x : ℝ => Real.exp (-x)) = (fun x => Real.exp ((-1) * x)) := by
        funext x
        rw [neg_one_mul]
      rw [he, Real.iteratedDeriv_exp_const_mul (a + b) (-1)]
      simp only [norm_mul, norm_pow,
        Real.norm_eq_abs, abs_neg, abs_one, one_pow, one_mul, neg_one_mul,
        abs_of_pos (Real.exp_pos (-y)), ite_true]

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_positiveHeightTaylor_parameter_bound (n k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (U : Set X), IsOpen U → ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ h : X → Bool → PolarPoint → ℝ,
      (∀ y ∈ U, ∀ side θ, ContDiffAt ℝ ∞ (h y side) (if side then r else l, θ)) →
      (∀ y ∈ U, ∀ side θ, 0 < h y side (if side then r else l, θ)) →
      ∀ JH : ∀ side, ∀ j : ℕ, j ≤ n → ∀ u θ,
        SmoothDirections U (fun y => iteratedDeriv u
          (radialBoundaryJet (h y side) (if side then r else l) j) θ),
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ H M t : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ t → δ⁻¹ ≤ M →
      (∀ side θ, (h x side (if side then r else l, θ))⁻¹ ≤ M) →
      (∀ side, ∀ j : ℕ, ∀ hj : j ≤ n, ∀ l : ℕ, l ≤ k →
        ∀ u : ℕ, u ≤ a + b → ∀ θ, ∀ z : Fin l → X, (∀ i, P (z i)) →
        ‖(JH side j hj u θ).D l x z‖ ≤ M * parameterHeightWeight H l * t ^ u) →
      ∀ Mlow : ℝ, 0 ≤ Mlow →
      (∀ side j, 0 < j → j ≤ n → ∀ θ,
        |positiveHeightTaylorData l r (fun _ => 1) (h x) side j θ| ≤ Mlow) →
      ((n + 1 : ℕ) : ℝ) * Mlow * δ ≤ 1 →
      ∀ inv : Bool, ∀ q : PolarPoint, ∀ J : SmoothDirections U
        (fun y => mixedDerivative a b (fun p => if inv then
          (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y) p)⁻¹
          else positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y) p) q),
      ‖J.D k x v‖ ≤ B * M ^ d * parameterHeightWeight H k * t ^ (a + b) := by
  obtain ⟨C0, d0, hC0, hd0, htrace⟩ :=
    n04Realization_positiveTrace_prefix_bound (X := X) n k (a + b) RH
  obtain ⟨CT, hCT, htaylor⟩ := n04Realization_endpointTaylorCorrection_parameter_bound
    (X := X) n (a + b)
  obtain ⟨CB, hCB, hcomp⟩ := n04Realization_finiteScalarComposition_bound (X := X) k a b RH
  let C1 : ℝ := 1 + CT * C0 + Real.exp 2
  let d1 : ℕ := a + b + d0 + 2
  have hC1 : 1 ≤ C1 := by
    dsimp only [C1]
    nlinarith [mul_nonneg (zero_le_one.trans hCT) (zero_le_one.trans hC0), Real.exp_pos 2]
  have hCTC0 : CT * C0 ≤ C1 := by dsimp only [C1]; linarith [Real.exp_pos 2]
  have hexpC : Real.exp 2 ≤ C1 := by
    dsimp only [C1]
    linarith [mul_nonneg (zero_le_one.trans hCT) (zero_le_one.trans hC0)]
  refine ⟨CB * C1 ^ (k + a + b + 1), d1 * (k + a + b + 1),
    one_le_mul_of_one_le_of_one_le hCB (one_le_pow₀ hC1),
    by
      have hd1 : 1 ≤ d1 := by dsimp only [d1]; omega
      simpa only [Nat.one_mul] using Nat.mul_le_mul hd1 (show 1 ≤ k + a + b + 1 by omega), ?_⟩
  intro U hU l r δ hδ hδ1 h hroot hpos JH x hx P v hv H M t hH hHR hM ht hδM
    hinv hraw Mlow hMlow hlow hsmall inv q J
  let A : X → Bool → ℕ → ℝ → ℝ :=
    fun y => positiveHeightTaylorData l r (fun _ => 1) (h y)
  have hlog (y : X) (side : Bool) : boundaryHeightLogRatio (fun _ => 1) (h y side) =
      (fun p => Real.log (h y side p)) := by
    funext p
    simp only [boundaryHeightLogRatio, div_one]
  have hA (y : X) (hy : y ∈ U) (side : Bool) (j : ℕ) (_hj : j ≤ n) :
      ContDiff ℝ ∞ (A y side j) :=
    contDiff_positiveHeightTaylorData contDiff_const (fun _ => zero_lt_one)
      (hroot y hy) (hpos y hy) side j
  let JA (side : Bool) (j : ℕ) (hj : j ≤ n) (u : ℕ) (θ : ℝ) :
      SmoothDirections U (fun y => iteratedDeriv u (A y side j) θ) :=
    (n04Realization_logBoundaryTrace_parameterTower hU (if side then r else l) j
      (fun y hy => hroot y hy side) (fun y hy => hpos y hy side)
      (fun d hd => JH side d (hd.trans hj)) u θ).congr (fun _ _ => by
        simp only [A, positiveHeightTaylorData, hlog])
  have hJA (side : Bool) (j : ℕ) (hj : j ≤ n) (d : ℕ) (hd : d ≤ k)
      (u : ℕ) (hu : u ≤ a + b) (θ : ℝ) (z : Fin d → X) (hz : ∀ i, P (z i)) :
      ‖(JA side j hj u θ).D d x z‖ ≤
        C0 * M ^ d0 * parameterHeightWeight H d * t ^ u := by
    let JR : SmoothDirections U (fun y => iteratedDeriv u
        (radialBoundaryJet (fun p => Real.log (h y side p)) (if side then r else l) j) θ) :=
      (JA side j hj u θ).congr (fun _ _ => by
        simp only [A, positiveHeightTaylorData, hlog])
    exact htrace U hU h (fun side => if side then r else l) hroot hpos JH x hx P
      H M t hH hHR hM ht hinv hraw side j hj d hd u hu θ JR z hz
  let T : X → PolarPoint → ℝ := fun y => endpointTaylorCorrection n l r δ (A y)
  let RT : MixedJetRegularity U univ T :=
    n04Realization_endpointTaylorCorrection_mixedJetRegularity hU n l r δ A hA JA
  let M1 : ℝ := C1 * M ^ d1
  have hM1 : 1 ≤ M1 := one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ hM)
  have hcoef : CT * δ⁻¹ ^ (a + b) * (C0 * M ^ d0) ≤ M1 := by
    calc
      _ ≤ CT * M ^ (a + b) * (C0 * M ^ d0) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδM _) (zero_le_one.trans hCT))
          (mul_nonneg (zero_le_one.trans hC0) (pow_nonneg (zero_le_one.trans hM) _))
      _ = (CT * C0) * M ^ (a + b + d0) := by rw [pow_add]; ring
      _ ≤ M1 := mul_le_mul hCTC0
        (pow_le_pow_right₀ hM (by dsimp only [d1]; omega))
        (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC1)
  have hT (d : ℕ) (hd : d ≤ k) (u w : ℕ) (huw : u + w ≤ a + b)
      (z : Fin d → X) (hz : ∀ i, P (z i)) :
      ‖(RT.parameter u w q (mem_univ _)).D d x z‖ ≤
        M1 * parameterHeightWeight H d * t ^ (u + w) := by
    have hb := htaylor U hU A hA JA l r δ hδ hδ1 d u w huw q
      (RT.parameter u w q (mem_univ _)) x hx z (C0 * M ^ d0) H t
      (mul_nonneg (zero_le_one.trans hC0) (pow_nonneg (zero_le_one.trans hM) _)) hH ht
      (fun side j hj => hJA side j hj d hd w (by omega) q.2 z hz)
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg hH d))
      (pow_nonneg (zero_le_one.trans ht) _))
  have hvalue (side : Bool) (θ : ℝ) : h x side (if side then r else l, θ) ≤ M := by
    have hb := hraw side 0 (Nat.zero_le n) 0 (Nat.zero_le k) 0 (Nat.zero_le (a + b)) θ
      Fin.elim0 (fun i => i.elim0)
    have hb' : |h x side (if side then r else l, θ)| ≤ M := by
      simpa only [smoothDirections_D_zero_apply (JH side 0 (Nat.zero_le n) 0 θ) hx,
        radialBoundaryJet, iteratedDeriv_zero, parameterHeightWeight, ite_true,
        pow_zero, mul_one, Real.norm_eq_abs] using hb
    exact (le_abs_self _).trans hb'
  have hamp := positiveHeightTaylorInterpolation_amplitude n hδ hδ1 hMlow hM
    (hpos x hx) hvalue hinv hlow hsmall q
  have hamp1 : Real.exp 2 * M ^ 2 ≤ M1 := mul_le_mul hexpC
    (pow_le_pow_right₀ hM (by dsimp only [d1]; omega))
    (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC1)
  let g : ℝ → ℝ := fun z => if inv then Real.exp (-z) else Real.exp z
  have hg : ContDiff ℝ ∞ g := by
    cases inv
    · exact Real.contDiff_exp
    · exact Real.contDiff_exp.comp contDiff_neg
  have houter (u : ℕ) (_hu : u ≤ a + b) (d : ℕ) (_hd : d ≤ k) :
      ‖iteratedFDeriv ℝ d (iteratedDeriv u g) (T x q)‖ ≤ M1 := by
    rw [n04Realization_signedExp_outer]
    cases inv
    · have hb : Real.exp (T x q) ≤ Real.exp 2 * M ^ 2 := by
        simpa only [positiveHeightTaylorInterpolation, one_mul, T, A] using hamp.1
      exact hb.trans hamp1
    · have hb : Real.exp (-T x q) ≤ Real.exp 2 * M ^ 2 := by
        simpa only [positiveHeightTaylorInterpolation, one_mul, Real.exp_neg, T, A] using hamp.2
      exact hb.trans hamp1
  have hfield (y : X) :
      (fun p => if inv then (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y) p)⁻¹
        else positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y) p) =
      (fun p => g (T y p)) := by
    funext p
    cases inv <;> simp only [g, T, A, Bool.false_eq_true, ite_false, ite_true,
      positiveHeightTaylorInterpolation, one_mul, Real.exp_neg]
  let JC : SmoothDirections U (fun y => mixedDerivative a b (fun p => g (T y p)) q) :=
    J.congr (fun y _ => by rw [hfield y])
  have hb := hcomp U hU univ isOpen_univ univ isOpen_univ T g RT hg.contDiffOn
    (fun _ _ _ _ => mem_univ _) q (mem_univ _) JC x hx P v hv H M1 t
    hH hHR hM1 ht houter hT
  calc
    _ ≤ CB * M1 ^ (k + a + b + 1) * parameterHeightWeight H k * t ^ (a + b) := hb
    _ = _ := by
      dsimp only [M1]
      rw [mul_pow, ← pow_mul]
      ring

end ContinuousFlexibility.Analysis
