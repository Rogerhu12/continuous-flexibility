import ContinuousFlexibility.Analysis.AngularFiberFiniteJetBounds
import ContinuousFlexibility.Analysis.NonlinearInverseMaterialBounds
import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds

/-!
# Fixed-loss jets of the actual angular inverse pullback

Only the actual angular lower bound and the original positive-order
forward jets are inputs. The genuine augmented inverse and the genuine
composition use the existing weighted polynomial estimates. One low
state order and one derivative loss work at every positive output order.
No new angular map or collar width is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem angularMaterial_monomial_mono
    {a b W H : ℝ} (hab : a ≤ b) (hb : 0 ≤ b) (hW : 1 ≤ W) (hH : 0 ≤ H) :
    a * W ^ a * H ≤ b * W ^ b * H :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul hab (Real.rpow_le_rpow_of_exponent_le hW hab)
      (Real.rpow_nonneg (zero_le_one.trans hW) _) hb) hH

private theorem angularMaterial_one_le
    {a W H : ℝ} (ha : 1 ≤ a) (hW : 1 ≤ W) (hH : 1 ≤ H) :
    1 ≤ a * W ^ a * H := by
  have ha0 := zero_le_one.trans ha
  have hr : 1 ≤ W ^ a := Real.one_le_rpow hW ha0
  have hprod : 1 ≤ a * W ^ a := by
    simpa only [one_mul] using mul_le_mul ha hr zero_le_one ha0
  simpa only [one_mul] using
    mul_le_mul hprod hH zero_le_one
      (mul_nonneg ha0 (Real.rpow_nonneg (zero_le_one.trans hW) _))

private theorem angularMaterial_inverse_first_cost
    {M R κ : ℝ} (hM : 1 ≤ M) (hR : 1 ≤ R) (hinv : κ⁻¹ ≤ R) :
    1 + (1 + M) / κ ≤ 3 * R * M := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hd : (1 + M) / κ ≤ (1 + M) * R := by
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hinv (add_nonneg zero_le_one hM0)
  have hRM : 1 ≤ R * M := by
    simpa only [one_mul] using mul_le_mul hR hM zero_le_one hR0
  have htwo : (1 + M) * R ≤ 2 * R * M := by
    have hh := mul_le_mul_of_nonneg_right (show 1 + M ≤ 2 * M by linarith) hR0
    nlinarith only [hh]
  linarith only [hd, hRM, htwo]

/-- The constants precede every actual field, state and point. The
angular lower-bound cost and raw jets are source data, not inverse jets. -/
theorem angularFiberPullback_positiveJets_le_material
    {Z : Type} [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ Z} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ K : ℝ, 1 ≤ K →
      ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ z : Z, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ φ ξ : PolarPoint → ℝ, ∀ T : ℝ, T ≠ 0 →
        ContDiff ℝ ∞ φ → ContDiff ℝ ∞ ξ →
      ∀ hpositive : (∀ q : PolarPoint, 0 < deriv (fun θ => φ (q.1, θ)) q.2),
        (∀ r θ, φ (r, θ + T) = φ (r, θ) + T) →
      ∀ x : PolarPoint, ∀ κ : ℝ, 0 < κ → κ⁻¹ ≤ K * W ^ K →
        κ ≤ angularPartial φ (x.1, parameterizedCircleInverse φ x) →
        (∀ k, 1 ≤ k →
          ‖iteratedFDeriv ℝ k φ (x.1, parameterizedCircleInverse φ x)‖ ≤
            A k * W ^ (A k) * (1 + p (k + inputLoss) z)) →
        (∀ k, 1 ≤ k →
          ‖iteratedFDeriv ℝ k ξ (x.1, parameterizedCircleInverse φ x)‖ ≤
            A k * W ^ (A k) * (1 + p (k + inputLoss) z)) →
        ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k (angularFiberPullback φ ξ) x‖ ≤
          B k * W ^ (B k) * (1 + p (k + loss) z) := by
  classical
  obtain ⟨baseI, lossI, hinverse⟩ :=
    nonlinearInverse_positiveJets_le_material hp hI inputLoss
  let commonLoss := max inputLoss lossI
  obtain ⟨baseC, lossC, hcomposition⟩ :=
    coordinateComposition_fixed_loss_material_bound
      (X := PolarPoint) (Y := PolarPoint) (Z := ℝ) hp hI commonLoss
  refine ⟨max baseI baseC, lossC, ?_⟩
  intro K hK A hA
  let AI : ℕ → ℝ := fun j => max 1 (max (3 * K * A (j + 1)) (K + A (j + 1)))
  have hAI (j : ℕ) : 1 ≤ AI j := le_max_left _ _
  have hIcoeff (j : ℕ) : 3 * K * A (j + 1) ≤ AI j :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hIexp (j : ℕ) : K + A (j + 1) ≤ AI j :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hpack (j : ℕ) {W H : ℝ} (hW : 1 ≤ W) (hH : 0 ≤ H) :
      (3 * K * A (j + 1)) * W ^ (K + A (j + 1)) * H ≤
        AI j * W ^ (AI j) * H :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul (hIcoeff j) (Real.rpow_le_rpow_of_exponent_le hW (hIexp j))
        (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans (hAI j))) hH
  obtain ⟨BI, hBI, hIBound⟩ := hinverse AI hAI
  let AC : ℕ → ℝ := fun k => max 1 (max (A k) (BI k))
  have hAC (k : ℕ) : 1 ≤ AC k := le_max_left _ _
  have hAAC (k : ℕ) : A k ≤ AC k := (le_max_left _ _).trans (le_max_right _ _)
  have hBIAC (k : ℕ) : BI k ≤ AC k := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨BC, hBC, hCBound⟩ := hcomposition AC hAC
  let B : ℕ → ℝ := fun k => if k = 0 then 1 else BC (k - 1)
  refine ⟨B, ?_, ?_⟩
  · intro k
    by_cases hk : k = 0
    · simp only [B, if_pos hk, zero_lt_one]
    · simpa only [B, if_neg hk] using hBC (k - 1)
  intro z hz W hW φ ξ T hT hφ hξ hpositive hperiod x κ hκ hκinv hangle hφraw hξraw
  have hzI : p baseI z ≤ 1 := (hp (Nat.le_max_left _ _) z).trans hz
  have hzC : p baseC z ≤ 1 := (hp (Nat.le_max_right _ _) z).trans hz
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  let α := parameterizedCircleInverse φ
  let f : PolarPoint → PolarPoint := fun q => (q.1, φ q)
  let g : PolarPoint → PolarPoint := fun q => (q.1, α q)
  have hα : ContDiff ℝ ∞ α :=
    contDiff_parameterizedCircleInverse hT hφ hpositive hperiod
  have hf : ContDiff ℝ ∞ f := contDiff_fst.prodMk hφ
  have hg : ContDiff ℝ ∞ g := contDiff_fst.prodMk hα
  have hfg : f ∘ g = id := by
    funext q
    exact Prod.ext rfl (parameterizedCircleInverse_right_inverse hT hφ hperiod q)
  have hgf : g ∘ f = id := by
    funext q
    exact Prod.ext rfl (parameterizedCircleInverse_left_inverse hpositive q)
  have hfx : f (g x) = x := congrFun hfg x
  let L : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ g x
  have hL : L.comp (fderiv ℝ f (g x)) = ContinuousLinearMap.id ℝ PolarPoint := by
    calc
      _ = (fderiv ℝ g (f (g x))).comp (fderiv ℝ f (g x)) := by rw [hfx]
      _ = fderiv ℝ (g ∘ f) (g x) :=
        (fderiv_comp (g x) (hg.differentiable (by simp) (f (g x)))
          (hf.differentiable (by simp) (g x))).symm
      _ = _ := by rw [hgf, fderiv_id]
  let M : ℝ := A 1 * W ^ (A 1) * (1 + p (1 + inputLoss) z)
  have hM : 1 ≤ M := angularMaterial_one_le (hA 1) hW
    (le_add_of_nonneg_right (apply_nonneg _ _))
  have hradial : |radialPartial φ (g x)| ≤ M := by
    have hunit : |radialPartial φ (g x)| ≤ ‖fderiv ℝ φ (g x)‖ := by
      simpa [radialPartial, Prod.norm_def] using
        (fderiv ℝ φ (g x)).le_opNorm (1, 0)
    have hfirst : ‖fderiv ℝ φ (g x)‖ ≤ M := by
      simpa only [norm_iteratedFDeriv_one] using hφraw 1 le_rfl
    exact hunit.trans hfirst
  have hLfirst : ‖L‖ ≤ 1 + (1 + M) / κ := by
    have hfirst := norm_fderiv_parameterizedCircleInverse_le hT hφ hpositive hperiod
      hκ (zero_le_one.trans hM) x hangle hradial
    have hh := flowJet_augmented_jet_norm_le hα (n := 1) le_rfl x
    simp only [norm_iteratedFDeriv_one] at hh
    exact hh.trans (add_le_add_left hfirst 1)
  have hR : 1 ≤ K * W ^ K := by
    simpa only [one_mul] using
      mul_le_mul hK (Real.one_le_rpow hW hK0) zero_le_one hK0
  have hLbound : ‖L‖ ≤ AI 0 * W ^ (AI 0) * (1 + p (inputLoss + 1) z) := by
    calc
      _ ≤ 3 * (K * W ^ K) * M := hLfirst.trans
        (angularMaterial_inverse_first_cost hM hR hκinv)
      _ = (3 * K * A 1) * W ^ (K + A 1) * (1 + p (inputLoss + 1) z) := by
        rw [Real.rpow_add hW0]
        dsimp only [M]
        rw [Nat.add_comm 1 inputLoss]
        ring
      _ ≤ _ := hpack 0 hW (add_nonneg zero_le_one (apply_nonneg _ _))
  have hraw (j : ℕ) (hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ (j + 1) f (g x)‖ ≤
        AI j * W ^ (AI j) * (1 + p (j + inputLoss + 1) z) := by
    let H : ℝ := 1 + p (j + inputLoss + 1) z
    have hH : 1 ≤ H := le_add_of_nonneg_right (apply_nonneg _ _)
    have hindex : (j + 1) + inputLoss = j + inputLoss + 1 := by omega
    have hrawj : ‖iteratedFDeriv ℝ (j + 1) φ (g x)‖ ≤
        A (j + 1) * W ^ (A (j + 1)) * H := by
      simpa only [H, hindex] using hφraw (j + 1) (by omega)
    have hMj := angularMaterial_one_le (hA (j + 1)) hW hH
    have hcoeff : 2 * A (j + 1) ≤ 3 * K * A (j + 1) := by
      have hh := mul_le_mul_of_nonneg_right hK (zero_le_one.trans (hA (j + 1)))
      nlinarith only [hh, hA (j + 1)]
    calc
      _ ≤ 1 + A (j + 1) * W ^ (A (j + 1)) * H :=
        (flowJet_augmented_jet_norm_le hφ (by omega : 1 ≤ j + 1) (g x)).trans
          (add_le_add_left hrawj 1)
      _ ≤ (2 * A (j + 1)) * W ^ (A (j + 1)) * H := by linarith only [hMj]
      _ ≤ (3 * K * A (j + 1)) * W ^ (K + A (j + 1)) * H :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff
            (Real.rpow_le_rpow_of_exponent_le hW (by linarith only [hK0]))
            (Real.rpow_nonneg hW0.le _)
            (mul_nonneg (mul_nonneg (by norm_num) hK0)
              (zero_le_one.trans (hA (j + 1))))) (zero_le_one.trans hH)
      _ ≤ _ := hpack j hW (zero_le_one.trans hH)
  have hginv := hIBound z hzI W hW PolarPoint PolarPoint f g x
    hf.contDiffAt hg.contDiffAt (Filter.Eventually.of_forall fun q => congrFun hfg q)
    L hL hLbound hraw
  have houter (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k ξ (g x)‖ ≤
        AC k * W ^ (AC k) * (1 + p (k + commonLoss) z) := by
    exact (hξraw k hk).trans ((angularMaterial_monomial_mono (hAAC k)
      (zero_le_one.trans (hAC k)) hW (add_nonneg zero_le_one (apply_nonneg _ _))).trans
        (mul_le_mul_of_nonneg_left (add_le_add_left
          (hp (Nat.add_le_add_left (Nat.le_max_left inputLoss lossI) k) z) 1)
          (mul_nonneg (zero_le_one.trans (hAC k)) (Real.rpow_nonneg hW0.le _))))
  have hinner (k : ℕ) (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k g x‖ ≤
        AC k * W ^ (AC k) * (1 + p (k + commonLoss) z) := by
    exact (hginv k hk).trans ((angularMaterial_monomial_mono (hBIAC k)
      (zero_le_one.trans (hAC k)) hW (add_nonneg zero_le_one (apply_nonneg _ _))).trans
        (mul_le_mul_of_nonneg_left (add_le_add_left
          (hp (Nat.add_le_add_left (Nat.le_max_right inputLoss lossI) k) z) 1)
          (mul_nonneg (zero_le_one.trans (hAC k)) (Real.rpow_nonneg hW0.le _))))
  intro k hk
  have hb := hCBound z hzC W hW ξ g x hξ.contDiffAt hg.contDiffAt
    houter hinner (k - 1)
  have horder : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [horder] at hb
  have hk0 : k ≠ 0 := by omega
  simpa only [B, if_neg hk0] using hb

end ContinuousFlexibility.Analysis
