import ContinuousFlexibility.Analysis.N04NegativeChartFixedBaseFamilies
import ContinuousFlexibility.Analysis.CircleStripAngularInterpolation

/-!
# Angular estimates with one low order for every state derivative

The low order absorbs only the loss at state order zero. For a finite
state prefix, the remaining loss is assigned a degree proportional to
the state order. State orders add in the transport Leibniz rule, so this
degree remains additive through arbitrarily many radial differentiations.
The state prefix changes the high shift and never the low order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {p : ℕ → Seminorm ℝ E} {U : Set E} {f : I → E → H.Space}

/-- Genuine angular jets use the degree `b + k * D` on the common
scale `N + K * D + 1`. In particular the base precedes `K`. -/
theorem N04FixedBaseSmoothFamilyOn.circle_diagonal_stateBudget
    (hf : N04FixedBaseSmoothFamilyOn p H.grading U f)
    (hp : Monotone p) (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m))
    (J : ∀ i, SmoothDirections U (f i)) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ D : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ K → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ m θ,
        |iteratedDeriv b (H.decode ((J i).D k x (fun _ => w)) m) θ| ≤
          C * T.H (T.sample m) ^ γ *
            (1 + p (N + K * D + B + 1) x + p (N + K * D + B + 1) w) ^
              (((b + k * D : ℕ) : ℝ) / ((N + K * D : ℕ) + 1 : ℝ)) := by
  classical
  obtain ⟨B₀, hjet⟩ := hf.jets J
  choose L hL using hjet
  obtain ⟨ib, il, hinterp⟩ := hIp
  let B : ℕ := max B₀ (max ib (1 + L 0 + il))
  have hB₀ : B₀ ≤ B := le_max_left _ _
  have hib : ib ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hzero : 1 + L 0 + il ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, fun K => ?_⟩
  let D : ℕ := 1 + il + ∑ j : Fin (K + 1), L j.val
  have hD (k : ℕ) (hk : k ≤ K) : 1 + L k + il ≤ D := by
    have hs : L k ≤ ∑ j : Fin (K + 1), L j.val :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (K + 1)))
    dsimp only [D]
    omega
  have hoff (k : ℕ) (hk : k ≤ K) : 1 + L k + il ≤ B + k * D := by
    by_cases hk0 : k = 0
    · simpa only [hk0, Nat.zero_mul, Nat.add_zero] using hzero
    · have hm : D ≤ k * D := by
        simpa only [one_mul] using Nat.mul_le_mul_right D (Nat.one_le_iff_ne_zero.mpr hk0)
      exact (hD k hk).trans (hm.trans (Nat.le_add_left _ _))
  refine ⟨D, fun R hR N k hk b hb => ?_⟩
  let high : ℕ := N + K * D + B + 1
  have hhigh : B < high := by dsimp only [high]; omega
  have hkd : k * D ≤ K * D := Nat.mul_le_mul_right D hk
  have horder : B < b + 1 + L k → b + 1 + L k + il < high := by
    have ho := hoff k hk
    dsimp only [high]
    omega
  obtain ⟨Ci, hCi, hscale⟩ := interpolation_affine_family_le_common_scale p hp
    B il (b + 1 + L k) high hhigh horder
    (fun a c ha hac => hinterp B a c hib ha hac) R hR k
  obtain ⟨Cj, hCj, hj⟩ := hL k R hR (b + 1)
  let A : ℝ := 2 * circleSobolevConstant
  have hA : 0 ≤ A := mul_nonneg (by norm_num) circleSobolevConstant_nonneg
  refine ⟨A * Cj * Ci, mul_nonneg (mul_nonneg hA hCj) hCi,
    fun i x hx w hxlow hwlow m θ => ?_⟩
  let Q : ℝ := 1 + p high x + p high w
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p high) x, apply_nonneg (p high) w]
  have hxQ : p high x ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p high) w]
  have hwQ : p high w ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p high) x]
  have hcost : interpolationOrderCost B il (b + 1 + L k) ≤ b + k * D := by
    have ho := hoff k hk
    unfold interpolationOrderCost
    split_ifs <;> omega
  have hden : ((high : ℝ) - B) = ((N + K * D : ℕ) : ℝ) + 1 := by
    dsimp only [high]
    push_cast
    ring
  have hexponent :
      (interpolationOrderCost B il (b + 1 + L k) : ℝ) / ((high : ℝ) - B) ≤
        ((b + k * D : ℕ) : ℝ) / (((N + K * D : ℕ) : ℝ) + 1) := by
    rw [hden]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcost) (by positivity)
  have hs := (hscale x (fun _ : Fin k => w) Q hxlow (fun _ => hwlow)
    hxQ (fun _ => hwQ) hQ).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hQ hexponent) hCi)
  have ht : tameJetSize p k (b + 1) (L k) B₀ x (fun _ => w) ≤
      1 + p (b + 1 + L k) x + ∑ _j : Fin k, p (b + 1 + L k) w :=
    multilinearTameSize_le_affine (p B₀) (p (b + 1 + L k)) k
      (by positivity) (fun _ => w) (fun _ => (hp hB₀ w).trans hwlow)
  have hg := (hj i x hx ((hp hB₀ x).trans hxlow) (fun _ => w)).trans
    (mul_le_mul_of_nonneg_left (ht.trans hs) hCj)
  have hweight : 0 ≤ T.H (T.sample m) ^ γ := Real.rpow_nonneg (hpos m).le γ
  calc
    _ ≤ (A * H.grading (b + 1) ((J i).D k x (fun _ => w))) *
        T.H (T.sample m) ^ γ := circleModel_iteratedDeriv_abs_le hH hpos _ m b θ
    _ ≤ (A * (Cj * (Ci * Q ^
        (((b + k * D : ℕ) : ℝ) / (((N + K * D : ℕ) : ℝ) + 1))))) *
        T.H (T.sample m) ^ γ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hA) hweight
    _ = _ := by dsimp only [Q, high]; ring

/-- The same base controls the actual strip tower at every physical
radius, using selector-independent circle estimates. -/
theorem N04FixedBaseSmoothFamilyOn.realized_strip_angular_stateBudget
    (hf : N04FixedBaseSmoothFamilyOn p H.grading U f)
    (hp : Monotone p) (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m))
    (l h : ℕ → ℝ) (rsel : I → ℕ → ℝ)
    (hcover : ∀ m r, r ∈ Ioo (l m) (h m) → ∃ i, rsel i m = r)
    {g : ℕ → E × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (g m))
    (heq : ∀ i m, rsel i m ∈ Ioo (l m) (h m) → ∀ x ∈ U, ∀ θ,
      g m (x, (rsel i m, θ)) = H.decode (f i x) m θ) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ D : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ K → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) k 0 b x w y| ≤
          C * T.H (T.sample m) ^ γ *
            (1 + p (N + K * D + B + 1) x + p (N + K * D + B + 1) w) ^
              (((b + k * D : ℕ) : ℝ) / ((N + K * D : ℕ) + 1 : ℝ)) := by
  let A := hf.choose
  obtain ⟨B, hb⟩ := hf.circle_diagonal_stateBudget hp hIp hH hpos A
  refine ⟨B, fun K => ?_⟩
  obtain ⟨D, hD⟩ := hb K
  refine ⟨D, fun R hR N k hk b hbN => ?_⟩
  obtain ⟨C, hC, hc⟩ := hD R hR N k hk b hbN
  refine ⟨C, hC, fun m x hx w hxlow hwlow y hy => ?_⟩
  obtain ⟨i, hi⟩ := hcover m y.1 hy
  have hr : rsel i m ∈ Ioo (l m) (h m) := hi.symm ▸ hy
  have hid := jointMixedDiagonal_eq_circleAngularJet (J m) hH (A i) m hr
    (heq i m hr) k b x w hx y.2
  have hyeta : (rsel i m, y.2) = y := Prod.ext hi rfl
  have hid' := (congrArg
    (fun q : PolarPoint => jointMixedDiagonal (J m) k 0 b x w q) hyeta).symm.trans hid
  exact (congrArg abs hid').trans_le (hc i x hx w hxlow hwlow m y.2)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04FixedBaseSmoothFamilyOn.realized_strip_angular_stateBudget'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04FixedBaseSmoothFamilyOn.realized_strip_angular_stateBudget
