import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseFamily
import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBasePrefixRadius
import ContinuousFlexibility.Analysis.CircleSobolevPointwise

/-!
# Angular power bounds with one low order for a circle family

The circle evaluation loss is added to the loss sequence before the low
order is chosen. A finite parameter prefix then pays one power per
parameter derivative. The sample-height factor survives evaluation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {p : ℕ → Seminorm ℝ E}

/-- The low order is independent of the parameter prefix. The high
loss and the parameter charge are chosen before the spatial order and
the low-ball radius. Every supplied genuine circle tower has this bound. -/
theorem N04PulledFieldsFixedBaseFamily.circle_diagonal_angular_power
    {g : I → E → H.Space} (hg : N04PulledFieldsFixedBaseFamily p H.grading U g)
    (hp : Monotone p) (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m)) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ K → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (J : SmoothDirections U (g i)) x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ m θ,
        |iteratedDeriv b (H.decode (J.D k x (fun _ => w)) m) θ| ≤
          C * T.H (T.sample m) ^ γ *
            (1 + p (N + highLoss) x + p (N + highLoss) w) ^
              (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
  obtain ⟨oldBase, d, hjet⟩ := hg.oneHigh
  obtain ⟨B, hB, hprefix⟩ := n04PulledFields_fixedBase_affine_prefix_power
    p hp hIp oldBase (fun k => 1 + d k)
  refine ⟨B, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨B + shift * K + 1, shift, fun R hR N k hk b hb => ?_⟩
  obtain ⟨Cj, hCj, hcj⟩ := hjet k R hR (b + 1)
  obtain ⟨Ci, hCi, hci⟩ := hshift R hR N
  let c : ℝ := 2 * circleSobolevConstant
  have hc : 0 ≤ c := mul_nonneg (by norm_num) circleSobolevConstant_nonneg
  refine ⟨c * (Cj * Ci), mul_nonneg hc (mul_nonneg hCj (zero_le_one.trans hCi)), ?_⟩
  intro i J x hx w hxlow hwlow m θ
  let high : ℕ := N + (B + shift * K + 1)
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
  have hindex : B + N + shift * K + 1 = high := by
    dsimp only [high]
    omega
  have hscale := hci k hk b hb x hxlow (fun _ : Fin k => w) (fun _ => hwlow) Q hQ
    (by simpa only [hindex] using hxQ) (fun _ => by simpa only [hindex] using hwQ)
  have hwold : p oldBase w ≤ 1 := (hp hB w).trans hwlow
  have htame : tameJetSize p k (b + 1) (d k) oldBase x (fun _ => w) ≤
      (1 + p (b + (1 + d k)) x) + ∑ _j : Fin k, p (b + (1 + d k)) w := by
    simpa only [tameJetSize, multilinearTameSize, Nat.add_assoc] using
      multilinearTameSize_le_affine (p oldBase) (p (b + 1 + d k)) k
        (a := 1 + p (b + 1 + d k) x) (by positivity) (fun _ : Fin k => w)
        (fun _ => hwold)
  have hgrade : H.grading (b + 1) (J.D k x (fun _ => w)) ≤
      (Cj * Ci) * Q ^ (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
    calc
      _ ≤ Cj * tameJetSize p k (b + 1) (d k) oldBase x (fun _ => w) :=
        hcj i J x hx ((hp hB x).trans hxlow) (fun _ => w)
      _ ≤ Cj * ((1 + p (b + (1 + d k)) x) + ∑ _j : Fin k, p (b + (1 + d k)) w) :=
        mul_le_mul_of_nonneg_left htame hCj
      _ ≤ Cj * (Ci * Q ^ (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hscale hCj
      _ = _ := by ring
  have hheight : 0 ≤ T.H (T.sample m) ^ γ := Real.rpow_nonneg (hpos m).le γ
  calc
    _ ≤ (c * H.grading (b + 1) (J.D k x (fun _ => w))) * T.H (T.sample m) ^ γ :=
      circleModel_iteratedDeriv_abs_le hH hpos _ m b θ
    _ ≤ (c * ((Cj * Ci) * Q ^ (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)))) *
        T.H (T.sample m) ^ γ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrade hc) hheight
    _ = _ := by dsimp only [Q, high]; ring

end ContinuousFlexibility.Analysis
