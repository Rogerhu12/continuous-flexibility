module

public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseFamily
public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBasePrefixRadius

/-!
# Fixed-base powers after a weighted linear evaluation bound

The interpolation argument is carried out with abstract parameter and
target spaces. A fixed evaluation loss is included before choosing the
low base, while the evaluation weight remains an independent factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {I M E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
  {U : Set E} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}

/-- An evaluation bound with fixed loss preserves the weight and the
common low grading of a genuine family, for every supplied tower. -/
theorem N04PulledFieldsFixedBaseFamily.weighted_evaluation_power
    {f : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (hp : Monotone p) (hIp : HasInterpolation p)
    (ev : ℕ → F → M → ℝ) (weight : M → ℝ) (hweight : ∀ y, 0 ≤ weight y)
    (evaluationLoss : ℕ) (Ce : ℝ) (hCe : 0 ≤ Ce)
    (heval : ∀ b u y, |ev b u y| ≤ (Ce * q (b + evaluationLoss) u) * weight y) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ K → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (J : SmoothDirections U (f i)) x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ y,
        |ev b (J.D k x (fun _ => w)) y| ≤ C * weight y *
          (1 + p (N + highLoss) x + p (N + highLoss) w) ^
            (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
  obtain ⟨oldBase, d, hjet⟩ := hf.oneHigh
  obtain ⟨B, hB, hprefix⟩ := n04PulledFields_fixedBase_affine_prefix_power
    p hp hIp oldBase (fun k => evaluationLoss + d k)
  refine ⟨B, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨B + shift * K + 1, shift, fun R hR N k hk b hb => ?_⟩
  obtain ⟨Cj, hCj, hcj⟩ := hjet k R hR (b + evaluationLoss)
  obtain ⟨Ci, hCi, hci⟩ := hshift R hR N
  refine ⟨Ce * (Cj * Ci), mul_nonneg hCe (mul_nonneg hCj (zero_le_one.trans hCi)), ?_⟩
  intro i J x hx w hxlow hwlow y
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
  have htame : tameJetSize p k (b + evaluationLoss) (d k) oldBase x (fun _ => w) ≤
      (1 + p (b + (evaluationLoss + d k)) x) +
        ∑ _j : Fin k, p (b + (evaluationLoss + d k)) w := by
    simpa only [tameJetSize, multilinearTameSize, Nat.add_assoc] using
      multilinearTameSize_le_affine (p oldBase) (p (b + evaluationLoss + d k)) k
        (a := 1 + p (b + evaluationLoss + d k) x) (by positivity) (fun _ : Fin k => w)
        (fun _ => hwold)
  have hgrade : q (b + evaluationLoss) (J.D k x (fun _ => w)) ≤
      (Cj * Ci) * Q ^ (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
    calc
      _ ≤ Cj * tameJetSize p k (b + evaluationLoss) (d k) oldBase x (fun _ => w) :=
        hcj i J x hx ((hp hB x).trans hxlow) (fun _ => w)
      _ ≤ Cj * ((1 + p (b + (evaluationLoss + d k)) x) +
          ∑ _j : Fin k, p (b + (evaluationLoss + d k)) w) :=
        mul_le_mul_of_nonneg_left htame hCj
      _ ≤ Cj * (Ci * Q ^ (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hscale hCj
      _ = _ := by ring
  calc
    _ ≤ (Ce * q (b + evaluationLoss) (J.D k x (fun _ => w))) * weight y :=
      heval b _ y
    _ ≤ (Ce * ((Cj * Ci) * Q ^ (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)))) *
        weight y := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrade hCe) (hweight y)
    _ = _ := by dsimp only [Q, high]; ring

/-- A curried evaluation label is handled before specializing either
space. This keeps witness and label conversions out of model adapters. -/
theorem N04PulledFieldsFixedBaseFamily.weighted_evaluation_power_two
    {P : Type*} {f : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (hp : Monotone p) (hIp : HasInterpolation p)
    (ev : ℕ → F → M → P → ℝ) (weight : M → ℝ) (hweight : ∀ y, 0 ≤ weight y)
    (evaluationLoss : ℕ) (Ce : ℝ) (hCe : 0 ≤ Ce)
    (heval : ∀ b u y t, |ev b u y t| ≤ (Ce * q (b + evaluationLoss) u) * weight y) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ K → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (J : SmoothDirections U (f i)) x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ y t,
        |ev b (J.D k x (fun _ => w)) y t| ≤ C * weight y *
          (1 + p (N + highLoss) x + p (N + highLoss) w) ^
            (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
  obtain ⟨B, hB⟩ := hf.weighted_evaluation_power hp hIp
    (fun b u (y : M × P) => ev b u y.1 y.2) (fun y : M × P => weight y.1)
    (fun y => hweight y.1) evaluationLoss Ce hCe (fun b u y => heval b u y.1 y.2)
  refine ⟨B, fun K => ?_⟩
  obtain ⟨highLoss, shift, hprefix⟩ := hB K
  refine ⟨highLoss, shift, fun R hR N k hk b hb => ?_⟩
  obtain ⟨C, hC, hc⟩ := hprefix R hR N k hk b hb
  exact ⟨C, hC, fun i J x hx w hxlow hwlow y t =>
    hc i J x hx w hxlow hwlow (y, t)⟩

end ContinuousFlexibility.Analysis
