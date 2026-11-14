module

public import ContinuousFlexibility.Analysis.JointJetInterpolationBudget
public import ContinuousFlexibility.Analysis.TameUniformFamilyJets
public import ContinuousFlexibility.Analysis.CircleSobolevPointwise

/-!
# A common interpolation scale for the actual angular parameter jets

At each fixed maximum parameter order, all tame losses and the single
angular Sobolev loss enter one low order. That order is chosen before
the low-ball radius and before the total spatial order. Every primitive
angular jet then uses only its angular order divided by `N + 1` of the
same high scale. The original sample-height power is retained.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Absorbing a fixed loss in the low order leaves precisely the spatial
order as the exponent budget. The number of parameter slots affects
only the numerical constant. -/
theorem hasInterpolation_spatial_affine_rpow_bound
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasInterpolation p)
    (oldBase oldLoss : ℕ) :
    ∃ B : ℕ, oldBase ≤ B ∧ ∀ R : ℝ, 0 ≤ R → ∀ N b : ℕ, b ≤ N → ∀ n : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ∀ v : Fin n → E, ∀ Q : ℝ,
        p B x ≤ R → (∀ i, p B (v i) ≤ 1) →
        p (N + B + 1) x ≤ Q → (∀ i, p (N + B + 1) (v i) ≤ Q) → 1 ≤ Q →
        1 + p (b + oldLoss) x + ∑ i, p (b + oldLoss) (v i) ≤
          C * Q ^ ((b : ℝ) / ((N : ℝ) + 1)) := by
  obtain ⟨ib, il, hinterp⟩ := hIp
  let B : ℕ := max oldBase (max ib (oldLoss + il))
  have hib : ib ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hloss : oldLoss + il ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, le_max_left _ _, ?_⟩
  intro R hR N b hb n
  have hhigh : B < N + B + 1 := by omega
  have horder : B < b + oldLoss → b + oldLoss + il < N + B + 1 := by omega
  obtain ⟨C, hC, hc⟩ := interpolation_affine_family_le_common_scale p hp
    B il (b + oldLoss) (N + B + 1) hhigh horder
    (fun a c ha hac => hinterp B a c hib ha hac) R hR n
  refine ⟨C, hC, fun x v Q hx hv hxQ hvQ hQ => ?_⟩
  have hcost : interpolationOrderCost B il (b + oldLoss) ≤ b := by
    unfold interpolationOrderCost
    split_ifs <;> omega
  have hden : (((N + B + 1 : ℕ) : ℝ) - B) = (N : ℝ) + 1 := by
    push_cast
    ring
  have hexponent :
      (interpolationOrderCost B il (b + oldLoss) : ℝ) /
          (((N + B + 1 : ℕ) : ℝ) - B) ≤ (b : ℝ) / ((N : ℝ) + 1) := by
    rw [hden]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcost) (by positivity)
  exact (hc x v Q hx hv hxQ hvQ hQ).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ hexponent) hC)

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {I E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Uniform bounds for genuine diagonal parameter jets on one common
high scale. The fixed output shift `+1` is reserved for angular Sobolev
evaluation. -/
theorem UniformFamilyJetBounds.diagonal_spatial_interpolation
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f : I → E → F} {J : ∀ i, SmoothDirections U (f i)}
    (hJ : UniformFamilyJetBounds p q J) (hp : Monotone p)
    (hIp : HasInterpolation p) (nmax : ℕ) :
    ∃ B : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 →
        q (b + 1) ((J i).D k x (fun _ => w)) ≤
          C * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)) := by
  classical
  choose base loss hbound using fun k : Fin (nmax + 1) => hJ (k : ℕ)
  let oldBase : ℕ := ∑ k : Fin (nmax + 1), base k
  let oldLoss : ℕ := (∑ k : Fin (nmax + 1), loss k) + 1
  obtain ⟨B, hB, hinterp⟩ :=
    hasInterpolation_spatial_affine_rpow_bound p hp hIp oldBase oldLoss
  refine ⟨B, fun R hR N k hk b hb => ?_⟩
  let j : Fin (nmax + 1) := ⟨k, by omega⟩
  have hbase : base j ≤ B :=
    (Finset.single_le_sum (f := base) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans hB
  have hloss : 1 + loss j ≤ oldLoss := by
    have hj : loss j ≤ ∑ i : Fin (nmax + 1), loss i :=
      Finset.single_le_sum (f := loss) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    dsimp only [oldLoss]
    omega
  obtain ⟨Cj, hCj, hcj⟩ := hbound j (R + (k : ℝ)) (by positivity) (b + 1)
  obtain ⟨Ci, hCi, hci⟩ := hinterp R hR N b hb k
  refine ⟨Cj * Ci, mul_nonneg hCj hCi, fun i x hx w hxlow hwlow => ?_⟩
  let Q : ℝ := 1 + p (N + B + 1) x + p (N + B + 1) w
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + B + 1)) x,
      apply_nonneg (p (N + B + 1)) w]
  have hxQ : p (N + B + 1) x ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + B + 1)) w]
  have hwQ : p (N + B + 1) w ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + B + 1)) x]
  have hxbase : p (base j) x ≤ R := (hp hbase x).trans hxlow
  have hwbase : p (base j) w ≤ 1 := (hp hbase w).trans hwlow
  have hslots : (∑ _i : Fin k, p (base j) w) ≤ (k : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => hwbase)
      _ = _ := by simp
  have hlow : jetGrading p k (base j) (x, fun _ => w) ≤ R + (k : ℝ) := by
    rw [jetGrading_apply]
    exact add_le_add hxbase hslots
  have hraw : q (b + 1) ((J i).D k x (fun _ => w)) ≤
      Cj * (1 + p (b + 1 + loss j) x + ∑ _i : Fin k, p (b + 1 + loss j) w) := by
    have h := hcj i (x, fun _ : Fin k => w) ⟨hx, mem_univ _⟩ hlow
    simpa only [jetGrading_apply, add_assoc] using h
  have hindex : b + 1 + loss j ≤ b + oldLoss := by omega
  have horder : 1 + p (b + 1 + loss j) x + ∑ _i : Fin k, p (b + 1 + loss j) w ≤
      1 + p (b + oldLoss) x + ∑ _i : Fin k, p (b + oldLoss) w :=
    add_le_add (add_le_add le_rfl (hp hindex x))
      (Finset.sum_le_sum (fun _ _ => hp hindex w))
  have hscale := hci x (fun _ : Fin k => w) Q hxlow (fun _ => hwlow) hxQ
    (fun _ => hwQ) hQ
  exact (hraw.trans (mul_le_mul_of_nonneg_left horder hCj)).trans
    ((mul_le_mul_of_nonneg_left hscale hCj).trans_eq (by dsimp only [Q]; ring))

private theorem diagonal_spatial_evaluation_interpolation
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f : I → E → F} {J : ∀ i, SmoothDirections U (f i)}
    (hJ : UniformFamilyJetBounds p q J) (hp : Monotone p)
    (hIp : HasInterpolation p) (nmax : ℕ)
    (eval : ℕ → F → ℕ → ℝ → ℝ) (weight : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hweight : ∀ m, 0 ≤ weight m)
    (heval : ∀ u m b θ, |eval b u m θ| ≤ (c * q (b + 1) u) * weight m) :
    ∃ B : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ m θ,
        |eval b ((J i).D k x (fun _ => w)) m θ| ≤
          C * weight m * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)) := by
  obtain ⟨B, hb⟩ := hJ.diagonal_spatial_interpolation hp hIp nmax
  refine ⟨B, fun R hR N k hk b hbN => ?_⟩
  obtain ⟨C, hC, hCbound⟩ := hb R hR N k hk b hbN
  refine ⟨c * C, mul_nonneg hc hC, fun i x hx w hxlow hwlow m θ => ?_⟩
  have hg := hCbound i x hx w hxlow hwlow
  calc
    _ ≤ (c * q (b + 1) ((J i).D k x (fun _ => w))) * weight m :=
      heval _ m b θ
    _ ≤ (c * (C * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
          ((b : ℝ) / ((N : ℝ) + 1)))) * weight m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hc) (hweight m)
    _ = _ := by ring

/-- The actual circle decoder keeps the original sample-height factor.
All constants precede the family index, circle label, angle, state, and
direction. The common low order precedes both `R` and `N`. -/
theorem UniformFamilyJetBounds.circle_diagonal_angular_interpolation
    {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    {p : ℕ → Seminorm ℝ E} {U : Set E}
    {f : I → E → H.Space} {J : ∀ i, SmoothDirections U (f i)}
    (hJ : UniformFamilyJetBounds p H.grading J) (hp : Monotone p)
    (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m)) (nmax : ℕ) :
    ∃ B : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ m θ,
        |iteratedDeriv b (H.decode ((J i).D k x (fun _ => w)) m) θ| ≤
          C * T.H (T.sample m) ^ γ *
            (1 + p (N + B + 1) x + p (N + B + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)) := by
  exact diagonal_spatial_evaluation_interpolation hJ hp hIp nmax
    (fun b u m θ => iteratedDeriv b (H.decode u m) θ)
    (fun m => T.H (T.sample m) ^ γ) (2 * circleSobolevConstant)
    (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
    (fun m => Real.rpow_nonneg (hpos m).le γ)
    (fun u m b θ => circleModel_iteratedDeriv_abs_le hH hpos u m b θ)

end ContinuousFlexibility.Analysis
