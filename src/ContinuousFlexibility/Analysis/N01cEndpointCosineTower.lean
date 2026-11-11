import ContinuousFlexibility.Analysis.N01cCosineAngularStateJets
import ContinuousFlexibility.Analysis.N01cGradedJetContinuity
import ContinuousFlexibility.Analysis.N01cEndpointMixedPowerAlgebra

/-!
# From actual endpoint estimates to joint cosine-speed towers

At radial order zero the endpoint weight is one. A finite parameter
prefix therefore has a uniform grading-unit-ball estimate throughout
each physical component. The exact signed formula transfers that
estimate to all real cosine times, including the zero-sine times.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

variable {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem EndpointMixedPowerBounds.angular_unit_bound
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {I : ι → Set ℝ} {δ : ι → PolarPoint → ℝ} {H E : ι → ℝ}
    {f : ι → X → PolarPoint → ℝ}
    (hf : EndpointMixedPowerBounds p center base loss U (fun m => I m ×ˢ univ)
      δ (fun m _ => H m) (fun m _ => E m) f)
    (hp : Monotone p) (hlow : ∀ x ∈ U, p base (x - center) ≤ 1)
    (m : ι) (hE : 1 ≤ E m) (b K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, k ≤ K →
      ∀ r ∈ I m, ∀ θ : ℝ,
      ∀ J : SmoothDirections U (fun x => iteratedDeriv b (fun η => f m x (r, η)) θ),
      ∀ x ∈ U, ∀ R : ℝ, 1 ≤ R → p (max base (b + loss)) (x - center) ≤ R →
      ∀ v : Fin k → X, (∀ i, p (max base (b + loss)) (v i) < 1) →
        |J.D k x v| ≤ B * R := by
  obtain ⟨C, A, hC, hA, hb⟩ := hf K b
  let B : ℝ := C * E m ^ A * max 1 (H m)
  have hCE : 0 ≤ C * E m ^ A :=
    mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hB : 0 ≤ B := mul_nonneg hCE (zero_le_one.trans (le_max_left _ _))
  refine ⟨B, hB, ?_⟩
  intro k hk r hr θ J x hx R hR hxR v hv
  let J0 : SmoothDirections U (fun y => mixedDerivative 0 b (f m y) (r, θ)) :=
    J.congr (fun y _ => by simp only [mixedDerivative, iteratedDeriv_zero])
  have hvl (i : Fin k) : p base (v i) ≤ 1 :=
    ((hp (le_max_left base (b + loss))) (v i)).trans (hv i).le
  have hxh : p (b + loss) (x - center) ≤ R :=
    ((hp (le_max_right base (b + loss))) (x - center)).trans hxR
  have hvh (i : Fin k) : p (b + loss) (v i) ≤ R :=
    (((hp (le_max_right base (b + loss))) (v i)).trans (hv i).le).trans hR
  have hraw : |J.D k x v| ≤ C * E m ^ A * parameterHeightWeight (H m) k *
      R ^ ((b : ℝ) / ((b : ℝ) + 1)) := by
    simpa only [pow_zero, one_mul, Nat.zero_add, Real.norm_eq_abs,
      J0, SmoothDirections.congr] using
        hb m k hk 0 b (by omega) (r, θ) ⟨hr, mem_univ _⟩ J0
          x hx (hlow x hx) v hvl R hR hxh hvh
  have hW : parameterHeightWeight (H m) k ≤ max 1 (H m) := by
    unfold parameterHeightWeight
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hcoef : C * E m ^ A * parameterHeightWeight (H m) k ≤ B :=
    mul_le_mul_of_nonneg_left hW hCE
  exact hraw.trans (mul_le_mul hcoef
    (Real.rpow_le_self_of_one_le hR (spatialOrder_fraction_le_one (le_refl b)))
    (Real.rpow_nonneg (zero_le_one.trans hR) _) hB)

private theorem abs_signedCosine_coefficients_le {c : ℝ}
    (hc : 0 ≤ c) (t : ℝ) :
    |c * |Real.sin t|| ≤ c ∧
      |c * (|Real.sin t| - Real.sin t)| ≤ 2 * c := by
  constructor
  · rw [abs_mul, abs_of_nonneg hc, abs_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t) hc).trans_eq (mul_one _)
  · rw [abs_mul, abs_of_nonneg hc]
    calc
      c * ||Real.sin t| - Real.sin t| ≤ c * (||Real.sin t|| + |Real.sin t|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hc
      _ = c * (|Real.sin t| + |Real.sin t|) := by rw [abs_abs]
      _ ≤ c * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add (Real.abs_sin_le_one t)
          (Real.abs_sin_le_one t)) hc
      _ = 2 * c := by ring

/-- The same chosen grading order controls the signed combination at
every real time. No division by the sine or the endpoint distance occurs. -/
theorem signedCosineAngularJet_unit_bounds
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (center : X) (base loss : ℕ)
    {U : Set X} (hU : IsOpen U) (hlow : ∀ x ∈ U, p base (x - center) ≤ 1)
    (l h : ι → ℝ) (δ : ι → PolarPoint → ℝ) (H E : ι → ℝ)
    (F A : ι → X → PolarPoint → ℝ)
    (hF : EndpointMixedPowerBounds p center base loss U
      (fun m => Ioo (l m) (h m) ×ˢ univ) δ (fun m _ => H m) (fun m _ => E m) F)
    (hA : EndpointMixedPowerBounds p center base loss U
      (fun m => Ioo (l m) (h m) ×ˢ univ) δ (fun m _ => H m) (fun m _ => E m) A)
    (m : ι) (hlh : l m < h m) (hE : 1 ≤ E m)
    (RF : MixedJetRegularity U (Ioo (l m) (h m) ×ˢ univ) (F m))
    (RA : MixedJetRegularity U (Ioo (l m) (h m) ×ˢ univ) (A m))
    (G : X × PolarPoint → ℝ)
    (heq : ∀ x ∈ U, ∀ t θ : ℝ, G (x, (t, θ)) =
      ((h m - l m) / 2 * |Real.sin t|) * F m x (rootCosinePath (l m) (h m) t, θ) +
      ((h m - l m) / 2 * (|Real.sin t| - Real.sin t)) *
        A m x (rootCosinePath (l m) (h m) t, θ))
    (b K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, k ≤ K → ∀ q : PolarPoint,
      ∀ J : SmoothDirections U (fun x => iteratedDeriv b (fun θ => G (x, (q.1, θ))) q.2),
      ∀ x ∈ U, ∀ R : ℝ, 1 ≤ R → p (max base (b + loss)) (x - center) ≤ R →
      ∀ v : Fin k → X, (∀ i, p (max base (b + loss)) (v i) < 1) →
        |J.D k x v| ≤ B * R := by
  obtain ⟨CF, hCF, hbF⟩ := hF.angular_unit_bound hp hlow m hE b K
  obtain ⟨CA, hCA, hbA⟩ := hA.angular_unit_bound hp hlow m hE b K
  let c : ℝ := (h m - l m) / 2
  have hc : 0 ≤ c := (div_pos (sub_pos.mpr hlh) (by norm_num)).le
  let B : ℝ := c * CF + (2 * c) * CA
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hc hCF)
    (mul_nonneg (mul_nonneg (by norm_num) hc) hCA)
  refine ⟨B, hB, ?_⟩
  intro k hk q J x hx R hR hxR v hv
  by_cases hs : Real.sin q.1 = 0
  · rw [signedCosineAngularJet_D_zero (F m) (A m) G heq b k q hs J hx v, abs_zero]
    exact mul_nonneg hB (zero_le_one.trans hR)
  · have hr := rootCosinePath_mem_Ioo_of_sin_ne_zero hlh hs
    have hJF := hbF k hk _ hr q.2 (RF.angularStateJets b _ hr q.2)
      x hx R hR hxR v hv
    have hJA := hbA k hk _ hr q.2 (RA.angularStateJets b _ hr q.2)
      x hx R hR hxR v hv
    have hcs := abs_signedCosine_coefficients_le hc q.1
    rw [signedCosineAngularJet_D_apply hU (F m) (A m) RF RA G heq b k q hr J hx v]
    calc
      _ ≤ |c * |Real.sin q.1| * (RF.angularStateJets b _ hr q.2).D k x v| +
          |c * (|Real.sin q.1| - Real.sin q.1) *
            (RA.angularStateJets b _ hr q.2).D k x v| := abs_add_le _ _
      _ = |c * |Real.sin q.1|| * |(RF.angularStateJets b _ hr q.2).D k x v| +
          |c * (|Real.sin q.1| - Real.sin q.1)| *
            |(RA.angularStateJets b _ hr q.2).D k x v| := by simp only [abs_mul]
      _ ≤ c * (CF * R) + (2 * c) * (CA * R) :=
        add_le_add (mul_le_mul hcs.1 hJF (abs_nonneg _) hc)
          (mul_le_mul hcs.2 hJA (abs_nonneg _) (mul_nonneg (by norm_num) hc))
      _ = B * R := by dsimp only [B]; ring

/-- Complete qualitative speed-tower construction from the two original
endpoint-controlled fields and the exact actual signed formula. -/
def continuousTimeSpeedTower_of_signedEndpointBounds
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hcp : ∀ n, Continuous (p n))
    (center : X) (base loss : ℕ)
    {U : Set X} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hlow : ∀ x ∈ U, p base (x - center) ≤ 1)
    (l h : ι → ℝ) (δ : ι → PolarPoint → ℝ) (H E : ι → ℝ)
    (F A : ι → X → PolarPoint → ℝ)
    (hF : EndpointMixedPowerBounds p center base loss U
      (fun m => Ioo (l m) (h m) ×ˢ univ) δ (fun m _ => H m) (fun m _ => E m) F)
    (hA : EndpointMixedPowerBounds p center base loss U
      (fun m => Ioo (l m) (h m) ×ˢ univ) δ (fun m _ => H m) (fun m _ => E m) A)
    (m : ι) (hlh : l m < h m) (hE : 1 ≤ E m)
    (RF : MixedJetRegularity U (Ioo (l m) (h m) ×ˢ univ) (F m))
    (RA : MixedJetRegularity U (Ioo (l m) (h m) ×ˢ univ) (A m))
    (G : X × PolarPoint → ℝ) (hfinite : IsFiniteAffineTimeSmooth U G)
    (heq : ∀ x ∈ U, ∀ t θ : ℝ, G (x, (t, θ)) =
      ((h m - l m) / 2 * |Real.sin t|) * F m x (rootCosinePath (l m) (h m) t, θ) +
      ((h m - l m) / 2 * (|Real.sin t| - Real.sin t)) *
        A m x (rootCosinePath (l m) (h m) t, θ)) :
    ContinuousTimeSpeedTower U G := by
  let J := signedCosineAngularStateJets hU hlh (F m) (A m) RF RA G heq
  have hjets : ∀ b K : ℕ, ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, k ≤ K → ∀ q : PolarPoint, ∀ x ∈ U,
      ∀ R : ℝ, 1 ≤ R → p N (x - center) ≤ R →
      ∀ v : Fin k → X, (∀ i, p N (v i) < 1) →
        |(J b q).D k x v| ≤ C * R := by
    intro b K
    obtain ⟨C, hC, hb⟩ := signedCosineAngularJet_unit_bounds p hp center base loss
      hU hlow l h δ H E F A hF hA m hlh hE RF RA G heq b K
    exact ⟨max base (b + loss), C, hC,
      fun k hk q x hx R hR hxR v hv => hb k hk q (J b q) x hx R hR hxR v hv⟩
  exact continuousTimeSpeedTower_of_graded_stateAngularJets
    p hcp center hU hconv hfinite J hjets

end ContinuousFlexibility.Analysis
