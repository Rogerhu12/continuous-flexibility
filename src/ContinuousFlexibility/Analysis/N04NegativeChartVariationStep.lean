import ContinuousFlexibility.Analysis.N04NegativeChartVariationForcing
import ContinuousFlexibility.Analysis.N04NegativeGeometryLinearVariationBounds

/-!
# The actual positive-state variation step with all spatial derivatives

The original classical flow equation supplies the linear ODE for its
true parameter derivative. Its forcing is the existing canonical finite
sum of selected speed jets and strict lower parameter variations. The
marked product estimate and variation of constants retain one external
weight, while every state-order spatial power remains outside the
polynomial material envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q]

private theorem actualVariation_hasDerivAt
    {G Θ : E × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hΘ : ContDiff ℝ ∞ Θ)
    (hinit : ∀ q α, Θ (q, (0, α)) = α)
    (hflow : ∀ q t α, HasDerivAt (fun r => Θ (q, (r, α)))
      (G (q, (t, Θ (q, (t, α))))) t)
    {n : ℕ} (hn : 0 < n) (q : E) (t α : ℝ) (v : Fin n → E) :
    HasDerivAt (fun r => flowParameterField Θ n q v (r, α))
      (flowVariationCoefficient G Θ q (t, α) * flowParameterField Θ n q v (t, α) +
        flowVariationForcing J hΘ n q v (t, α)) t := by
  have hd := globalCircleVectorTrajectory_hasDerivAt_parameterJet_time hG
    (contDiff_flowInitialSlice hΘ α).continuous
    (fun z => hinit z α) (fun z r => hflow z r α) n q t v
  change HasDerivAt (fun r => flowParameterField Θ n q v (r, α))
    (flowParameterField (fun z => G (z.1, (z.2.1, Θ z))) n q v (t, α)) t at hd
  apply hd.congr_deriv
  rw [flowVariationForcing_eq_source_sub hG J hΘ hn]
  ring

private theorem actualVariation_zero
    {Θ : E × PolarPoint → ℝ}
    (hinit : ∀ q α, Θ (q, (0, α)) = α)
    {n : ℕ} (hn : 0 < n) (q : E) (α : ℝ) (v : Fin n → E) :
    flowParameterField Θ n q v (0, α) = 0 := by
  have he : (fun z : E => Θ (z, (0, α))) = fun _ : E => α :=
    funext (fun z => hinit z α)
  change iteratedFDeriv ℝ n (fun z : E => Θ (z, (0, α))) q v = 0
  rw [he]
  cases n with
  | zero => omega
  | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply,
      ContinuousMultilinearMap.zero_apply]

private theorem linearVariation_markedForcing_prefix
    (n K : ℕ) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {κ F : Q × ℝ → ℝ} {w : Q → ℝ → ℝ},
      ContDiff ℝ ∞ κ → ContDiff ℝ ∞ F →
      (∀ y, ContinuousOn (w y) (Icc (0 : ℝ) 1)) →
      (∀ y, w y 0 = 0) →
      (∀ y t, t ∈ Ioo (0 : ℝ) 1 →
        HasDerivAt (w y) (κ (y, t) * w y t + F (y, t)) t) →
      ∀ (x : Q) {W M ρ Λ : ℝ} (D : ℕ), 0 ≤ W → 1 ≤ M → 1 ≤ ρ →
      (∀ t ∈ Icc (0 : ℝ) 1, |∫ r in (0 : ℝ)..t, κ (x, r)| ≤ Λ) →
      (∀ j, 1 ≤ j → j ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : Q => κ (y, t)) x‖ ≤ M * ρ ^ j) →
      (∀ j, j ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : Q => F (y, t)) x‖ ≤
          C₀ * W * M ^ (n + 1) * ρ ^ (D * (n + 1) + j)) →
      ∀ k, k ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ k (fun y : Q => w y t) x‖ ≤
          C * Real.exp (2 * Λ) * W * M ^ ((n + 1) * (2 * K + 1)) *
            ρ ^ (D * (n + 1) + k) := by
  obtain ⟨C₁, hC₁, hlinear⟩ :=
    n04NegativeGeometry_linearVariation_weighted_prefix (Q := Q) K
  refine ⟨C₁ * C₀ ^ (2 * K + 1),
    one_le_mul_of_one_le_of_one_le hC₁ (one_le_pow₀ hC₀), ?_⟩
  intro κ F w hκ hF hw hzero hderiv x W M ρ Λ D hW hM hρ hamp hκj hforcing
  let M₁ : ℝ := C₀ * M ^ (n + 1)
  let W₁ : ℝ := W * ρ ^ (D * (n + 1))
  have hM₁ : 1 ≤ M₁ := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hM)
  have hW₁ : 0 ≤ W₁ := mul_nonneg hW (pow_nonneg (zero_le_one.trans hρ) _)
  have hMM₁ : M ≤ M₁ := by
    have hp : M ≤ M ^ (n + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (Nat.succ_le_succ (Nat.zero_le n))
    exact hp.trans (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hM) _) hC₀)
  have hκ₁ (j : ℕ) (hj : 1 ≤ j) (hjK : j ≤ K)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ j (fun y : Q => κ (y, t)) x‖ ≤ M₁ * ρ ^ j :=
    (hκj j hj hjK t ht).trans
      (mul_le_mul_of_nonneg_right hMM₁ (pow_nonneg (zero_le_one.trans hρ) _))
  have hF₁ (j : ℕ) (hj : j ≤ K) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ j (fun y : Q => F (y, t)) x‖ ≤ W₁ * M₁ * ρ ^ j := by
    refine (hforcing j hj t ht).trans_eq ?_
    dsimp only [W₁, M₁]
    rw [pow_add]
    ring
  intro k hk t ht
  have hb := hlinear hκ hF hw hzero hderiv x hM₁ hW₁
    (zero_le_one.trans hρ) hamp hκ₁ hF₁ k hk t ht
  refine hb.trans_eq ?_
  dsimp only [W₁, M₁]
  rw [mul_pow, ← pow_mul, pow_add]
  ring

/-- This is the genuine state-order induction step. The forcing factors
contain only original speed derivatives and strictly lower state
variations; the current unknown is not among the bounded factors.
The integer D is a state-order loss and does not depend on the spatial
order K. All numerical constants precede the actual field and flow. -/
theorem n04NegativeChart_actualVariation_weighted_step (n K : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {G Θ : E × PolarPoint → ℝ},
      ∀ (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
        (hΘ : ContDiff ℝ ∞ Θ),
      (∀ q α, Θ (q, (0, α)) = α) →
      (∀ q t α, HasDerivAt (fun r => Θ (q, (r, α)))
        (G (q, (t, Θ (q, (t, α))))) t) →
      ∀ (γ : Q → E) (α : Q → ℝ), ContDiff ℝ ∞ γ → ContDiff ℝ ∞ α →
      ∀ (v : Fin n → E) (x : Q) {W M ρ Λ : ℝ} (D : ℕ),
      0 ≤ W → 1 ≤ M → 1 ≤ ρ →
      (∀ t ∈ Icc (0 : ℝ) 1,
        |∫ r in (0 : ℝ)..t, flowVariationCoefficient G Θ (γ x) (r, α x)| ≤ Λ) →
      (∀ j, 1 ≤ j → j ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j
          (fun y : Q => flowVariationCoefficient G Θ (γ y) (t, α y)) x‖ ≤ M * ρ ^ j) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ d : FlowForcingChoice n,
        ∃ i₀ : Fin (d.1.length + 1),
        (∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (fun y : Q =>
          canonicalFlowForcingFactors J hΘ (γ y) v t d i₀ (α y)) x‖ ≤
            W * M * ρ ^ (D + j)) ∧
        (∀ i, i ≠ i₀ → ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (fun y : Q =>
          canonicalFlowForcingFactors J hΘ (γ y) v t d i (α y)) x‖ ≤
            M * ρ ^ (D + j))) →
      ∀ k, k ≤ K → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ k
          (fun y : Q => flowParameterField Θ n (γ y) v (t, α y)) x‖ ≤
            C * Real.exp (2 * Λ) * W * M ^ ((n + 1) * (2 * K + 1)) *
              ρ ^ (D * (n + 1) + k) := by
  obtain ⟨C₀, hC₀, hforcing⟩ :=
    n04NegativeChart_actualForcing_weighted_prefix (E := E) (Q := Q) n K
  obtain ⟨C, hC, hlinear⟩ :=
    linearVariation_markedForcing_prefix (Q := Q) n K hC₀
  refine ⟨C, hC, ?_⟩
  intro G Θ hG J hΘ hinit hflow γ α hγ hα v x W M ρ Λ D hW hM hρ hamp hκj hmarked
  let κ : Q × ℝ → ℝ := fun z => flowVariationCoefficient G Θ (γ z.1) (z.2, α z.1)
  let F : Q × ℝ → ℝ := fun z => flowVariationForcing J hΘ n (γ z.1) v (z.2, α z.1)
  let w : Q → ℝ → ℝ := fun y t => flowParameterField Θ n (γ y) v (t, α y)
  have hmap : ContDiff ℝ ∞ (fun z : Q × ℝ => (γ z.1, (z.2, α z.1))) :=
    (hγ.comp contDiff_fst).prodMk (contDiff_snd.prodMk (hα.comp contDiff_fst))
  have hκ : ContDiff ℝ ∞ κ :=
    (n04NegativeChart_flowCoefficient_joint_contDiff hG hΘ).comp hmap
  have hF : ContDiff ℝ ∞ F :=
    (n04NegativeChart_flowForcing_joint_contDiff hG J hΘ hn v).comp hmap
  have hwjoint : ContDiff ℝ ∞ (fun z : Q × ℝ => w z.1 z.2) :=
    (n04NegativeChart_flowParameterField_joint_contDiff hΘ n v).comp hmap
  have hw (y : Q) : ContinuousOn (w y) (Icc (0 : ℝ) 1) :=
    (hwjoint.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hzero (y : Q) : w y 0 = 0 :=
    actualVariation_zero hinit hn (γ y) (α y) v
  have hderiv (y : Q) (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (w y) (κ (y, t) * w y t + F (y, t)) t :=
    actualVariation_hasDerivAt hG J hΘ hinit hflow hn (γ y) t (α y) v
  apply hlinear hκ hF hw hzero hderiv x D hW hM hρ hamp hκj
  intro j hj t ht
  exact hforcing hG J hΘ γ α hγ hα v t x D hW hM hρ (hmarked t ht) j hj

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_actualVariation_weighted_step'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_actualVariation_weighted_step
