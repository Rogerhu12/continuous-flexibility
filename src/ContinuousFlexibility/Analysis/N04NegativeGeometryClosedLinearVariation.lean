module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryLinearVariationBounds
public import ContinuousFlexibility.Analysis.N04FlowJetEquations

/-!
# Linear variation estimates on the original closed time interval

A compact smooth time change converts the genuine within-derivative
equation into an ordinary ODE on the entire real line. Only the
coefficients after this time change need be jointly smooth. This is the
regularity already proved for the actual N04 flow on a closed interval.

The time change and its first derivative bound are fixed before every
spatial order. The forcing weight is retained exactly once, and the
result applies at every original time, including both endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

def n04NegativeGeometry_timeChangedCoefficient (f : Q × ℝ → ℝ)
    (z : Q × ℝ) : ℝ :=
  deriv (compactScalarFlowTime 0 1) z.2 *
    f (z.1, compactScalarFlowTime 0 1 z.2)

private theorem timeChangedCoefficient_contDiff
    {f : Q × ℝ → ℝ}
    (hf : ContDiff ℝ ∞
      (fun z : Q × ℝ => f (z.1, compactScalarFlowTime 0 1 z.2))) :
    ContDiff ℝ ∞ (n04NegativeGeometry_timeChangedCoefficient f) := by
  have hτ' : ContDiff ℝ ∞ (deriv (compactScalarFlowTime 0 1)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_compactScalarFlowTime 0 1)).2
  exact (hτ'.comp contDiff_snd).mul hf

private theorem timeChangedCoefficient_jet_le
    {f : Q × ℝ → ℝ}
    (hf : ContDiff ℝ ∞
      (fun z : Q × ℝ => f (z.1, compactScalarFlowTime 0 1 z.2)))
    (x : Q) (k : ℕ) (t : ℝ) {D M : ℝ} (hD : 0 ≤ D)
    (hτ : |deriv (compactScalarFlowTime 0 1) t| ≤ D)
    (hb : ‖iteratedFDeriv ℝ k
      (fun y : Q => f (y, compactScalarFlowTime 0 1 t)) x‖ ≤ M) :
    ‖iteratedFDeriv ℝ k
      (fun y : Q => n04NegativeGeometry_timeChangedCoefficient f (y, t)) x‖ ≤ D * M := by
  have hs : ContDiff ℝ ∞
      (fun y : Q => f (y, compactScalarFlowTime 0 1 t)) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  have he : (fun y : Q => n04NegativeGeometry_timeChangedCoefficient f (y, t)) =
      fun y : Q => deriv (compactScalarFlowTime 0 1) t •
        f (y, compactScalarFlowTime 0 1 t) := rfl
  rw [he, iteratedFDeriv_const_smul_apply' (hs.contDiffAt.of_le (by simp)),
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul hτ hb (norm_nonneg _) hD

variable [FiniteDimensional ℝ Q]

/-- A universal time-change cost is chosen before the spatial order.
The theorem uses the original closed-interval ODE and actual spatial
derivatives, with no assumed equation for the solution's derivatives. -/
theorem n04NegativeGeometry_closedLinearVariation_weighted_prefix :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ {κ F : Q × ℝ → ℝ} {w : Q → ℝ → ℝ},
        ContDiff ℝ ∞
          (fun z : Q × ℝ => κ (z.1, compactScalarFlowTime 0 1 z.2)) →
        ContDiff ℝ ∞
          (fun z : Q × ℝ => F (z.1, compactScalarFlowTime 0 1 z.2)) →
        (∀ y, ContinuousOn (w y) (Icc (0 : ℝ) 1)) →
        (∀ y, w y 0 = 0) →
        (∀ y t, t ∈ Icc (0 : ℝ) 1 →
          HasDerivWithinAt (w y) (κ (y, t) * w y t + F (y, t))
            (Icc (0 : ℝ) 1) t) →
        ∀ (x : Q) {M W ρ Λ : ℝ}, 1 ≤ M → 0 ≤ W → 0 ≤ ρ → 0 ≤ Λ →
        (∀ t ∈ Icc (0 : ℝ) 1, |κ (x, t)| ≤ Λ) →
        (∀ j, 1 ≤ j → j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
          ‖iteratedFDeriv ℝ j (fun y : Q => κ (y, t)) x‖ ≤ M * ρ ^ j) →
        (∀ j, j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
          ‖iteratedFDeriv ℝ j (fun y : Q => F (y, t)) x‖ ≤ W * M * ρ ^ j) →
        ∀ k, k ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
          ‖iteratedFDeriv ℝ k (fun y : Q => w y t) x‖ ≤
            C * Real.exp (D * Λ) * W * M ^ (2 * N + 1) * ρ ^ k := by
  have hτ' : Continuous (deriv (compactScalarFlowTime 0 1)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_compactScalarFlowTime 0 1)).2.continuous
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hτ'.continuousOn
  let D : ℝ := max 1 B
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hτb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |deriv (compactScalarFlowTime 0 1) t| ≤ D := by
    have hb : |deriv (compactScalarFlowTime 0 1) t| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB t ht
    exact hb.trans (le_max_right _ _)
  refine ⟨2 * D, (by linarith only [hD]), fun N => ?_⟩
  obtain ⟨C, hC, hbound⟩ := n04NegativeGeometry_linearVariation_weighted_prefix (Q := Q) N
  refine ⟨C * D ^ (2 * N + 1),
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD), ?_⟩
  intro κ F w hκ hF hw hzero hderiv x M W ρ Λ hM hW hρ hΛ hκ0 hκj hFj
  let κ₁ : Q × ℝ → ℝ := n04NegativeGeometry_timeChangedCoefficient κ
  let F₁ : Q × ℝ → ℝ := n04NegativeGeometry_timeChangedCoefficient F
  let w₁ : Q → ℝ → ℝ := fun y t => w y (compactScalarFlowTime 0 1 t)
  have hκ₁ : ContDiff ℝ ∞ κ₁ := timeChangedCoefficient_contDiff hκ
  have hF₁ : ContDiff ℝ ∞ F₁ := timeChangedCoefficient_contDiff hF
  have hw₁ (y : Q) : ContinuousOn (w₁ y) (Icc (0 : ℝ) 1) :=
    ((hw y).comp_continuous (contDiff_compactScalarFlowTime 0 1).continuous
      (fun t => n04Flow_compactTime_mem t)).continuousOn
  have hzero₁ (y : Q) : w₁ y 0 = 0 := by
    simpa only [w₁, compactScalarFlowTime_zero] using hzero y
  have hderiv₁ (y : Q) (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (w₁ y) (κ₁ (y, t) * w₁ y t + F₁ (y, t)) t := by
    have hf : ∀ y t, t ∈ uIcc (0 : ℝ) 1 →
        HasDerivWithinAt (w y) (κ (y, t) * w y t + F (y, t))
          (uIcc (0 : ℝ) 1) t := by
      intro y t ht
      simpa only [uIcc_of_le zero_le_one] using
        hderiv y t (by simpa only [uIcc_of_le zero_le_one] using ht)
    have hd := scalarFlowTimeChange_hasDerivAt
      (Θ := fun z : Q × ℝ => w z.1 z.2)
      (F := fun z : Q × (ℝ × ℝ) => κ (z.1, z.2.1) * z.2.2 + F (z.1, z.2.1))
      (a := (0 : ℝ)) (b := 1) hf y t
    apply hd.congr_deriv
    simp only [scalarFlowTimeChange, scalarFieldTimeChange, w₁, κ₁, F₁,
      n04NegativeGeometry_timeChangedCoefficient]
    ring
  have hκ₁0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |κ₁ (x, t)| ≤ D * Λ := by
    have hb := timeChangedCoefficient_jet_le hκ x 0 t hD0 (hτb t ht)
      (by simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
        hκ0 (compactScalarFlowTime 0 1 t) (n04Flow_compactTime_mem t))
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, κ₁] using hb
  have hamp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |∫ r in (0 : ℝ)..t, κ₁ (x, r)| ≤ D * Λ := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (C := D * Λ) (f := fun r => κ₁ (x, r))
      (fun r hr => by
        have hr' : r ∈ Icc (0 : ℝ) t := by
          simpa only [uIcc_of_le ht.1] using uIoc_subset_uIcc hr
        simpa only [Real.norm_eq_abs] using hκ₁0 r ⟨hr'.1, hr'.2.trans ht.2⟩)
    have hi' : |∫ r in (0 : ℝ)..t, κ₁ (x, r)| ≤ (D * Λ) * t := by
      simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using hi
    exact hi'.trans (mul_le_of_le_one_right (mul_nonneg hD0 hΛ) ht.2)
  have hκ₁j (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ j (fun y : Q => κ₁ (y, t)) x‖ ≤ (D * M) * ρ ^ j := by
    exact (timeChangedCoefficient_jet_le hκ x j t hD0 (hτb t ht)
      (hκj j hj hjN (compactScalarFlowTime 0 1 t) (n04Flow_compactTime_mem t))).trans_eq
      (mul_assoc _ _ _).symm
  have hF₁j (j : ℕ) (hj : j ≤ N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ j (fun y : Q => F₁ (y, t)) x‖ ≤ W * (D * M) * ρ ^ j := by
    refine (timeChangedCoefficient_jet_le hF x j t hD0 (hτb t ht)
      (hFj j hj (compactScalarFlowTime 0 1 t) (n04Flow_compactTime_mem t))).trans_eq ?_
    ring
  intro k hk t ht
  obtain ⟨s, hs, hst⟩ := n04Flow_compactTime_surjOn ht
  have hb := hbound hκ₁ hF₁ hw₁ hzero₁ hderiv₁ x
    (one_le_mul_of_one_le_of_one_le hD hM) hW hρ hamp hκ₁j hF₁j k hk s hs
  have he : (fun y : Q => w₁ y s) = fun y : Q => w y t := by
    funext y
    exact congrArg (w y) hst
  rw [he] at hb
  refine hb.trans_eq ?_
  rw [show 2 * (D * Λ) = (2 * D) * Λ by ring, mul_pow]
  ring

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_closedLinearVariation_weighted_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_closedLinearVariation_weighted_prefix
