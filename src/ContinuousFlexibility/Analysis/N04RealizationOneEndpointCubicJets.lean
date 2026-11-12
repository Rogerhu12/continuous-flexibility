import ContinuousFlexibility.Analysis.N04RealizationCubicRegularity
import ContinuousFlexibility.Analysis.N04RealizationDominatedParameterIntegral

/-!
# Parameter jets through one cubic Taylor division

Only the actual numerator has a parameter tower. At each parameter a
smooth flat representative supplies the scalar Taylor identity. The
representatives may be chosen independently: their role ends before
parameter differentiation. The Taylor integrand is extended by zero at
the two integration endpoints, so no endpoint parameter tower is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Interval Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {R : ℝ} {N e : E → PolarPoint → ℝ}

private theorem n04Realization_cubicTaylorWeight_bounds
    (a : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ (1 / 2 : ℝ) * (1 - t) ^ 2 * t ^ a ∧
      (1 / 2 : ℝ) * (1 - t) ^ 2 * t ^ a ≤ 1 / 2 := by
  have hsq : (1 - t) ^ 2 ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr ht.2.le) (sub_le_self _ ht.1.le)
  have hpow : t ^ a ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
  have hmul := mul_le_mul hsq hpow (pow_nonneg ht.1.le a) (by norm_num : (0 : ℝ) ≤ 1)
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (pow_nonneg ht.1.le a)
  · nlinarith

/-- All actual parameter jets of an actual cubic quotient lose exactly
three radial orders. The input majorants are continuous in the parameter
and its direction slots; the parameter set itself is unchanged. -/
theorem n04Realization_oneEndpointCubic_parameterJets
    (RN : MixedJetRegularity U (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) N)
    (hrep : ∀ x ∈ U, ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
      EqOn F (N x) (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) ∧
      ∀ θ i, i ≤ 2 → iteratedDeriv i (fun r : ℝ => F (r, θ)) 0 = 0)
    (hfactor : ∀ x ∈ U, ∀ q ∈ Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ),
      N x q = q.1 ^ 3 * e x q)
    (G : ∀ k : ℕ, ℕ → ℕ → E × (Fin k → E) → ℝ)
    (hG : ∀ k a b, Continuous (G k a b))
    (hbound : ∀ k a b q (hq : q ∈ Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)),
      ∀ x ∈ U, ∀ v : Fin k → E,
        |(RN.parameter a b q hq).D k x v| ≤ G k a b (x, v))
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ))
    (Q : SmoothDirections U (fun x => mixedDerivative a b (e x) p)) :
    ∀ k x, x ∈ U → ∀ v : Fin k → E,
      |Q.D k x v| ≤ G k (a + 3) b (x, v) / 2 := by
  classical
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  letI : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioo]⟩
  let c : ℝ → ℝ := fun t => (1 / 2 : ℝ) * (1 - t) ^ 2 * t ^ a
  let q : ℝ → PolarPoint := fun t => (t * p.1, p.2)
  have hq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      q t ∈ Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨mul_pos ht.1 hp.1.1, ?_⟩, mem_univ _⟩
    calc
      t * p.1 < 1 * p.1 := mul_lt_mul_of_pos_right ht.2 hp.1.1
      _ < R := by simpa only [one_mul] using hp.1.2
  let f : E → ℝ → ℝ := fun x t =>
    if t ∈ Ioo (0 : ℝ) 1 then c t * mixedDerivative (a + 3) b (N x) (q t) else 0
  let J : ∀ t : ℝ, SmoothDirections U (fun x => f x t) := fun t => by
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · exact (smoothDirections_postcompCLM (RN.parameter (a + 3) b (q t) (hq t ht))
        (c t • ContinuousLinearMap.id ℝ ℝ)).congr (fun x _ => by
          simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
            smul_eq_mul, f, if_pos ht])
    · simpa only [f, if_neg ht] using smoothDirections_constant Q.open_domain (0 : ℝ)
  have hJD (k : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E)
      (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      (J t).D k x v = c t * (RN.parameter (a + 3) b (q t) (hq t ht)).D k x v :=
    n04Realization_smoothDirections_D_const_mul
      (RN.parameter (a + 3) b (q t) (hq t ht)) (J t) (c t)
      (fun _ _ => by simp only [f, if_pos ht]) k hx v
  have hJzero (k : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E)
      (t : ℝ) (ht : t ∉ Ioo (0 : ℝ) 1) : (J t).D k x v = 0 := by
    simpa only [zero_mul] using n04Realization_smoothDirections_D_const_mul
      (RN.parameter (a + 3) b p hp) (J t) 0
      (fun _ _ => by simp only [f, if_neg ht, zero_mul]) k hx v
  have hJB (k : ℕ) (x : E) (hx : x ∈ U) (v : Fin k → E) (t : ℝ) :
      |(J t).D k x v| ≤ G k (a + 3) b (x, v) / 2 := by
    have hG0 : 0 ≤ G k (a + 3) b (x, v) :=
      (abs_nonneg _).trans (hbound k (a + 3) b p hp x hx v)
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · obtain ⟨hc0, hc1⟩ := n04Realization_cubicTaylorWeight_bounds a ht
      rw [hJD k x hx v t ht, abs_mul, abs_of_nonneg hc0]
      calc
        c t * |(RN.parameter (a + 3) b (q t) (hq t ht)).D k x v| ≤
            c t * G k (a + 3) b (x, v) :=
          mul_le_mul_of_nonneg_left (hbound k (a + 3) b (q t) (hq t ht) x hx v) hc0
        _ ≤ (1 / 2 : ℝ) * G k (a + 3) b (x, v) :=
          mul_le_mul_of_nonneg_right hc1 hG0
        _ = _ := by ring
    · rw [hJzero k x hx v t ht, abs_zero]
      exact div_nonneg hG0 (by norm_num)
  have hf (x : E) (hx : x ∈ U) : AEStronglyMeasurable (f x) μ := by
    have hc : Continuous c :=
      (continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).mul
        (continuous_id.pow a)
    have hcoord : Continuous q := (continuous_id.mul continuous_const).prodMk continuous_const
    have hn := (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ)
      (RN.spatial x hx) (a + 3) b).continuousOn.comp hcoord.continuousOn hq
    have hfOn : ContinuousOn (f x) (Ioo (0 : ℝ) 1) :=
      (hc.continuousOn.mul hn).congr (fun t ht => by
        simp only [f, if_pos ht, Function.comp_apply])
    exact hfOn.aestronglyMeasurable measurableSet_Ioo
  have hvalue (x : E) (hx : x ∈ U) :
      mixedDerivative a b (e x) p = ∫ t, f x t ∂μ := by
    obtain ⟨F, hF, he, hzero⟩ := hrep x hx
    obtain ⟨h0, h1, h2⟩ := radialBoundaryPartials_of_sliceJets hF 0 hzero
    have heq : ∀ r ∈ Ioo (0 : ℝ) R, ∀ θ : ℝ,
        e x (r, θ) = radialCubicQuotient F (r, θ) := by
      intro r hr θ
      apply mul_left_cancel₀ (pow_ne_zero 3 hr.1.ne')
      calc
        r ^ 3 * e x (r, θ) = N x (r, θ) :=
          (hfactor x hx (r, θ) ⟨hr, mem_univ _⟩).symm
        _ = F (r, θ) := (@he (r, θ) ⟨hr, mem_univ _⟩).symm
        _ = r ^ 3 * radialCubicQuotient F (r, θ) :=
          (cube_mul_cubicQuotient (h0 θ) r).symm
    rw [mixedDerivative_eq_of_eqOn_radialCylinder heq a b hp.1,
      mixedDerivative_radialCubicQuotient_eq_integral hF h0 h1 h2,
      ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hd := mixedDerivative_eq_of_eqOn_radialCylinder
      (p := q t) (fun r hr θ => @he (r, θ) ⟨hr, mem_univ _⟩)
      (a + 3) b (hq t ht).1
    simpa only [f, if_pos ht, c, q, mul_assoc] using
      congrArg (fun w : ℝ => (1 / 2 : ℝ) * (1 - t) ^ 2 * t ^ a * w) hd
  have hid := n04Realization_smoothDirections_integral_jets (μ := μ) J Q hvalue hf
    (fun k y => G k (a + 3) b y / 2)
    (fun k => (hG k (a + 3) b).div_const 2) hJB
  intro k x hx v
  rw [hid k x hx v]
  change |∫ t in Ioo (0 : ℝ) 1, (J t).D k x v| ≤ _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun t => (J t).D k x v)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hJB k x hx v t)
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb

end ContinuousFlexibility.Analysis
