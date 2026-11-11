import ContinuousFlexibility.Analysis.CylinderMixedJets
import ContinuousFlexibility.Analysis.SmoothScaledIntegral

/-!
# Mixed derivatives of a radially scaled cylinder integral

The angular derivative passes through the fixed compact integral without
an extra factor.  Each radial derivative inserts one factor of the
integration variable.  The derivative formulas below concern the actual
iterated derivatives, with local domination obtained from continuity on
a compact parameter rectangle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology Interval

/-- Angular jets of the integral along a radially scaled segment. -/
def angularScaledIntervalIntegralJet (w : ℝ → ℝ) (g : PolarPoint → ℝ)
    (b : ℕ) (r θ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, w t * mixedDerivative 0 b g (t * r, θ)

private theorem contDiff_angularMixedJet {g : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (b : ℕ) : ContDiff ℝ ∞ (mixedDerivative 0 b g) :=
  contDiffOn_univ.mp (contDiffOn_mixedDerivative isOpen_univ hg.contDiffOn 0 b)

private theorem hasDerivAt_angularMixedJet {g : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g) (b : ℕ) (r θ : ℝ) :
    HasDerivAt (fun x : ℝ => mixedDerivative 0 b g (r, x))
      (mixedDerivative 0 (b + 1) g (r, θ)) θ := by
  have hs : ContDiff ℝ ∞ (fun x : ℝ => g (r, x)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  have hd := (hs.differentiable_iteratedDeriv b
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl b) θ).hasDerivAt
  simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_succ] using hd

/-- Angular differentiation under the integral.  The radius is fixed and
no uniform bound over all radii is assumed. -/
theorem hasDerivAt_angularScaledIntervalIntegralJet
    {w : ℝ → ℝ} {g : PolarPoint → ℝ}
    (hw : Continuous w) (hg : ContDiff ℝ ∞ g) (b : ℕ) (r θ : ℝ) :
    HasDerivAt (angularScaledIntervalIntegralJet w g b r)
      (angularScaledIntervalIntegralJet w g (b + 1) r θ) θ := by
  have hjet (n : ℕ) : Continuous (mixedDerivative 0 n g) :=
    (contDiff_angularMixedJet hg n).continuous
  have hsection (n : ℕ) (x : ℝ) :
      Continuous (fun t : ℝ => w t * mixedDerivative 0 n g (t * r, x)) :=
    hw.mul ((hjet n).comp
      ((continuous_id.mul continuous_const).prodMk continuous_const))
  have hcompact : IsCompact
      (Icc (θ - 1) (θ + 1) ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (fun p : ℝ × ℝ =>
      w p.2 * mixedDerivative 0 (b + 1) g (p.2 * r, p.1)) :=
    (hw.comp continuous_snd).mul ((hjet (b + 1)).comp
      ((continuous_snd.mul continuous_const).prodMk continuous_fst))
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  have hs : Ioo (θ - 1) (θ + 1) ∈ 𝓝 θ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t : ℝ => w t * mixedDerivative 0 b g (t * r, x))
    (F' := fun x t : ℝ => w t * mixedDerivative 0 (b + 1) g (t * r, x))
    (μ := volume) (a := 0) (b := 1) (s := Ioo (θ - 1) (θ + 1))
    (bound := fun _ : ℝ => B) hs
    (Filter.Eventually.of_forall (fun x => (hsection b x).aestronglyMeasurable))
    ((hsection b θ).intervalIntegrable 0 1)
    ((hsection (b + 1) θ).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t ht x hx => by
      have ht' : t ∈ Icc (0 : ℝ) 1 :=
        Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)
      exact hB (x, t) ⟨⟨hx.1.le, hx.2.le⟩, ht'⟩))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ x _ =>
      (hasDerivAt_angularMixedJet hg b (t * r) x).const_mul (w t)))
  exact h.2

/-- The angular integral jets are genuine iterated angular derivatives. -/
theorem iteratedDeriv_angular_scaled_intervalIntegral
    {w : ℝ → ℝ} {g : PolarPoint → ℝ}
    (hw : Continuous w) (hg : ContDiff ℝ ∞ g) (b : ℕ) (r : ℝ) :
    iteratedDeriv b (fun θ : ℝ => ∫ t in (0 : ℝ)..1, w t * g (t * r, θ)) =
      fun θ => ∫ t in (0 : ℝ)..1, w t * mixedDerivative 0 b g (t * r, θ) := by
  induction b with
  | zero => simp only [iteratedDeriv_zero, mixedDerivative]
  | succ b ih =>
      rw [iteratedDeriv_succ, ih]
      funext θ
      exact (hasDerivAt_angularScaledIntervalIntegralJet hw hg b r θ).deriv

/-- Each radial derivative inserts a factor of the integration variable;
angular derivatives require exactly the same angular order of the input.
The identity uses the actual mixed derivatives on the product cylinder. -/
theorem mixedDerivative_scaled_cylinderIntegral
    {w : ℝ → ℝ} {g : PolarPoint → ℝ}
    (hw : Continuous w) (hg : ContDiff ℝ ∞ g) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b
        (fun q : PolarPoint => ∫ t in (0 : ℝ)..1, w t * g (t * q.1, q.2)) p =
      ∫ t in (0 : ℝ)..1, w t * t ^ a * mixedDerivative a b g (t * p.1, p.2) := by
  have hinner :
      (fun r : ℝ => iteratedDeriv b
        (fun θ : ℝ => ∫ t in (0 : ℝ)..1, w t * g (t * r, θ)) p.2) =
      fun r : ℝ => ∫ t in (0 : ℝ)..1, w t * mixedDerivative 0 b g (t * r, p.2) :=
    funext (fun r => congrFun (iteratedDeriv_angular_scaled_intervalIntegral hw hg b r) p.2)
  have hsmooth : ContDiff ℝ ∞ (fun r : ℝ => mixedDerivative 0 b g (r, p.2)) :=
    (contDiff_angularMixedJet hg b).comp (contDiff_id.prodMk contDiff_const)
  have hrad := congrFun (iteratedDeriv_scaled_intervalIntegral hw hsmooth a) p.1
  change iteratedDeriv a
      (fun r : ℝ => iteratedDeriv b
        (fun θ : ℝ => ∫ t in (0 : ℝ)..1, w t * g (t * r, θ)) p.2) p.1 = _
  rw [hinner]
  simpa only [mixedDerivative, iteratedDeriv_zero] using hrad

end ContinuousFlexibility.Analysis
