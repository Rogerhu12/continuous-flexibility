import ContinuousFlexibility.Analysis.N07aIntervalPrimitiveLp
import Mathlib.Topology.Sequences

/-!
# Smooth approximation of the actual interval second-derivative graph

Only the two distributional derivative identities are inputs. The proof
integrates a smooth approximation of the actual second derivative twice;
the integration constants are recovered from the weak identities. Thus the
approximants converge in all three L² coordinates without an endpoint
boundary condition or a supplied smooth representative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- Constant functions in the actual interval L² quotient. -/
def n07aIntervalConstant (c : ℝ) : N07aIntervalL2 :=
  (memLp_const c).toLp (fun _ : ℝ => c)

theorem n07aIntervalConstant_ae (c : ℝ) :
    (n07aIntervalConstant c : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun _ => c) :=
  MemLp.coeFn_toLp _

/-- The primitive and one constant recover every actual weak derivative
pair in the interval quotient. -/
theorem n07a_interval_weakDerivative_eq_primitive (f g : N07aIntervalL2)
    (hfg : HasIntervalWeakDerivative 0 1 f g) :
    ∃ c : ℝ, f = n07aIntervalConstant c + n07aIntervalPrimitive g := by
  let P : ℝ → ℝ := intervalL1Primitive 0 1 g
  have hf : LocallyIntegrableOn (f : ℝ → ℝ) (Ioo (0 : ℝ) 1) :=
    IntegrableOn.locallyIntegrableOn ((Lp.memLp f).integrable (by norm_num))
  have hP : LocallyIntegrableOn P (Ioo (0 : ℝ) 1) :=
    IntegrableOn.locallyIntegrableOn
      ((n07a_intervalL1Primitive_memLp (Lp.memLp g)).integrable (by norm_num))
  have hpweak : HasIntervalWeakDerivative 0 1 P g :=
    n07a_intervalL1Primitive_weakDerivative (Lp.memLp g)
  have hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 → (∫ x, (f x - P x) * deriv φ x) = 0 := by
    intro φ hφ hc hs
    have hdφ := (contDiff_infty_iff_deriv.mp hφ).2
    have hds := tsupport_deriv_subset.trans hs
    have hi₁ := interval_integrable_mul_test hf hdφ.continuous hc.deriv hds
    have hi₂ := interval_integrable_mul_test hP hdφ.continuous hc.deriv hds
    simp_rw [sub_mul]
    rw [integral_sub hi₁ hi₂, hfg φ hφ hc hs, hpweak φ hφ hc hs, sub_self]
  obtain ⟨c, hce⟩ := interval_ae_constant_of_integral_deriv_zero zero_lt_one (hf.sub hP) hzero
  refine ⟨c, ?_⟩
  apply Lp.ext
  filter_upwards [hce, Lp.coeFn_add (n07aIntervalConstant c) (n07aIntervalPrimitive g),
    n07aIntervalConstant_ae c, n07aIntervalPrimitive_apply_ae g] with x hx ha hc hp
  simp only [Pi.add_apply] at ha
  rw [ha, hc, hp]
  change f x - P x = c at hx
  change f x = c + P x
  linarith

/-- The ordinary global primitive is used for smooth representatives. -/
def n07aSmoothPrimitive (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, f y

theorem n07aSmoothPrimitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (n07aSmoothPrimitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem n07aSmoothPrimitive_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (n07aSmoothPrimitive f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (n07aSmoothPrimitive_hasDerivAt hf.continuous x).differentiableAt, ?_⟩
  have he : deriv (n07aSmoothPrimitive f) = f :=
    funext fun x => (n07aSmoothPrimitive_hasDerivAt hf.continuous x).deriv
  rw [he]
  exact hf

theorem n07aSmoothPrimitive_eq_intervalL1Primitive (f : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    n07aSmoothPrimitive f x = intervalL1Primitive 0 1 f x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with y hy
  rw [uIoc_of_le hx.1.le] at hy
  exact (indicator_of_mem (show y ∈ Ioo (0 : ℝ) 1 from
    ⟨hy.1, hy.2.trans_lt hx.2⟩) f).symm

/-- The bounded quotient primitive has the expected ordinary integral
representative for every prescribed a.e. representative of its input. -/
theorem n07aIntervalPrimitive_ae_smoothPrimitive {f : N07aIntervalL2} {g : ℝ → ℝ}
    (hfg : (f : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g) :
    (n07aIntervalPrimitive f : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      n07aSmoothPrimitive g := by
  filter_upwards [n07aIntervalPrimitive_apply_ae f,
    ae_restrict_mem measurableSet_Ioo] with x hx hxin
  rw [hx, n07a_intervalL1Primitive_congr hfg]
  exact (n07aSmoothPrimitive_eq_intervalL1Primitive g hxin).symm

/-- A genuine smooth sequence converging in the three coordinates of the
maximal second weak derivative graph. -/
theorem n07a_intervalH2_smooth_approximation (u₀ u₁ u₂ : N07aIntervalL2)
    (h₀₁ : HasIntervalWeakDerivative 0 1 u₀ u₁)
    (h₁₂ : HasIntervalWeakDerivative 0 1 u₁ u₂) :
    ∃ f : ℕ → ℝ → ℝ, ∃ f₀ f₁ f₂ : ℕ → N07aIntervalL2,
      (∀ n, ContDiff ℝ ∞ (f n) ∧
        (f₀ n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f n ∧
        (f₁ n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] deriv (f n) ∧
        (f₂ n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] deriv (deriv (f n))) ∧
      Tendsto f₀ atTop (𝓝 u₀) ∧ Tendsto f₁ atTop (𝓝 u₁) ∧ Tendsto f₂ atTop (𝓝 u₂) := by
  obtain ⟨c₀, hc₀⟩ := n07a_interval_weakDerivative_eq_primitive u₀ u₁ h₀₁
  obtain ⟨c₁, hc₁⟩ := n07a_interval_weakDerivative_eq_primitive u₁ u₂ h₁₂
  have hdense := smoothCompactL2Submodule_dense
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) isOpen_Ioo
    (ae_restrict_mem measurableSet_Ioo)
    (fun K _ _ => measure_lt_top _ K)
  obtain ⟨q, hq, hqt⟩ := mem_closure_iff_seq_limit.mp (hdense u₂)
  choose g hg hgc hgs hqg using hq
  let d (n : ℕ) : ℝ → ℝ := fun x => c₁ + n07aSmoothPrimitive (g n) x
  let f (n : ℕ) : ℝ → ℝ := fun x => c₀ + n07aSmoothPrimitive (d n) x
  let f₁ : ℕ → N07aIntervalL2 := fun n => n07aIntervalConstant c₁ + n07aIntervalPrimitive (q n)
  let f₀ : ℕ → N07aIntervalL2 := fun n => n07aIntervalConstant c₀ + n07aIntervalPrimitive (f₁ n)
  have hd (n : ℕ) : ContDiff ℝ ∞ (d n) :=
    contDiff_const.add (n07aSmoothPrimitive_contDiff (hg n))
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    contDiff_const.add (n07aSmoothPrimitive_contDiff (hd n))
  have hfder (n : ℕ) : deriv (f n) = d n :=
    funext fun x => ((n07aSmoothPrimitive_hasDerivAt (hd n).continuous x).const_add c₀).deriv
  have hdder (n : ℕ) : deriv (d n) = g n :=
    funext fun x => ((n07aSmoothPrimitive_hasDerivAt (hg n).continuous x).const_add c₁).deriv
  have hf₁ (n : ℕ) : (f₁ n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] d n := by
    filter_upwards [Lp.coeFn_add (n07aIntervalConstant c₁) (n07aIntervalPrimitive (q n)),
      n07aIntervalConstant_ae c₁, n07aIntervalPrimitive_ae_smoothPrimitive (hqg n)]
      with x hx hc hp
    simp only [Pi.add_apply] at hx
    change f₁ n x = c₁ + n07aSmoothPrimitive (g n) x
    exact hx.trans (congrArg₂ (· + ·) hc hp)
  have hf₀ (n : ℕ) : (f₀ n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f n := by
    filter_upwards [Lp.coeFn_add (n07aIntervalConstant c₀) (n07aIntervalPrimitive (f₁ n)),
      n07aIntervalConstant_ae c₀, n07aIntervalPrimitive_ae_smoothPrimitive (hf₁ n)]
      with x hx hc hp
    simp only [Pi.add_apply] at hx
    change f₀ n x = c₀ + n07aSmoothPrimitive (d n) x
    exact hx.trans (congrArg₂ (· + ·) hc hp)
  have ht₁ : Tendsto f₁ atTop (𝓝 u₁) := by
    rw [hc₁]
    exact tendsto_const_nhds.add (n07aIntervalPrimitive.continuous.tendsto _ |>.comp hqt)
  have ht₀ : Tendsto f₀ atTop (𝓝 u₀) := by
    rw [hc₀]
    exact tendsto_const_nhds.add (n07aIntervalPrimitive.continuous.tendsto _ |>.comp ht₁)
  refine ⟨f, f₀, f₁, q, ?_, ht₀, ht₁, hqt⟩
  intro n
  refine ⟨hf n, hf₀ n, ?_, ?_⟩
  · rw [hfder]
    exact hf₁ n
  · rw [hfder, hdder]
    exact hqg n

end ContinuousFlexibility.Analysis
