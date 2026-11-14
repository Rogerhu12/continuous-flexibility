module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Strong translations and convolution on the actual real Lebesgue L² space

Translations are strongly continuous: the continuity assertion fixes an L²
vector. Convolution is a Bochner integral in L² for each such vector. No
operator-norm continuity of translations, or integral of an operator-valued
translation family, is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology Convolution

abbrev RealL2 : Type := Lp ℝ 2 (volume : Measure ℝ)

/-- The actual translation `u(x) ↦ u(x-t)` on Lebesgue L². -/
def realL2Translate (t : ℝ) : RealL2 →ₗᵢ[ℝ] RealL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ => x - t)
    (measurePreserving_sub_right volume t)

theorem realL2Translate_coeFn (t : ℝ) (u : RealL2) :
    (realL2Translate t u : ℝ → ℝ) =ᵐ[volume] (fun x => u (x - t)) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_sub_right volume t)

@[simp] theorem realL2Translate_norm (t : ℝ) (u : RealL2) :
    ‖realL2Translate t u‖ = ‖u‖ := (realL2Translate t).norm_map u

@[simp] theorem realL2Translate_zero (u : RealL2) : realL2Translate 0 u = u := by
  apply Lp.ext
  filter_upwards [realL2Translate_coeFn 0 u] with x hx
  simpa only [sub_zero] using hx

/-- Strong continuity, with the L² vector fixed. -/
theorem continuous_realL2Translate (u : RealL2) :
    Continuous (fun t : ℝ => realL2Translate t u) := by
  let g : C(ℝ, C(ℝ, ℝ)) :=
    (⟨fun p : ℝ × ℝ => p.2 - p.1, continuous_snd.sub continuous_fst⟩ :
      C(ℝ × ℝ, ℝ)).curry
  have hgm : ∀ t, MeasurePreserving (g t) volume volume :=
    fun t => measurePreserving_sub_right volume t
  exact (continuous_const : Continuous (fun _ : ℝ => u)).compMeasurePreservingLp
    g.continuous hgm (by norm_num)

/-- The integral is in L², separately for each input vector. -/
def realL2Convolution (κ : ℝ → ℝ) (u : RealL2) : RealL2 :=
  ∫ t : ℝ, κ t • realL2Translate t u

theorem realL2Convolution_integrable {κ : ℝ → ℝ} (hκ : Integrable κ volume)
    (u : RealL2) : Integrable (fun t : ℝ => κ t • realL2Translate t u) volume := by
  refine (hκ.norm.mul_const ‖u‖).mono'
    (hκ.aestronglyMeasurable.smul (continuous_realL2Translate u).aestronglyMeasurable) ?_
  exact Eventually.of_forall (fun t => by
    simp only [norm_smul, realL2Translate_norm]
    exact le_rfl)

theorem realL2Convolution_norm_le (κ : ℝ → ℝ) (u : RealL2) :
    ‖realL2Convolution κ u‖ ≤ (∫ t : ℝ, |κ t|) * ‖u‖ := by
  calc
    ‖realL2Convolution κ u‖ ≤ ∫ t : ℝ, ‖κ t • realL2Translate t u‖ :=
      norm_integral_le_integral_norm _
    _ = (∫ t : ℝ, |κ t|) * ‖u‖ := by
      simp only [norm_smul, realL2Translate_norm, Real.norm_eq_abs, integral_mul_const]

/-- This continuous linear map is assembled after proving integrability
and linearity vector by vector. It is not an operator-valued integral. -/
def realL2ConvolutionOperator (κ : ℝ → ℝ) (hκ : Integrable κ volume) :
    RealL2 →L[ℝ] RealL2 :=
  LinearMap.mkContinuous
    { toFun := realL2Convolution κ
      map_add' := by
        intro u v
        change (∫ t : ℝ, κ t • realL2Translate t (u + v)) = _
        simp only [map_add, smul_add]
        exact integral_add (realL2Convolution_integrable hκ u)
          (realL2Convolution_integrable hκ v)
      map_smul' := by
        intro a u
        change (∫ t : ℝ, κ t • realL2Translate t (a • u)) =
          a • ∫ t : ℝ, κ t • realL2Translate t u
        simp only [map_smul]
        simp_rw [smul_comm (κ _) a]
        exact integral_smul a _ }
    (∫ t : ℝ, |κ t|) (realL2Convolution_norm_le κ)

@[simp] theorem realL2ConvolutionOperator_apply (κ : ℝ → ℝ)
    (hκ : Integrable κ volume) (u : RealL2) :
    realL2ConvolutionOperator κ hκ u = realL2Convolution κ u := rfl

theorem realL2Convolution_pairing {κ : ℝ → ℝ} (hκ : Integrable κ volume)
    (u : RealL2) (L : RealL2 →L[ℝ] ℝ) :
    L (realL2Convolution κ u) = ∫ t : ℝ, κ t * L (realL2Translate t u) := by
  rw [realL2Convolution, ← L.integral_comp_comm (realL2Convolution_integrable hκ u)]
  simp only [map_smul, smul_eq_mul]

theorem realL2Convolution_sub_kernel {κ η : ℝ → ℝ}
    (hκ : Integrable κ volume) (hη : Integrable η volume) (u : RealL2) :
    realL2Convolution (κ - η) u = realL2Convolution κ u - realL2Convolution η u := by
  simp only [realL2Convolution, Pi.sub_apply, sub_smul]
  exact integral_sub (realL2Convolution_integrable hκ u)
    (realL2Convolution_integrable hη u)

theorem realL2Convolution_sub_norm_le {κ η : ℝ → ℝ}
    (hκ : Integrable κ volume) (hη : Integrable η volume) (u : RealL2) :
    ‖realL2Convolution κ u - realL2Convolution η u‖ ≤
      (∫ t : ℝ, |κ t - η t|) * ‖u‖ := by
  rw [← realL2Convolution_sub_kernel hκ hη u]
  exact realL2Convolution_norm_le (κ - η) u

/-- Approximation in the actual L² norm. The general convolution theorem
is applied with L² itself as its complete normed codomain. -/
theorem realL2Convolution_tendsto {ι : Type*} {l : Filter ι} {κ : ι → ℝ → ℝ}
    (hnκ : ∀ᶠ i in l, ∀ t, 0 ≤ κ i t)
    (hiκ : ∀ᶠ i in l, ∫ t : ℝ, κ i t = 1)
    (hsκ : Tendsto (fun i => Function.support (κ i)) l (𝓝 (0 : ℝ)).smallSets)
    (u : RealL2) :
    Tendsto (fun i => realL2Convolution (κ i) u) l (𝓝 u) := by
  let g : ℝ → RealL2 := fun x => realL2Translate (-x) u
  have hg : Continuous g := (continuous_realL2Translate u).comp continuous_neg
  have hcg : Tendsto (Function.uncurry (fun _ : ι => g))
      (l ×ˢ 𝓝 (0 : ℝ)) (𝓝 u) := by
    change Tendsto (g ∘ (Prod.snd : ι × ℝ → ℝ)) (l ×ˢ 𝓝 (0 : ℝ)) (𝓝 u)
    have h := (hg.tendsto 0).comp
      (tendsto_snd : Tendsto (Prod.snd : ι × ℝ → ℝ) (l ×ˢ 𝓝 0) (𝓝 0))
    simpa only [g, neg_zero, realL2Translate_zero] using h
  have h := convolution_tendsto_right (μ := (volume : Measure ℝ))
    (g := fun _ : ι => g) (k := fun _ : ι => (0 : ℝ))
    hnκ hiκ hsκ (Eventually.of_forall (fun _ => hg.aestronglyMeasurable))
    hcg tendsto_const_nhds
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub,
    g, neg_neg, realL2Convolution] using h

end ContinuousFlexibility.Radial
