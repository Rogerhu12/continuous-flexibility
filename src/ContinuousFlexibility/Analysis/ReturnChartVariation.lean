import ContinuousFlexibility.Analysis.ReturnChartDifferentiation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Differentiating the return residual in a chart direction

The transported chart varies as `F + s V`.  Its odd part supplies the
right chart.  We differentiate the actual local inverse identity; only
continuity of the inverse curve at the parameter value is assumed.
The derivative of the inverse, and then the derivative of the residual,
are consequences.  The final integral Taylor identity gives precisely
the frozen-residual coefficient occurring in `circleChartError`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem evenPart_affine (F V : ℝ → ℝ) (s θ : ℝ) :
    evenPart (fun x => F x + s * V x) θ = evenPart F θ + s * evenPart V θ := by
  unfold evenPart
  ring

theorem oddPart_affine (F V : ℝ → ℝ) (s θ : ℝ) :
    oddPart (fun x => F x + s * V x) θ = oddPart F θ + s * oddPart V θ := by
  unfold oddPart
  ring

theorem evenPart_continuous (F : ℝ → ℝ) (hF : Continuous F) : Continuous (evenPart F) := by
  exact ((hF.add (hF.comp continuous_neg)).div_const 2).congr
    (fun t => by simp only [evenPart, Pi.add_apply, Function.comp_def])

theorem oddPart_continuous (F : ℝ → ℝ) (hF : Continuous F) : Continuous (oddPart F) := by
  exact ((hF.sub (hF.comp continuous_neg)).div_const 2).congr
    (fun t => by simp only [oddPart, Pi.sub_apply, Function.comp_def])

theorem evenPart_hasDerivAt {F : ℝ → ℝ} {θ dpos dneg : ℝ}
    (hpos : HasDerivAt F dpos θ) (hneg : HasDerivAt F dneg (-θ)) :
    HasDerivAt (evenPart F) ((dpos - dneg) / 2) θ := by
  have hreflect : HasDerivAt (fun t => F (-t)) (-dneg) θ := by
    simpa only [mul_neg_one, Function.comp_def] using hneg.comp θ (hasDerivAt_neg (x := θ))
  have h := ((hpos.add hreflect).div_const 2).congr_deriv
    (g' := (dpos - dneg) / 2) (by ring)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by simp only [evenPart, Pi.add_apply])

/-- At zero the factor `s` removes any need to differentiate its continuous
coefficient.  This avoids assuming differentiability of the inverse curve
when deriving its first variation. -/
theorem hasDerivAt_parameter_mul_of_continuousAt {a : ℝ → ℝ}
    (ha : ContinuousAt a 0) : HasDerivAt (fun s : ℝ => s * a s) (a 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hlim : Tendsto a (𝓝[≠] (0 : ℝ)) (𝓝 (a 0)) :=
    ha.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
  simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

/-- Continuity of the actual inverse curve follows from positivity of the
nearby chart derivatives.  The proof uses two fixed points bracketing the
base inverse value and the pointwise affine dependence of their images. -/
theorem returnChart_inverse_affine_continuous (F V : ℝ → ℝ)
    (g : ℝ → ℝ → ℝ) (θ : ℝ)
    (hpositive : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x,
      0 < deriv (oddPart (fun y => F y + s * V y)) x)
    (hright : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x,
      oddPart (fun y => F y + s * V y) (g s x) = x) :
    ContinuousAt (fun s => g s θ) 0 := by
  have hmono : ∀ᶠ s in 𝓝 (0 : ℝ),
      StrictMono (oddPart (fun y => F y + s * V y)) :=
    hpositive.mono fun _ hs => strictMono_of_deriv_pos hs
  have hmono0 : StrictMono (oddPart F) := by
    simpa only [zero_mul, add_zero] using hmono.self_of_nhds
  have hright0 : oddPart F (g 0 θ) = θ := by
    simpa only [zero_mul, add_zero] using hright.self_of_nhds θ
  have hc (x : ℝ) : ContinuousAt (fun s => oddPart (fun y => F y + s * V y) x) 0 := by
    simp_rw [oddPart_affine]
    fun_prop
  apply tendsto_order.2
  constructor
  · intro l hl
    have hlt0 : oddPart F l < θ := by
      rw [← hright0]
      exact hmono0 hl
    have hlt : ∀ᶠ s in 𝓝 (0 : ℝ), oddPart (fun y => F y + s * V y) l < θ :=
      (hc l).eventually_lt continuousAt_const (by
        simpa only [zero_mul, add_zero] using hlt0)
    filter_upwards [hmono, hright, hlt] with s hs hinv hlt
    apply hs.lt_iff_lt.mp
    rw [hinv θ]
    exact hlt
  · intro u hu
    have hgt0 : θ < oddPart F u := by
      rw [← hright0]
      exact hmono0 hu
    have hgt : ∀ᶠ s in 𝓝 (0 : ℝ), θ < oddPart (fun y => F y + s * V y) u :=
      continuousAt_const.eventually_lt (hc u) (by
        simpa only [zero_mul, add_zero] using hgt0)
    filter_upwards [hmono, hright, hgt] with s hs hinv hgt
    apply hs.lt_iff_lt.mp
    rw [hinv θ]
    exact hgt

/-- Differentiate the genuine local inverse identity for the affine chart
family.  The identity is needed only near zero, where the perturbed charts
are defined as diffeomorphisms. -/
theorem returnChart_inverse_affine_variation (F V : ℝ → ℝ)
    (g : ℝ → ℝ → ℝ) (θ : ℝ)
    (hV : Continuous V)
    (hpos : 0 < deriv (oddPart F) (g 0 θ))
    (hinverse : ∀ᶠ s in 𝓝 (0 : ℝ),
      oddPart (fun x => F x + s * V x) (g s θ) = θ)
    (hg : ContinuousAt (fun s => g s θ) 0) :
    HasDerivAt (fun s => g s θ)
      (-oddPart V (g 0 θ) / deriv (oddPart F) (g 0 θ)) 0 := by
  have hmul := hasDerivAt_parameter_mul_of_continuousAt
    ((oddPart_continuous V hV).continuousAt.comp hg)
  have htarget : HasDerivAt (fun s : ℝ => θ - s * oddPart V (g s θ))
      (-oddPart V (g 0 θ)) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) θ).sub hmul).congr_deriv
      (g' := -oddPart V (g 0 θ)) (by simp only [zero_sub, Function.comp_def])
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      simp only [Pi.sub_apply, Function.comp_def])
  have hchart : HasDerivAt (oddPart F) (deriv (oddPart F) (g 0 θ)) (g 0 θ) :=
    (differentiableAt_of_deriv_ne_zero hpos.ne').hasDerivAt
  have hcomp : (oddPart F ∘ fun s => g s θ) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => θ - s * oddPart V (g s θ)) := by
    filter_upwards [hinverse] with s hs
    rw [oddPart_affine] at hs
    dsimp only [Function.comp_apply]
    linarith only [hs]
  exact HasDerivAt.of_comp_left hg hchart htarget hpos.ne' hcomp

/-- Chain differentiation of the residual in the affine chart family.
The parameter derivative of the inverse and the spatial derivative of the
base residual are both derived from their actual inverse identities. -/
theorem hasDerivAt_returnResidual_affine_chart (F V : ℝ → ℝ)
    (g : ℝ → ℝ → ℝ) (θ : ℝ)
    (hF : Differentiable ℝ F) (hV : Continuous V)
    (hpos : ∀ x, 0 < deriv (oddPart F) x)
    (hleft : ∀ x, g 0 (oddPart F x) = x)
    (hright : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x,
      oddPart (fun y => F y + s * V y) (g s x) = x)
    (hg : ContinuousAt (fun s => g s θ) 0) :
    HasDerivAt (fun s => evenPart (fun x => F x + s * V x) (g s θ))
      (evenPart V (g 0 θ) -
        deriv (fun x => evenPart F (g 0 x)) θ * oddPart V (g 0 θ)) 0 := by
  have hright0 (x : ℝ) : oddPart F (g 0 x) = x := by
    simpa only [zero_mul, add_zero] using hright.self_of_nhds x
  have hginv := returnChart_inverse_affine_variation F V g θ hV (hpos _)
    (hright.mono fun _ hs => hs θ) hg
  have hE := evenPart_hasDerivAt (hF (g 0 θ)).hasDerivAt (hF (-g 0 θ)).hasDerivAt
  have hmul := hasDerivAt_parameter_mul_of_continuousAt
    ((evenPart_continuous V hV).continuousAt.comp hg)
  have hparameter : HasDerivAt
      (fun s => evenPart F (g s θ) + s * evenPart V (g s θ))
      (((deriv F (g 0 θ) - deriv F (-g 0 θ)) / 2) *
          (-oddPart V (g 0 θ) / deriv (oddPart F) (g 0 θ)) +
        evenPart V (g 0 θ)) 0 := by
    exact ((hE.comp 0 hginv).add hmul).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp only [Function.comp_def, Pi.add_apply])
  have hparameter' : HasDerivAt
      (fun s => evenPart (fun x => F x + s * V x) (g s θ))
      (((deriv F (g 0 θ) - deriv F (-g 0 θ)) / 2) *
          (-oddPart V (g 0 θ) / deriv (oddPart F) (g 0 θ)) +
        evenPart V (g 0 θ)) 0 :=
    hparameter.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => evenPart_affine F V s (g s θ))
  have hbaseInverse := returnChart_hasDerivAt_inverse (oddPart F) (g 0) hpos hleft hright0 θ
  have hbase : HasDerivAt (fun x => evenPart F (g 0 x))
      (((deriv F (g 0 θ) - deriv F (-g 0 θ)) / 2) *
        (deriv (oddPart F) (g 0 θ))⁻¹) θ := by
    simpa only [Function.comp_def] using hE.comp θ hbaseInverse
  apply hparameter'.congr_deriv
  rw [hbase.deriv]
  simp only [div_eq_mul_inv]
  ring

/-- The fully geometric version: positivity of the actual nearby charts
supplies the inverse continuity used in the chain differentiation. -/
theorem hasDerivAt_returnResidual_affine_chart_of_positive_family (F V : ℝ → ℝ)
    (g : ℝ → ℝ → ℝ) (θ : ℝ)
    (hF : Differentiable ℝ F) (hV : Continuous V)
    (hleft : ∀ x, g 0 (oddPart F x) = x)
    (hpositive : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x,
      0 < deriv (oddPart (fun y => F y + s * V y)) x)
    (hright : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x,
      oddPart (fun y => F y + s * V y) (g s x) = x) :
    HasDerivAt (fun s => evenPart (fun x => F x + s * V x) (g s θ))
      (evenPart V (g 0 θ) -
        deriv (fun x => evenPart F (g 0 x)) θ * oddPart V (g 0 θ)) 0 := by
  have hpos : ∀ x, 0 < deriv (oddPart F) x := by
    simpa only [zero_mul, add_zero] using hpositive.self_of_nhds
  exact hasDerivAt_returnResidual_affine_chart F V g θ hF hV hpos hleft hright
    (returnChart_inverse_affine_continuous F V g θ hpositive hright)

/-- A chart direction has the transported form `V = ψ ∘ (F + T)`.
Oddness of the inverse carries the even/odd projections into the fixed
right-chart coordinates. -/
theorem hasDerivAt_returnResidual_chart_variation (F ψ : ℝ → ℝ) (T : ℝ)
    (g : ℝ → ℝ → ℝ) (θ : ℝ)
    (hF : Differentiable ℝ F) (hψ : Continuous ψ)
    (hpos : ∀ x, 0 < deriv (oddPart F) x)
    (hleft : ∀ x, g 0 (oddPart F x) = x)
    (hright : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x,
      oddPart (fun y => F y + s * ψ (F y + T)) (g s x) = x)
    (hg : ContinuousAt (fun s => g s θ) 0) :
    HasDerivAt (fun s => evenPart (fun x => F x + s * ψ (F x + T)) (g s θ))
      (evenPart (fun t => ψ (t + T + evenPart F (g 0 t))) θ -
        deriv (fun x => evenPart F (g 0 x)) θ *
          oddPart (fun t => ψ (t + T + evenPart F (g 0 t))) θ) 0 := by
  have hV : Continuous (fun x => ψ (F x + T)) := by
    simpa only [Function.comp_def] using hψ.comp (hF.continuous.add_const T)
  have h := hasDerivAt_returnResidual_affine_chart F (fun x => ψ (F x + T))
    g θ hF hV hpos hleft hright hg
  have hright0 (x : ℝ) : oddPart F (g 0 x) = x := by
    simpa only [zero_mul, add_zero] using hright.self_of_nhds x
  have hoddInverse : ∀ x, g 0 (-x) = -g 0 x :=
    returnChart_inverse_odd (oddPart F) (g 0) (oddPart_neg_argument F) hleft hright0
  have hcomp : (fun x => ψ (F x + T)) ∘ g 0 =
      (fun t => ψ (t + T + evenPart F (g 0 t))) := by
    funext t
    have hdecomp := oddPart_add_evenPart F (g 0 t)
    rw [hright0] at hdecomp
    apply congrArg ψ
    linarith only [hdecomp]
  have heven := congrFun
    (evenPart_comp_odd (fun x => ψ (F x + T)) (g 0) hoddInverse) θ
  have hodd := congrFun
    (oddPart_comp_odd (fun x => ψ (F x + T)) (g 0) hoddInverse) θ
  rw [hcomp] at heven hodd
  simp only [Function.comp_apply] at heven hodd
  rw [← heven, ← hodd] at h
  exact h

/-- Taylor's formula along the straight segment, with its actual integral
remainder.  It is valid also for a negative or zero displacement. -/
theorem returnChart_taylor_integral (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (x e : ℝ) :
    ψ (x + e) = ψ x + e * ∫ t in (0 : ℝ)..1, deriv ψ (x + t * e) := by
  have hdiff := hψ.differentiable (by simp)
  have hderiv (t : ℝ) : HasDerivAt (fun s : ℝ => ψ (x + s * e))
      (e * deriv ψ (x + t * e)) t := by
    simpa only [zero_add, one_mul, mul_one, mul_comm, Function.comp_def, Pi.add_apply, id_eq] using
      (hdiff (x + t * e)).hasDerivAt.comp t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).mul_const e))
  have hcontinuous : Continuous (fun t : ℝ => e * deriv ψ (x + t * e)) :=
    continuous_const.mul ((contDiff_infty_iff_deriv.mp hψ).2.continuous.comp
      (continuous_const.add (continuous_id.mul_const e)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) 1) => hderiv t)
    (hcontinuous.intervalIntegrable (0 : ℝ) 1)
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [one_mul, zero_mul, add_zero] at hFTC
  linarith only [hFTC]

theorem returnChart_even_taylor_integral (ψ e : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (T θ : ℝ) :
    evenPart (fun t => ψ (t + T + e t)) θ =
      evenPart (fun t => ψ (t + T)) θ +
        evenPart (fun t => e t * ∫ a in (0 : ℝ)..1, deriv ψ (t + T + a * e t)) θ := by
  unfold evenPart
  dsimp only
  rw [returnChart_taylor_integral ψ hψ (θ + T) (e θ),
    returnChart_taylor_integral ψ hψ (-θ + T) (e (-θ))]
  ring

/-- The exact scalar chart derivative with the frozen residual retained
inside all evaluation points of the integral remainder. -/
theorem hasDerivAt_returnResidual_chart_variation_integral (F ψ : ℝ → ℝ) (T : ℝ)
    (g : ℝ → ℝ → ℝ) (θ : ℝ)
    (hF : Differentiable ℝ F) (hψ : ContDiff ℝ ∞ ψ)
    (hpos : ∀ x, 0 < deriv (oddPart F) x)
    (hleft : ∀ x, g 0 (oddPart F x) = x)
    (hright : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x,
      oddPart (fun y => F y + s * ψ (F y + T)) (g s x) = x)
    (hg : ContinuousAt (fun s => g s θ) 0) :
    HasDerivAt (fun s => evenPart (fun x => F x + s * ψ (F x + T)) (g s θ))
      (evenPart (fun t => ψ (t + T)) θ +
        evenPart (fun t => evenPart F (g 0 t) * ∫ a in (0 : ℝ)..1,
          deriv ψ (t + T + a * evenPart F (g 0 t))) θ -
        deriv (fun x => evenPart F (g 0 x)) θ *
          oddPart (fun t => ψ (t + T + evenPart F (g 0 t))) θ) 0 := by
  have h := hasDerivAt_returnResidual_chart_variation F ψ T g θ hF hψ.continuous
    hpos hleft hright hg
  exact h.congr_deriv (by rw [returnChart_even_taylor_integral ψ _ hψ T θ])

/-- The scalar derivative is exactly the decoding prescribed in N02.
The inverse family is the actual inverse of the varied odd chart, and its
parameter regularity assumption is only continuity at the base value.
The frozen residual occurs at the unchanged evaluation points inside
`circleChartError`. -/
theorem hasDerivAt_circleChartError_scalar (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (m : ℕ)
    (r v : CircleSpace S) (g : ℝ → ℝ → ℝ) (θ : ℝ)
    (htransport : Differentiable ℝ
      (fun t => stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m))
    (hψ : ContDiff ℝ ∞ ((S.circle (3 / 4 : ℝ)).decode v m))
    (hpos : ∀ t, 0 < deriv (rightChartCandidate S C z m) t)
    (hg0 : ∀ t, g 0 t = C.rightChartInverse z m t)
    (hleft : ∀ t, C.rightChartInverse z m (rightChartCandidate S C z m t) = t)
    (hright : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t,
      oddPart (fun y =>
        stateLeftChart S z.1 m (C.minusReturnInverse z m y) - C.travel m +
          s * (S.circle (3 / 4 : ℝ)).decode v m
            (stateLeftChart S z.1 m (C.minusReturnInverse z m y))) (g s t) = t)
    (hg : ContinuousAt (fun s => g s θ) 0)
    (hdecode : ∀ t, (S.circle (3 / 4 : ℝ)).decode r m t = returnResidualField S C z m t) :
    HasDerivAt (fun s => evenPart (fun y =>
      stateLeftChart S z.1 m (C.minusReturnInverse z m y) - C.travel m +
        s * (S.circle (3 / 4 : ℝ)).decode v m
          (stateLeftChart S z.1 m (C.minusReturnInverse z m y))) (g s θ))
      (circleRotationDifference S C v m θ + circleChartError S C z r v m θ) 0 := by
  let F : ℝ → ℝ := fun t =>
    stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m
  let ψ : ℝ → ℝ := (S.circle (3 / 4 : ℝ)).decode v m
  have hleft' (t : ℝ) : g 0 (oddPart F t) = t := by
    rw [hg0]
    exact hleft t
  have hright' : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t,
      oddPart (fun y => F y + s * ψ (F y + C.travel m)) (g s t) = t := by
    filter_upwards [hright] with s hs
    intro t
    simpa only [F, ψ, sub_add_cancel] using hs t
  have h := hasDerivAt_returnResidual_chart_variation_integral F ψ (C.travel m)
    g θ htransport hψ hpos hleft' hright' hg
  have heval (t : ℝ) : evenPart F (g 0 t) = returnResidualField S C z m t := by
    rw [hg0]
    rfl
  have hfun : (fun t => evenPart F (g 0 t)) = returnResidualField S C z m := funext heval
  have hdecodeFun : (S.circle (3 / 4 : ℝ)).decode r m =
      returnResidualField S C z m := funext hdecode
  have hvalue : HasDerivAt
      (fun s => evenPart (fun y => F y + s * ψ (F y + C.travel m)) (g s θ))
      (circleRotationDifference S C v m θ + circleChartError S C z r v m θ) 0 := by
    apply h.congr_deriv
    rw [hfun]
    simp_rw [heval]
    unfold circleRotationDifference circleChartError
    simp only [ψ, hdecodeFun]
    ring
  exact hvalue.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => by simp only [F, ψ, sub_add_cancel])

end ContinuousFlexibility.Statements
