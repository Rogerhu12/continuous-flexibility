module

public import ContinuousFlexibility.Analysis.RootFlowParameterUnscale
public import ContinuousFlexibility.Analysis.RootDividedHeight
public import ContinuousFlexibility.Analysis.OpenGermBoundaryJets

/-!
# Exact removal of the root model's parameter normalization

The physical-side chart and divided height are unchanged after removing
the parameter normalization from the same chosen flow. The radial factor
contains exactly one power of the normalization, which cancels in the
height. Ordinary jets at the root follow from the open-side equality and
smoothness at that point; no quantitative collar size is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem positive_left_mul_rpow
    {a : ℝ} (ha : 0 < a) (b p : ℝ) :
    (a * b) ^ p = a ^ p * b ^ p := by
  by_cases hb : 0 ≤ b
  · exact Real.mul_rpow ha.le hb
  have hb' : b < 0 := lt_of_not_ge hb
  rw [Real.rpow_def_of_neg (mul_neg_of_pos_of_neg ha hb'),
    Real.rpow_def_of_pos ha, Real.rpow_def_of_neg hb',
    Real.log_mul ha.ne' hb'.ne, add_mul, Real.exp_add]
  ring

/-- The actual even coordinate is exactly the unscaled even coordinate
at the same physical radial distance. -/
theorem rootScaledInverseCoordinate_even_parameterUnscale
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) (θ : ℝ) :
    rootEven (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (x, θ) =
      rootEven (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h)
        (δ * x, θ) := by
  have hp := rootScaledInverseCoordinate_physical_eq_parameterUnscale
    Θ h hδ hx 1 θ
  have hm := rootScaledInverseCoordinate_physical_eq_parameterUnscale
    Θ h hδ hx (-1) θ
  simp only [one_mul, neg_one_mul] at hp hm
  simp only [rootEven, hp, hm]

/-- The actual odd coefficient has precisely the three-halves scale.
Only positive physical distances are used, so this proof does not
differentiate the piecewise total definition of the odd quotient. -/
theorem rootScaledInverseCoordinate_odd_parameterUnscale
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) (θ : ℝ) :
    rootOddCoefficient (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (x, θ) =
      δ ^ (3 / 2 : ℝ) *
        rootOddCoefficient (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h)
          (δ * x, θ) := by
  have hp := rootScaledInverseCoordinate_physical_eq_parameterUnscale
    Θ h hδ hx.le 1 θ
  have hm := rootScaledInverseCoordinate_physical_eq_parameterUnscale
    Θ h hδ hx.le (-1) θ
  simp only [one_mul, neg_one_mul] at hp hm
  simp only [rootOddCoefficient, rootOdd, if_neg hx.ne',
    if_neg (mul_pos hδ hx).ne']
  rw [← hp, ← hm, Real.mul_rpow hδ.le hx.le]
  have hd : δ ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  have hxp : x ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp [hd, hxp]
  <;> ring

/-- The radial power absorbs exactly one normalization factor, including
for the total real power away from the positive model collar. -/
theorem extendedRootRadialFactor_parameterUnscale_pos
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) (θ : ℝ) :
    extendedRootRadialFactor (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (x, θ) =
      δ * extendedRootRadialFactor
        (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h) (δ * x, θ) := by
  simp only [extendedRootRadialFactor,
    extendedRootOddCoefficient_of_nonneg _ (p := (x, θ)) hx.le,
    extendedRootOddCoefficient_of_nonneg _ (p := (δ * x, θ)) (mul_pos hδ hx).le]
  rw [rootScaledInverseCoordinate_odd_parameterUnscale Θ h hδ hx θ]
  have hreorder (v : ℝ) : (3 / 2 : ℝ) * (δ ^ (3 / 2 : ℝ) * v) =
      δ ^ (3 / 2 : ℝ) * ((3 / 2 : ℝ) * v) := by ring
  rw [hreorder, positive_left_mul_rpow (Real.rpow_pos_of_pos hδ _),
    ← Real.rpow_mul hδ.le,
    show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]

/-- The displayed extended charts agree on the physical open half-plane
after the exact radial substitution. No new flow or chart is selected. -/
theorem extendedRootEvenOddChart_parameterUnscale_pos
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) (θ : ℝ) :
    extendedRootEvenOddChart (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (x, θ) =
      extendedRootEvenOddChart
        (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h) (δ * x, θ) := by
  apply Prod.ext
  · change x * extendedRootRadialFactor _ (x, θ) =
      (δ * x) * extendedRootRadialFactor _ (δ * x, θ)
    rw [extendedRootRadialFactor_parameterUnscale_pos Θ h hδ hx θ]
    ring
  · change extendedRootEven _ (x, θ) = extendedRootEven _ (δ * x, θ)
    rw [extendedRootEven_of_nonneg _ hx.le,
      extendedRootEven_of_nonneg _ (mul_pos hδ hx).le]
    exact rootScaledInverseCoordinate_even_parameterUnscale Θ h hδ hx.le θ

/-- The radial normalization cancels from the actual divided height.
The input divided coefficient is only reparametrized, not replaced. -/
theorem rootDividedHeight_parameterUnscale_pos
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ) (V : PolarPoint → ℝ)
    {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) (θ : ℝ) :
    rootDividedHeight δ (fun p => V (δ * p.1, p.2))
        (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (x, θ) =
      rootDividedHeight 1 V
        (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h) (δ * x, θ) := by
  unfold rootDividedHeight
  rw [extendedRootRadialFactor_parameterUnscale_pos Θ h hδ hx θ,
    mul_div_mul_left _ _ hδ.ne', one_mul]

/-- Equal smooth physical-side models have equal full ordinary jets at
the root after removing the same parameter scale. The collar radius
does not enter this identity or any bound transferred through it. -/
theorem iteratedFDeriv_rootModel_parameterUnscale
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F G : PolarPoint → Y} {δ θ : ℝ} (hδ : 0 < δ)
    (he : ∀ x : ℝ, 0 < x → ∀ η : ℝ, F (x, η) = G (δ * x, η))
    (hF : ContDiffAt ℝ ∞ F (0, θ))
    (hG : ContDiffAt ℝ ∞ G (0, θ)) (n : ℕ) :
    iteratedFDeriv ℝ n (fun p : PolarPoint => F (p.1 / δ, p.2)) (0, θ) =
      iteratedFDeriv ℝ n G (0, θ) := by
  have harg : ContDiff ℝ ∞ (fun p : PolarPoint => (p.1 / δ, p.2)) :=
    (contDiff_fst.div_const δ).prodMk contDiff_snd
  have hFs : ContDiffAt ℝ ∞ (fun p : PolarPoint => F (p.1 / δ, p.2)) (0, θ) := by
    have hF' : ContDiffAt ℝ ∞ F
        ((fun p : PolarPoint => (p.1 / δ, p.2)) (0, θ)) := by
      simpa only [zero_div] using hF
    have hh := hF'.comp (0, θ) harg.contDiffAt
    simpa only [Function.comp_def] using hh
  have hclosure : (0, θ) ∈ closure (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rw [closure_prod_eq, closure_Ioi, closure_univ]
    exact mk_mem_prod self_mem_Ici (mem_univ θ)
  apply iteratedFDeriv_eq_of_eqOn_open_of_mem_closure
    (isOpen_Ioi.prod isOpen_univ) hclosure _ hFs hG n
  intro p hp
  have hh := he (p.1 / δ) (div_pos hp.1 hδ) p.2
  have hc : δ * (p.1 / δ) = p.1 := by field_simp [hδ.ne']
  simpa only [hc] using hh

/-- Full chart jets at the true root are the unscaled model jets. The
only smoothness inputs concern the two actual displayed models. -/
theorem iteratedFDeriv_rootChart_parameterUnscale
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ)
    {δ θ : ℝ} (hδ : 0 < δ)
    (hscaled : ContDiffAt ℝ ∞
      (extendedRootEvenOddChart (rootScaledInverseCoordinate Θ h (Real.sqrt δ))) (0, θ))
    (hunscaled : ContDiffAt ℝ ∞
      (extendedRootEvenOddChart
        (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h)) (0, θ)) (n : ℕ) :
    iteratedFDeriv ℝ n (fun p : PolarPoint =>
      extendedRootEvenOddChart (rootScaledInverseCoordinate Θ h (Real.sqrt δ))
        (p.1 / δ, p.2)) (0, θ) =
      iteratedFDeriv ℝ n (extendedRootEvenOddChart
        (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h)) (0, θ) :=
  iteratedFDeriv_rootModel_parameterUnscale hδ
    (fun x hx η => extendedRootEvenOddChart_parameterUnscale_pos Θ h hδ hx η)
    hscaled hunscaled n

/-- The same cancellation applies to every real power of the actual
height, so it includes height and inverse height without a delta cost. -/
theorem iteratedFDeriv_rootHeight_power_parameterUnscale
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (h : ℝ → ℝ) (V : PolarPoint → ℝ)
    {δ θ : ℝ} (hδ : 0 < δ)
    (hscaled : ContDiffAt ℝ ∞
      (rootDividedHeight δ (fun p => V (δ * p.1, p.2))
        (rootScaledInverseCoordinate Θ h (Real.sqrt δ))) (0, θ))
    (hunscaled : ContDiffAt ℝ ∞
      (rootDividedHeight 1 V
        (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h)) (0, θ))
    (hscaled0 : rootDividedHeight δ (fun p => V (δ * p.1, p.2))
      (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (0, θ) ≠ 0)
    (hunscaled0 : rootDividedHeight 1 V
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h) (0, θ) ≠ 0)
    (a : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun p : PolarPoint =>
      rootDividedHeight δ (fun q => V (δ * q.1, q.2))
        (rootScaledInverseCoordinate Θ h (Real.sqrt δ)) (p.1 / δ, p.2) ^ a) (0, θ) =
      iteratedFDeriv ℝ n (fun p => rootDividedHeight 1 V
        (rootInverseCoordinate (rootFlowParameterUnscale Θ δ) h) p ^ a) (0, θ) :=
  iteratedFDeriv_rootModel_parameterUnscale hδ
    (fun x hx η => congrArg (fun y : ℝ => y ^ a)
      (rootDividedHeight_parameterUnscale_pos Θ h V hδ hx η))
    (hscaled.rpow_const_of_ne hscaled0) (hunscaled.rpow_const_of_ne hunscaled0) n

end ContinuousFlexibility.Analysis
