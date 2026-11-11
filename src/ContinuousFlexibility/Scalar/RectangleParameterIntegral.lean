import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Smooth parameters in compact physical integrals

The parameter derivatives are derivatives of the actual integrand. Compactness
of a parameter ball times the physical integration set supplies the uniform
bound needed for differentiation under the integral. Iterating that argument
gives every mixed derivative, including arbitrary direction tuples.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {P X F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure X} [IsLocallyFiniteMeasure μ]

/-- Joint smoothness of the derivative in the parameter, with the physical
point retained as a variable. -/
theorem contDiffAt_parameter_fderiv
    {f : P × X → F} {p : P} {x : X}
    (hf : ContDiffAt ℝ ∞ f (p, x)) :
    ContDiffAt ℝ ∞
      (fun z : P × X => fderiv ℝ (fun q : P => f (q, z.2)) z.1) (p, x) := by
  have h : ContDiffAt ℝ ∞
      (fun z : (P × X) × P => f (z.2, z.1.2)) ((p, x), p) :=
    hf.comp ((p, x), p) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact h.fderiv contDiffAt_fst (by simp)

/-- All parameter jets remain jointly smooth. -/
theorem contDiffAt_parameter_iteratedFDeriv
    {f : P × X → F} {p : P} {x : X}
    (hf : ContDiffAt ℝ ∞ f (p, x)) (s : ℕ) :
    ContDiffAt ℝ ∞
      (fun z : P × X => iteratedFDeriv ℝ s (fun q : P => f (q, z.2)) z.1)
      (p, x) := by
  induction s with
  | zero =>
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ P F).symm : F →L[ℝ] P [×0]→L[ℝ] F)
  | succ s hs =>
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      exact (contDiffAt_parameter_fderiv hs).continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => P) F).symm :
          (P →L[ℝ] P [×s]→L[ℝ] F) →L[ℝ] P [×(s + 1)]→L[ℝ] F)

private theorem continuousOn_parameter_slice
    {f : P × X → F} {O : Set P} {K : Set X}
    (hf : ∀ p ∈ O, ∀ x ∈ K, ContDiffAt ℝ ∞ f (p, x)) {p : P} (hp : p ∈ O) :
    ContinuousOn (fun x => f (p, x)) K := by
  intro x hx
  exact ((hf p hp x hx).continuousAt.comp
    (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

/-- The compact-set parameter derivative. The dominating function is a
constant bound on a compact parameter ball times the physical set. -/
theorem hasFDerivAt_compactIntegral_parameter
    {f : P × X → F} {O : Set P} {K : Set X}
    (hO : IsOpen O) (hK : IsCompact K)
    (hf : ∀ p ∈ O, ∀ x ∈ K, ContDiffAt ℝ ∞ f (p, x))
    {p : P} (hp : p ∈ O) :
    HasFDerivAt (fun q => ∫ x in K, f (q, x) ∂μ)
      (∫ x in K, fderiv ℝ (fun q => f (q, x)) p ∂μ) p := by
  obtain ⟨ε, hε, hεO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hp)
  have hδ : 0 < ε / 2 := half_pos hε
  have hball : closedBall p (ε / 2) ⊆ O := by
    intro q hq
    apply hεO
    exact lt_of_le_of_lt hq (half_lt_self hε)
  have hdf : ∀ q ∈ O, ∀ x ∈ K, ContDiffAt ℝ ∞
      (fun z : P × X => fderiv ℝ (fun q => f (q, z.2)) z.1) (q, x) :=
    fun q hq x hx => contDiffAt_parameter_fderiv (hf q hq x hx)
  have hcont : ContinuousOn
      (fun z : P × X => fderiv ℝ (fun q => f (q, z.2)) z.1)
      (closedBall p (ε / 2) ×ˢ K) := by
    intro z hz
    exact (hdf z.1 (hball hz.1) z.2 hz.2).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := ((isCompact_closedBall p (ε / 2)).prod hK).exists_bound_of_continuousOn hcont
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ.restrict K) (s := closedBall p (ε / 2)) (bound := fun _ => M)
    (closedBall_mem_nhds p hδ)
  · filter_upwards [hO.mem_nhds hp] with q hq
    exact ((continuousOn_parameter_slice hf hq).integrableOn_compact hK).aestronglyMeasurable
  · exact (continuousOn_parameter_slice hf hp).integrableOn_compact hK
  · exact ((continuousOn_parameter_slice hdf hp).integrableOn_compact hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro q hq
    exact hM (q, x) ⟨hq, hx⟩
  · exact integrableOn_const hK.measure_ne_top
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro q hq
    exact (((hf q (hball hq) x hx).comp q
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).hasFDerivAt

private theorem contDiffAt_compactIntegral_parameter_nat (s : ℕ)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : P × X → F} {O : Set P} {K : Set X}
    (hO : IsOpen O) (hK : IsCompact K)
    (hf : ∀ p ∈ O, ∀ x ∈ K, ContDiffAt ℝ ∞ f (p, x))
    {p : P} (hp : p ∈ O) :
    ContDiffAt ℝ s (fun q => ∫ x in K, f (q, x) ∂μ) p := by
  induction s generalizing F with
  | zero =>
      apply contDiffAt_zero.mpr
      refine ⟨O, hO.mem_nhds hp, ?_⟩
      intro q hq
      have hd := hasFDerivAt_compactIntegral_parameter (μ := μ) hO hK hf hq
      exact hd.continuousAt.continuousWithinAt
  | succ s hs =>
      rw [show ((s + 1 : ℕ) : ℕ∞ω) = (s : ℕ∞ω) + 1 by simp]
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun q => ∫ x in K, fderiv ℝ (fun q => f (q, x)) q ∂μ,
        ⟨O, hO.mem_nhds hp, fun q hq => hasFDerivAt_compactIntegral_parameter hO hK hf hq⟩,
        ?_⟩
      exact hs
        (fun q hq x hx => contDiffAt_parameter_fderiv (hf q hq x hx))

/-- Smoothness of compact physical integrals in all finite-dimensional parameters. -/
theorem contDiffAt_compactIntegral_parameter
    {f : P × X → F} {O : Set P} {K : Set X}
    (hO : IsOpen O) (hK : IsCompact K)
    (hf : ∀ p ∈ O, ∀ x ∈ K, ContDiffAt ℝ ∞ f (p, x))
    {p : P} (hp : p ∈ O) :
    ContDiffAt ℝ ∞ (fun q => ∫ x in K, f (q, x) ∂μ) p := by
  apply contDiffAt_infty.mpr
  intro s
  exact contDiffAt_compactIntegral_parameter_nat s hO hK hf hp

/-- Every parameter derivative commutes with the compact integral as a
continuous multilinear map. -/
theorem iteratedFDeriv_compactIntegral_parameter
    {f : P × X → F} {O : Set P} {K : Set X}
    (hO : IsOpen O) (hK : IsCompact K)
    (hf : ∀ p ∈ O, ∀ x ∈ K, ContDiffAt ℝ ∞ f (p, x))
    (s : ℕ) {p : P} (hp : p ∈ O) :
    iteratedFDeriv ℝ s (fun q => ∫ x in K, f (q, x) ∂μ) p =
      ∫ x in K, iteratedFDeriv ℝ s (fun q => f (q, x)) p ∂μ := by
  induction s generalizing p with
  | zero =>
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ P F).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun x => f (p, x))).symm
  | succ s hs =>
      have heq : iteratedFDeriv ℝ s (fun q => ∫ x in K, f (q, x) ∂μ) =ᶠ[𝓝 p]
          (fun q => ∫ x in K, iteratedFDeriv ℝ s (fun q => f (q, x)) q ∂μ) := by
        filter_upwards [hO.mem_nhds hp] with q hq using hs hq
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      rw [heq.fderiv_eq]
      rw [(hasFDerivAt_compactIntegral_parameter hO hK
        (fun q hq x hx => contDiffAt_parameter_iteratedFDeriv (hf q hq x hx) s) hp).fderiv]
      exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => P) F).symm.toContinuousLinearEquiv.integral_comp_comm
          (fun x => fderiv ℝ (iteratedFDeriv ℝ s (fun q => f (q, x))) p)).symm

/-- Evaluating the mixed derivative in arbitrary directions also commutes
with the physical integral. -/
theorem iteratedFDeriv_compactIntegral_parameter_apply
    {f : P × X → F} {O : Set P} {K : Set X}
    (hO : IsOpen O) (hK : IsCompact K)
    (hf : ∀ p ∈ O, ∀ x ∈ K, ContDiffAt ℝ ∞ f (p, x))
    (s : ℕ) {p : P} (hp : p ∈ O) (v : Fin s → P) :
    iteratedFDeriv ℝ s (fun q => ∫ x in K, f (q, x) ∂μ) p v =
      ∫ x in K, iteratedFDeriv ℝ s (fun q => f (q, x)) p v ∂μ := by
  rw [iteratedFDeriv_compactIntegral_parameter hO hK hf s hp]
  apply ContinuousMultilinearMap.integral_apply
  exact (continuousOn_parameter_slice
    (fun q hq x hx => contDiffAt_parameter_iteratedFDeriv (hf q hq x hx) s) hp).integrableOn_compact hK

/-- The fixed-interval form of the compact integration theorem. -/
theorem contDiffAt_intervalIntegral_parameter
    {f : P × ℝ → F} {O : Set P} {a b : ℝ}
    (hO : IsOpen O) (hab : a ≤ b)
    (hf : ∀ p ∈ O, ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ f (p, t))
    {p : P} (hp : p ∈ O) :
    ContDiffAt ℝ ∞ (fun q => ∫ t in a..b, f (q, t)) p := by
  simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact contDiffAt_compactIntegral_parameter hO isCompact_Icc hf hp

/-- The physical iterated interval integral is the compact-rectangle
integral. The normalization is an arbitrary fixed scalar. -/
theorem rectangleIntegral_eq_compactIntegral
    {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) (C : ℝ) :
    (∫ r in a..b, C * ∫ θ in c..d, f (r, θ)) =
      ∫ x in Icc a b ×ˢ Icc c d, C * f x := by
  rw [intervalIntegral.integral_const_mul, integral_const_mul]
  congr 1
  rw [Measure.volume_eq_prod, setIntegral_prod f
    (hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))]
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    ← integral_Icc_eq_integral_Ioc]

/-- All finite-parameter mixed derivatives commute with the exact
`dr dθ` rectangle integral, with arbitrary normalization and directions. -/
theorem iteratedFDeriv_rectangleIntegral_parameter
    {f : P × (ℝ × ℝ) → ℝ} {O : Set P} {a b c d : ℝ}
    (hO : IsOpen O) (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ∀ p ∈ O, ∀ x ∈ Icc a b ×ˢ Icc c d, ContDiffAt ℝ ∞ f (p, x))
    (C : ℝ) (s : ℕ) {p : P} (hp : p ∈ O) (v : Fin s → P) :
    iteratedFDeriv ℝ s (fun q => ∫ r in a..b, C * ∫ θ in c..d, f (q, (r, θ))) p v =
      ∫ r in a..b, C * ∫ θ in c..d,
        iteratedFDeriv ℝ s (fun q => f (q, (r, θ))) p v := by
  have heq : (fun q => ∫ r in a..b, C * ∫ θ in c..d, f (q, (r, θ))) =ᶠ[𝓝 p]
      (fun q => ∫ x in Icc a b ×ˢ Icc c d, C * f (q, x)) := by
    filter_upwards [hO.mem_nhds hp] with q hq
    exact rectangleIntegral_eq_compactIntegral hab hcd
      (continuousOn_parameter_slice hf hq) C
  rw [(heq.iteratedFDeriv ℝ s).eq_of_nhds]
  rw [iteratedFDeriv_compactIntegral_parameter_apply hO (isCompact_Icc.prod isCompact_Icc)
    (fun q hq x hx => contDiffAt_const.mul (hf q hq x hx)) s hp v]
  have hjet : ContinuousOn
      (fun x : ℝ × ℝ => iteratedFDeriv ℝ s (fun q => f (q, x)) p v)
      (Icc a b ×ˢ Icc c d) := by
    intro x hx
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => P) ℝ v).continuous.continuousAt.comp
      ((contDiffAt_parameter_iteratedFDeriv (hf p hp x hx) s).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id))).continuousWithinAt
  rw [rectangleIntegral_eq_compactIntegral hab hcd hjet C]
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro x hx
  have hs : ContDiffAt ℝ s (fun q => f (q, x)) p :=
    ((hf p hp x hx).comp p (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  simpa only [Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun A : P [×s]→L[ℝ] ℝ => A v)
      (iteratedFDeriv_const_smul_apply (a := C) hs)

end ContinuousFlexibility
