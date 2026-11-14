module

public import ContinuousFlexibility.Analysis.RootScaledInverseCoordinate
public import ContinuousFlexibility.Analysis.N04bRootFlowIdentification

/-!
# Identifying the same controlled root flow after its exact rescaling

The regularized family below is supplied with its actual ODE; it is never
reselected. Physical distance is δ x and the second normalized parameter
is σ sqrt(δ) x^(3/2). The comparison trajectory needs only closed-time
continuity and the ordinary interior ODE.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem rootPhysicalSpeed_parameterScale
    (d c : PolarPoint → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (σ r θ : ℝ) :
    rootPhysicalSpeed (rootParameterScaledDrift d δ)
        (rootParameterScaledSpeed c δ (Real.sqrt δ)) σ (r, θ) =
      δ * rootPhysicalSpeed d c σ (δ * r, θ) := by
  simp only [rootPhysicalSpeed, rootParameterScaledDrift,
    rootParameterScaledSpeed, Real.sqrt_mul hδ]
  ring

/-- A complete stored family is identified with the already controlled
family, with exactly the physical parameter δ ζ = σ (δ x)^(3/2). -/
theorem rootRescaledFlow_eq_storedFlow
    {d c : PolarPoint → ℝ} {T R δ σ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hcperiod : ∀ r, Function.Periodic (fun θ => c (r, θ)) T)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hΦinit : ∀ θ, Φ θ 0 = θ)
    (hΦcont : ∀ θ, ContinuousOn (Φ θ) (Icc (0 : ℝ) (δ * R)))
    (hΦflow : ∀ θ r, r ∈ Ioo (0 : ℝ) (δ * R) →
      HasDerivAt (Φ θ) (rootPhysicalSpeed d c σ (r, Φ θ r)) r)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) R) (θ : ℝ) :
    Θ (x, (σ * Real.sqrt δ) * x ^ (3 / 2 : ℝ)) 1 θ = Φ θ (δ * x) := by
  let Ψ : ℝ → ℝ → ℝ := fun θ r => Φ θ (δ * r)
  have hscaled := contDiff_rootParameterScaledFields hd hc δ (Real.sqrt δ)
  have hperiod := periodic_rootParameterScaledFields hdperiod hcperiod δ (Real.sqrt δ)
  have hflow := rootFlowParameterScale_equations hΘ (Real.sqrt δ)
  have hΨinit : ∀ θ, Ψ θ 0 = θ := by
    intro θ
    simpa only [Ψ, mul_zero] using hΦinit θ
  have hΨcont : ∀ θ, ContinuousOn (Ψ θ) (Icc (0 : ℝ) R) := by
    intro θ
    exact (hΦcont θ).comp (continuous_const.mul continuous_id).continuousOn
      (fun r hr => ⟨mul_nonneg hδ.le hr.1, mul_le_mul_of_nonneg_left hr.2 hδ.le⟩)
  have hΨflow : ∀ θ r, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt (Ψ θ)
        (rootPhysicalSpeed (rootParameterScaledDrift d δ)
          (rootParameterScaledSpeed c δ (Real.sqrt δ)) σ (r, Ψ θ r)) r := by
    intro θ r hr
    have hlin : HasDerivAt (fun y : ℝ => δ * y) δ r := by
      simpa only [mul_one, id_eq] using (hasDerivAt_id r).const_mul δ
    have hh := (hΦflow θ (δ * r)
      ⟨mul_pos hδ hr.1, mul_lt_mul_of_pos_left hr.2 hδ⟩).comp r hlin
    have he : (Φ θ) ∘ (fun y : ℝ => δ * y) = Ψ θ := by
      funext y
      exact Function.comp_apply
    rw [he] at hh
    apply hh.congr_deriv
    rw [rootPhysicalSpeed_parameterScale d c hδ.le]
    ring
  have heq := n04b_rootRegularizedFlow_eq_storedFlow hR hT hscaled.1 hscaled.2
    hperiod.1 hperiod.2 hflow.1 hflow.2 hΨinit hΨcont hΨflow hx θ
  change Θ (x, Real.sqrt δ * (σ * x ^ (3 / 2 : ℝ))) 1 θ = Φ θ (δ * x) at heq
  rw [show Real.sqrt δ * (σ * x ^ (3 / 2 : ℝ)) =
    (σ * Real.sqrt δ) * x ^ (3 / 2 : ℝ) by ring] at heq
  exact heq

/-- The single-trajectory form does not require continuity in its initial
angle. The auxiliary Picard trajectory is only used to prove uniqueness;
the controlled regularized family in the conclusion is the original Θ. -/
theorem rootRescaledFlow_eq_storedTrajectory
    {d c : PolarPoint → ℝ} {T R δ σ θ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdperiod : ∀ r, Function.Periodic (fun η => d (r, η)) T)
    (hcperiod : ∀ r, Function.Periodic (fun η => c (r, η)) T)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hfinit : f 0 = θ) (hfcont : ContinuousOn f (Icc (0 : ℝ) (δ * R)))
    (hfflow : ∀ r ∈ Ioo (0 : ℝ) (δ * R),
      HasDerivAt f (rootPhysicalSpeed d c σ (r, f r)) r)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) R) :
    Θ (x, (σ * Real.sqrt δ) * x ^ (3 / 2 : ℝ)) 1 θ = f (δ * x) := by
  obtain ⟨Ψ, hΨinit, hΨflow, _⟩ := exists_rootPhysicalFlow_on_Icc
    (mul_nonneg hδ.le hR.le) hT hd hc hdperiod hcperiod σ
  have hΨcont (η : ℝ) : ContinuousOn (Ψ η) (Icc (0 : ℝ) (δ * R)) :=
    HasDerivWithinAt.continuousOn (hΨflow η)
  have hΨopen (η r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (δ * R)) :
      HasDerivAt (Ψ η) (rootPhysicalSpeed d c σ (r, Ψ η r)) r :=
    (hΨflow η r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have heq := n04b_rootPhysicalFlow_unique (mul_pos hδ hR) hd hc
    (hΨcont θ) (hΨopen θ) hfcont hfflow ((hΨinit θ).trans hfinit.symm)
  exact (rootRescaledFlow_eq_storedFlow hR hδ hT hd hc hdperiod hcperiod
    hΘ hΨinit hΨcont hΨopen hx θ).trans
      (heq ⟨mul_nonneg hδ.le hx.1, mul_le_mul_of_nonneg_left hx.2 hδ.le⟩)

end ContinuousFlexibility.Analysis
