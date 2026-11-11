import ContinuousFlexibility.Analysis.InteriorSpeedLocalization
import ContinuousFlexibility.Analysis.AiryHalfHolonomy

/-!
# True transport by the constructed interior flows

The radial variable is part of the actual ODE path. A genuine first
integral is constant along that path by the chain rule and the mean
value theorem. Applying the actual inverse endpoint map therefore
recovers the first integral from one fixed radial section.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def interiorEndpointParameter (a b r : ℝ) : ℝ × ℝ :=
  (2 * (r - a) / (b - a) - 1, 0)

theorem interiorEndpointParameter_mem {a b r : ℝ} (hab : a < b)
    (hr : r ∈ Icc a b) : interiorEndpointParameter a b r ∈ n04FlowParameterBox := by
  have hw : 0 < b - a := sub_pos.mpr hab
  have h0 : 0 ≤ 2 * (r - a) / (b - a) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hr.1)) hw.le
  have h2 : 2 * (r - a) / (b - a) ≤ 2 :=
    (div_le_iff₀ hw).mpr (by linarith [hr.2])
  change (2 * (r - a) / (b - a) - 1 ∈ Icc (-1 : ℝ) 1) ∧
    (0 : ℝ) ∈ Icc (-1 : ℝ) 1
  exact ⟨⟨by linarith, by linarith⟩, by norm_num⟩

theorem interiorFlowRadius_endpointParameter {a b : ℝ} (hab : a < b) (r : ℝ) :
    interiorFlowRadius a b 1 (interiorEndpointParameter a b r) = r := by
  dsimp only [interiorFlowRadius, interiorEndpointParameter]
  field_simp [sub_ne_zero.mpr hab.ne'] <;> ring

/-- This is a consequence of the actual ODE, not an assumption about a
chosen flow's parameter derivatives. -/
theorem interiorFlow_preserves_firstIntegral
    {a b : ℝ} (hab : a ≤ b) {f U : PolarPoint → ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations (interiorScalarFlowField f a b) Θ)
    (hU : ContinuousOn U (Icc a b ×ˢ (univ : Set ℝ)))
    (hUd : ∀ r ∈ Icc a b, ∀ θ : ℝ, DifferentiableAt ℝ U (r, θ))
    (htransport : ∀ r ∈ Icc a b, ∀ θ : ℝ,
      radialPartial U (r, θ) = -f (r, θ) * angularPartial U (r, θ))
    {v : ℝ × ℝ} (hv : v ∈ n04FlowParameterBox) (θ : ℝ) :
    U (interiorFlowRadius a b 1 v, Θ v 1 θ) = U (a, θ) := by
  let c : ℝ := (b - a) / 2 * (1 + v.1)
  have hR : Continuous (fun t : ℝ => interiorFlowRadius a b t v) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have hpath : ContinuousOn
      (fun t : ℝ => (interiorFlowRadius a b t v, Θ v t θ)) (Icc (0 : ℝ) 1) :=
    hR.continuousOn.prodMk (n04Flow_time_continuousOn hΘ v θ)
  have hcont : ContinuousOn
      (fun t : ℝ => U (interiorFlowRadius a b t v, Θ v t θ)) (Icc (0 : ℝ) 1) :=
    hU.comp hpath (fun t ht => ⟨interiorFlowRadius_mem hab ht hv, mem_univ _⟩)
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => U (interiorFlowRadius a b s v, Θ v s θ)) 0 t := by
    have hr : interiorFlowRadius a b t v ∈ Icc a b :=
      interiorFlowRadius_mem hab (Ioo_subset_Icc_self ht) hv
    have hrd : HasDerivAt (fun s : ℝ => interiorFlowRadius a b s v) c t := by
      simpa only [interiorFlowRadius, c, one_mul, id_eq] using
        ((hasDerivAt_id t).mul_const c).const_add a
    have hh := (hUd _ hr (Θ v t θ)).hasFDerivAt.comp_hasDerivAt t
      (hrd.prodMk (n04Flow_time_hasDerivAt hΘ v θ ht))
    have he : U ∘ (fun s : ℝ => (interiorFlowRadius a b s v, Θ v s θ)) =
        (fun s : ℝ => U (interiorFlowRadius a b s v, Θ v s θ)) := by
      funext s
      exact Function.comp_apply
    rw [he] at hh
    apply hh.congr_deriv
    rw [polarCLM_apply_decompose]
    change c * radialPartial U (interiorFlowRadius a b t v, Θ v t θ) +
      (c * f (interiorFlowRadius a b t v, Θ v t θ)) *
        angularPartial U (interiorFlowRadius a b t v, Θ v t θ) = 0
    rw [htransport _ hr (Θ v t θ)]
    ring
  obtain ⟨t, _, hzero⟩ := exists_hasDerivAt_eq_slope
    (fun t : ℝ => U (interiorFlowRadius a b t v, Θ v t θ))
    (fun _ => 0) zero_lt_one hcont hd
  have he : U (interiorFlowRadius a b 1 v, Θ v 1 θ) =
      U (interiorFlowRadius a b 0 v, Θ v 0 θ) := by
    have hh : 0 * ((1 : ℝ) - 0) =
        U (interiorFlowRadius a b 1 v, Θ v 1 θ) -
          U (interiorFlowRadius a b 0 v, Θ v 0 θ) :=
      (eq_div_iff (by norm_num : (1 : ℝ) - 0 ≠ 0)).mp hzero
    linarith only [hh]
  rw [show interiorFlowRadius a b 0 v = a by
    simp only [interiorFlowRadius, zero_mul, add_zero], hΘ.1 v θ] at he
  exact he

/-- Exact recovery from the actual inverse endpoint map. -/
theorem interiorFlow_firstIntegral_eq_inverse_section
    {a b : ℝ} (hab : a < b) {f U : PolarPoint → ℝ}
    {Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations (interiorScalarFlowField f a b) Θ)
    (hinverse : ∀ v θ, Θ v 1 (Ψ v 1 θ) = θ)
    (hU : ContinuousOn U (Icc a b ×ˢ (univ : Set ℝ)))
    (hUd : ∀ r ∈ Icc a b, ∀ θ : ℝ, DifferentiableAt ℝ U (r, θ))
    (htransport : ∀ r ∈ Icc a b, ∀ θ : ℝ,
      radialPartial U (r, θ) = -f (r, θ) * angularPartial U (r, θ))
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    U (r, θ) = U (a, Ψ (interiorEndpointParameter a b r) 1 θ) := by
  have h := interiorFlow_preserves_firstIntegral hab.le hΘ hU hUd htransport
    (interiorEndpointParameter_mem hab hr)
    (Ψ (interiorEndpointParameter a b r) 1 θ)
  rw [hinverse, interiorFlowRadius_endpointParameter hab r] at h
  exact h

end ContinuousFlexibility.Analysis
