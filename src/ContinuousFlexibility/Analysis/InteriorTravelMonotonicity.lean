module

public import ContinuousFlexibility.Analysis.InteriorFlowTransport

/-!
# The actual travel difference is monotone along the plus flow

The two first integrals use the minus and plus characteristic speeds.
Along the actual plus trajectory their half-difference has derivative
`c * (fplus - fminus) * angularPartial U / 2`. Ordered speeds and a
nonnegative angular derivative therefore propagate section bounds.
This is a statement along characteristics, without assuming radial
monotonicity at a fixed physical angle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem interiorFlow_travelDifference_monotone
    {a b : ℝ} (hab : a ≤ b) {fminus fplus U V : PolarPoint → ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations (interiorScalarFlowField fplus a b) Θ)
    (hU : ContinuousOn U (Icc a b ×ˢ (univ : Set ℝ)))
    (hV : ContinuousOn V (Icc a b ×ˢ (univ : Set ℝ)))
    (hUd : ∀ r ∈ Icc a b, ∀ θ : ℝ, DifferentiableAt ℝ U (r, θ))
    (hVd : ∀ r ∈ Icc a b, ∀ θ : ℝ, DifferentiableAt ℝ V (r, θ))
    (hminus : ∀ r ∈ Icc a b, ∀ θ : ℝ,
      radialPartial U (r, θ) = -fminus (r, θ) * angularPartial U (r, θ))
    (hplus : ∀ r ∈ Icc a b, ∀ θ : ℝ,
      radialPartial V (r, θ) = -fplus (r, θ) * angularPartial V (r, θ))
    (hspeeds : ∀ r ∈ Icc a b, ∀ θ : ℝ, fminus (r, θ) ≤ fplus (r, θ))
    (hangular : ∀ r ∈ Icc a b, ∀ θ : ℝ, 0 ≤ angularPartial U (r, θ))
    {v : ℝ × ℝ} (hv : v ∈ n04FlowParameterBox) (θ : ℝ) :
    MonotoneOn (fun t : ℝ =>
      (U (interiorFlowRadius a b t v, Θ v t θ) -
        V (interiorFlowRadius a b t v, Θ v t θ)) / 2) (Icc (0 : ℝ) 1) := by
  let c : ℝ := (b - a) / 2 * (1 + v.1)
  have hc : 0 ≤ c := mul_nonneg
    (div_nonneg (sub_nonneg.mpr hab) (by norm_num)) (by linarith only [hv.1.1])
  let path : ℝ → PolarPoint := fun t => (interiorFlowRadius a b t v, Θ v t θ)
  let τ : ℝ → ℝ := fun t => (U (path t) - V (path t)) / 2
  let dτ : ℝ → ℝ := fun t =>
    c * (fplus (path t) - fminus (path t)) * angularPartial U (path t) / 2
  have hpath : ContinuousOn path (Icc (0 : ℝ) 1) :=
    (continuous_const.add (continuous_id.mul continuous_const)).continuousOn.prodMk
      (n04Flow_time_continuousOn hΘ v θ)
  have hmaps : MapsTo path (Icc (0 : ℝ) 1) (Icc a b ×ˢ (univ : Set ℝ)) :=
    fun t ht => ⟨interiorFlowRadius_mem hab ht hv, mem_univ _⟩
  have hcont : ContinuousOn τ (Icc (0 : ℝ) 1) :=
    ((hU.comp hpath hmaps).sub (hV.comp hpath hmaps)).div_const 2
  have hnonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ dτ t := by
    have hr := interiorFlowRadius_mem hab ht hv
    exact div_nonneg
      (mul_nonneg (mul_nonneg hc (sub_nonneg.mpr (hspeeds _ hr _)))
        (hangular _ hr _)) (by norm_num)
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt τ (dτ t) t := by
    have hr := interiorFlowRadius_mem hab (Ioo_subset_Icc_self ht) hv
    have hrd : HasDerivAt (fun s : ℝ => interiorFlowRadius a b s v) c t := by
      simpa only [interiorFlowRadius, c, one_mul, id_eq] using
        ((hasDerivAt_id t).mul_const c).const_add a
    have hchain (W : PolarPoint → ℝ) (hW : DifferentiableAt ℝ W (path t)) :
        HasDerivAt (fun s : ℝ => W (path s))
          (c * radialPartial W (path t) +
            (c * fplus (path t)) * angularPartial W (path t)) t := by
      have h := hW.hasFDerivAt.comp_hasDerivAt t
        (hrd.prodMk (n04Flow_time_hasDerivAt hΘ v θ ht))
      have he : W ∘ path = (fun s : ℝ => W (path s)) := by
        funext s
        exact Function.comp_apply
      rw [he] at h
      apply h.congr_deriv
      rw [polarCLM_apply_decompose]
      rfl
    have h := ((hchain U (hUd _ hr _)).sub (hchain V (hVd _ hr _))).div_const 2
    apply h.congr_deriv
    dsimp only [dτ, path]
    rw [hminus _ hr _, hplus _ hr _]
    ring
  change MonotoneOn τ (Icc (0 : ℝ) 1)
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with heq | hlt
  · exact le_of_eq (congrArg τ heq)
  · have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs.1 ht.2
    obtain ⟨u, hu, he⟩ := exists_hasDerivAt_eq_slope τ dτ hlt
      (hcont.mono hsub) (fun u hu => hd u ⟨hs.1.trans_lt hu.1, hu.2.trans_le ht.2⟩)
    have hprod : dτ u * (t - s) = τ t - τ s :=
      (eq_div_iff (sub_pos.mpr hlt).ne').mp he
    have hn : 0 ≤ dτ u * (t - s) :=
      mul_nonneg (hnonneg u (hsub (Ioo_subset_Icc_self hu))) (sub_nonneg.mpr hst)
    linarith only [hprod, hn]

end ContinuousFlexibility.Analysis
