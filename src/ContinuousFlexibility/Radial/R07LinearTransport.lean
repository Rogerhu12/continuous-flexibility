import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous parameter dependence of finite linear transport

On a compact time interval, joint continuity of the operator coefficients is
continuity into the sup-norm space of continuous operator curves.  Applying
Gronwall to the difference of two solution curves then proves continuity of
the transported endpoint state.  No smooth or normed structure on the
parameter space is required, and the solutions may be chosen arbitrarily.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology

/-- Forward finite transport for a linear equation depends continuously on
jointly continuous coefficients and a continuous initial state. -/
theorem continuous_linearODE_endpoint {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : X → ℝ → E →L[ℝ] E} {u : X → ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn (fun z : X × ℝ => A z.1 z.2) {z | z.2 ∈ Icc a b})
    (hu : ∀ p, ContinuousOn (u p) (Icc a b))
    (hderiv : ∀ p t, t ∈ Icc a b → HasDerivAt (u p) (A p t (u p t)) t)
    (hinit : Continuous (fun p => u p a)) :
    Continuous (fun p => u p b) := by
  have hAp (p : X) : ContinuousOn (A p) (Icc a b) :=
    hA.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  let B : X → C(Icc a b, E →L[ℝ] E) := fun p =>
    ⟨fun t => A p t.val, (hAp p).domRestrict⟩
  have hBc : Continuous B := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hA.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z => z.2.property)
  apply continuous_iff_continuousAt.mpr
  intro q
  let V : C(Icc a b, E) := ⟨fun t => u q t.val, (hu q).domRestrict⟩
  let δ : X → ℝ := fun p => ‖u p a - u q a‖
  let K : X → ℝ := fun p => ‖B p‖ + 1
  let ε : X → ℝ := fun p => ‖B p - B q‖ * ‖V‖
  let majorant : X → ℝ := fun p =>
    δ p * exp (K p * (b - a)) + ε p / K p * (exp (K p * (b - a)) - 1)
  have hK (p : X) : 0 < K p := add_pos_of_nonneg_of_pos (norm_nonneg (B p)) zero_lt_one
  have hδc : Continuous δ := (hinit.sub continuous_const).norm
  have hKc : Continuous K := by
    change Continuous (fun p : X => ‖B p‖ + (1 : ℝ))
    exact (hBc.norm : Continuous (fun p : X => ‖B p‖)).add continuous_const
  have hεc : Continuous ε := (hBc.sub continuous_const).norm.mul_const ‖V‖
  have hexp : Continuous (fun p => exp (K p * (b - a))) :=
    Real.continuous_exp.comp (hKc.mul_const (b - a))
  have hmajorant : Continuous majorant :=
    (hδc.mul hexp).add ((hεc.div hKc (fun p => (hK p).ne')).mul (hexp.sub continuous_const))
  have hzero : majorant q = 0 := by
    simp only [majorant, δ, ε, sub_self, norm_zero, zero_mul, zero_div, zero_add]
  have hbound (p : X) : ‖u p b - u q b‖ ≤ majorant p := by
    have hd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => u p t - u q t)
        (A p t (u p t) - A q t (u q t)) (Ici t) t := by
      intro t ht
      exact ((hderiv p t ⟨ht.1, ht.2.le⟩).sub
        (hderiv q t ⟨ht.1, ht.2.le⟩)).hasDerivWithinAt
    have hnorm (t : ℝ) (ht : t ∈ Ico a b) :
        ‖A p t (u p t) - A q t (u q t)‖ ≤ K p * ‖u p t - u q t‖ + ε p := by
      let t' : Icc a b := ⟨t, ht.1, ht.2.le⟩
      have hB : ‖A p t‖ ≤ K p :=
        ((B p).norm_coe_le_norm t').trans (le_add_of_nonneg_right zero_le_one)
      have hdiff : ‖A p t - A q t‖ ≤ ‖B p - B q‖ :=
        (B p - B q).norm_coe_le_norm t'
      have hV : ‖u q t‖ ≤ ‖V‖ := V.norm_coe_le_norm t'
      calc
        ‖A p t (u p t) - A q t (u q t)‖ =
            ‖A p t (u p t - u q t) + (A p t - A q t) (u q t)‖ := by
          congr 1
          simp only [map_sub, ContinuousLinearMap.sub_apply]
          abel
        _ ≤ ‖A p t (u p t - u q t)‖ + ‖(A p t - A q t) (u q t)‖ := norm_add_le _ _
        _ ≤ ‖A p t‖ * ‖u p t - u q t‖ + ‖A p t - A q t‖ * ‖u q t‖ :=
          add_le_add ((A p t).le_opNorm _) ((A p t - A q t).le_opNorm _)
        _ ≤ K p * ‖u p t - u q t‖ + ε p :=
          add_le_add (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
            (mul_le_mul hdiff hV (norm_nonneg _) (norm_nonneg _))
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      ((hu p).sub (hu q)) hd (show ‖u p a - u q a‖ ≤ δ p from le_rfl) hnorm b ⟨hab, le_rfl⟩
    rw [gronwallBound_of_K_ne_0 (hK p).ne'] at h
    exact h
  have hlim : Tendsto majorant (𝓝 q) (𝓝 0) := by
    simpa only [hzero] using (hmajorant.continuousAt : ContinuousAt majorant q)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hlim

/-- The same statement with prescribed data at the right endpoint follows
by reversing the real time coordinate. -/
theorem continuous_linearODE_endpoint_from_right {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : X → ℝ → E →L[ℝ] E} {u : X → ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn (fun z : X × ℝ => A z.1 z.2) {z | z.2 ∈ Icc a b})
    (hu : ∀ p, ContinuousOn (u p) (Icc a b))
    (hderiv : ∀ p t, t ∈ Icc a b → HasDerivAt (u p) (A p t (u p t)) t)
    (hinit : Continuous (fun p => u p b)) :
    Continuous (fun p => u p a) := by
  have hAc : ContinuousOn (fun z : X × ℝ => -A z.1 (-z.2))
      {z | z.2 ∈ Icc (-b) (-a)} := by
    refine (hA.comp (continuous_fst.prodMk continuous_snd.neg).continuousOn ?_).neg
    intro z hz
    change a ≤ -z.2 ∧ -z.2 ≤ b
    exact ⟨by linarith only [hz.2], by linarith only [hz.1]⟩
  have huc (p : X) : ContinuousOn (fun t => u p (-t)) (Icc (-b) (-a)) := by
    refine (hu p).comp continuous_neg.continuousOn ?_
    intro t ht
    exact ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
  have hdc (p : X) (t : ℝ) (ht : t ∈ Icc (-b) (-a)) :
      HasDerivAt (fun t => u p (-t)) ((-A p (-t)) (u p (-t))) t := by
    have h := (hderiv p (-t) ⟨by linarith only [ht.2], by linarith only [ht.1]⟩).scomp t
      (hasDerivAt_id t).neg
    simpa only [Function.comp_def, neg_one_smul, ContinuousLinearMap.neg_apply] using h
  have hi : Continuous (fun p => u p (-(-b))) := by simpa only [neg_neg] using hinit
  have h := continuous_linearODE_endpoint (neg_le_neg hab) hAc huc hdc hi
  simpa only [neg_neg] using h

/-- Finite linear transport is continuous in either orientation of the
unordered interval between the fixed initial and final points. -/
theorem continuous_linearODE_transport {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : X → ℝ → E →L[ℝ] E} {u : X → ℝ → E} {a b : ℝ}
    (hA : ContinuousOn (fun z : X × ℝ => A z.1 z.2) {z | z.2 ∈ uIcc a b})
    (hu : ∀ p, ContinuousOn (u p) (uIcc a b))
    (hderiv : ∀ p t, t ∈ uIcc a b → HasDerivAt (u p) (A p t (u p t)) t)
    (hinit : Continuous (fun p => u p a)) :
    Continuous (fun p => u p b) := by
  rcases le_total a b with hab | hba
  · simp only [uIcc_of_le hab] at hA hu hderiv
    exact continuous_linearODE_endpoint hab hA hu hderiv hinit
  · simp only [uIcc_of_ge hba] at hA hu hderiv
    exact continuous_linearODE_endpoint_from_right hba hA hu hderiv hinit

end ContinuousFlexibility.Radial
