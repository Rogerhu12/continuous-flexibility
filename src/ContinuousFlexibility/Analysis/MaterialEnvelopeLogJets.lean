module

public import ContinuousFlexibility.Analysis.MaterialEndpointGlobalJets

/-!
# The actual material envelope logarithm

The endpoint formula for log E0 has symbol order at most three. The shared
endpoint-to-global lemma therefore bounds its positive material derivatives
for every actual IsMaterialData witness, including the compact middle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Real Set Filter
open ContinuousFlexibility.Analysis
open ContinuousFlexibility.Radial (RadialSymbolBounds)
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem envelope_rpow_symbol (s : ℝ) :
    RadialSymbolBounds 1 s (fun x : ℝ => x ^ s) := by
  refine ⟨contDiffOn_id.rpow_const_of_ne (fun _ hx => ne_of_gt hx), ?_⟩
  intro n
  refine ⟨‖(descPochhammer ℝ n).eval s‖, norm_nonneg _, ?_⟩
  intro x _ hx
  rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]

private theorem envelope_symbol_weaken {s t : ℝ} {f : ℝ → ℝ}
    (hf : RadialSymbolBounds 1 s f) (hst : s ≤ t) : RadialSymbolBounds 1 t f := by
  refine ⟨hf.1, fun n => ?_⟩
  obtain ⟨C, hC, hb⟩ := hf.2 n
  exact ⟨C, hC, fun x hx hx₀ => (hb x hx hx₀).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (sub_le_sub_right hst _)) hC)⟩

private theorem envelope_constant_symbol (c : ℝ) :
    RadialSymbolBounds 1 0 (fun _ : ℝ => c) := by
  simpa only [Real.rpow_zero, mul_one] using (envelope_rpow_symbol 0).const_mul c

private theorem envelope_shifted_inverse_symbol (c : ℝ) (hc : 0 ≤ c) :
    RadialSymbolBounds 1 (-1) (fun x : ℝ => (x + c)⁻¹) := by
  have hs : ContDiffOn ℝ ∞ (fun x : ℝ => x + c) (Ioi 0) :=
    contDiffOn_id.add contDiffOn_const
  refine ⟨hs.inv (fun x hx => (add_pos_of_pos_of_nonneg hx hc).ne'), fun n => ?_⟩
  let s : ℝ := -1
  let f : ℝ → ℝ := fun x => x ^ s
  have hF : (fun x : ℝ => (x + c)⁻¹) = (fun x => f (x + c)) := by
    funext x
    exact (Real.rpow_neg_one (x + c)).symm
  obtain ⟨C, hC, hb⟩ := (envelope_rpow_symbol s).2 n
  refine ⟨C, hC, fun x hx hx₀ => ?_⟩
  rw [hF, iteratedDeriv_comp_add_const]
  have hle : x ≤ x + c := le_add_of_nonneg_right hc
  exact (hb (x + c) (hx.trans hle) (hx₀.trans_le hle)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx₀ hle
        (sub_nonpos.mpr (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Nat.cast_nonneg _)))) hC)

private theorem envelope_shifted_log_symbol (c : ℝ) (hc : 0 ≤ c) (s : ℝ) (hs : 0 < s) :
    RadialSymbolBounds 1 s (fun x : ℝ => Real.log (x + c)) := by
  have hpos (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : 0 < x + c := add_pos_of_pos_of_nonneg hx hc
  have hlog : ContDiffOn ℝ ∞ (fun x : ℝ => Real.log (x + c)) (Ioi 0) :=
    (contDiffOn_id.add contDiffOn_const).log (fun x hx => (hpos x hx).ne')
  refine ⟨hlog, fun n => ?_⟩
  cases n with
  | zero =>
    refine ⟨(1 + c) ^ s / s, div_nonneg (Real.rpow_nonneg (by linarith) _) hs.le, ?_⟩
    intro x hx hx₀
    have hx1 : 1 ≤ x + c := hx.trans (le_add_of_nonneg_right hc)
    have hp := hpos x hx₀
    have hpow : x + c ≤ (1 + c) * x := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hx)]
    rw [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
    change ‖Real.log (x + c)‖ ≤ _
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1)]
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hp s)
    rw [Real.log_rpow hp] at h
    have ha : Real.log (x + c) ≤ (x + c) ^ s / s := by
      apply (le_div_iff₀ hs).mpr
      linarith only [h]
    refine ha.trans ?_
    rw [div_mul_eq_mul_div, ← Real.mul_rpow (by linarith : 0 ≤ 1 + c) hx₀.le]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hp.le hpow hs.le) hs.le
  | succ n =>
    obtain ⟨C, hC, hb⟩ := (envelope_shifted_inverse_symbol c hc).2 n
    refine ⟨C, hC, fun x hx hx₀ => ?_⟩
    have he : deriv (fun y : ℝ => Real.log (y + c)) =ᶠ[𝓝 x] (fun y => (y + c)⁻¹) := by
      filter_upwards [Ioi_mem_nhds hx₀] with y hy
      have hd := (((hasDerivAt_id' y).add_const c).log (hpos y hy).ne').deriv
      simpa only [one_div] using hd
    rw [iteratedDeriv_succ', (he.iteratedDeriv n).eq_of_nhds]
    exact (hb x hx hx₀).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by push_cast; linarith)) hC)

/-- The exponent in the genuine endpoint E0 model is
1 + x^(5/2) log(exp(1)+x), of symbol order three. -/
theorem materialEndpointLogE0_symbol :
    RadialSymbolBounds 1 3 (fun x => Real.log (materialE0 x)) := by
  have hl : RadialSymbolBounds 1 (1 / 2) materialLogFactor := by
    have he : (fun x : ℝ => Real.log (x + Real.exp 1)) = materialLogFactor := by
      funext x
      change Real.log (x + Real.exp 1) = Real.log (Real.exp 1 + x)
      rw [add_comm x]
    rw [← he]
    exact envelope_shifted_log_symbol (Real.exp 1) (Real.exp_pos 1).le (1 / 2)
      (by norm_num)
  have h := (envelope_rpow_symbol (5 / 2)).mul hl
  have hp : RadialSymbolBounds 1 3
      (fun x => x ^ ((5 : ℝ) / 2) * materialLogFactor x) := by
    norm_num at h
    exact h
  have hs := (envelope_symbol_weaken (envelope_constant_symbol 1)
    (by norm_num : (0 : ℝ) ≤ 3)).add hp
  have he : ((fun _ : ℝ => (1 : ℝ)) +
      (fun x => x ^ ((5 : ℝ) / 2) * materialLogFactor x)) =
      (fun x => Real.log (materialE0 x)) := by
    funext x
    simp only [Pi.add_apply, materialE0, Real.log_exp, materialE0Exponent]
  exact he ▸ hs

/-- No extra logarithmic-envelope hypothesis is needed: the actual endpoint
formulas and ordinary smoothness already give this global bound. -/
theorem materialE0_log_material_jet_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo D.a D.b,
      |materialDerivativeIterate T n (fun t => Real.log (T.E0 t)) r| ≤ C := by
  have hdata := hT
  obtain ⟨hcont, hpos, _, _, _, _, _, _, _, _, hends, _⟩ := hdata
  obtain ⟨d0, δ, hd0, hδ, _, hL, hR⟩ := hends
  have hlog : ContDiffOn ℝ ∞ (fun r => Real.log (T.E0 r)) (Ioo D.a D.b) :=
    (hcont T.E0 (by simp)).log (fun r hr => (hpos r hr).2.2.1.ne')
  exact materialDerivativeIterate_global_bound_of_endpoint_symbol hd0 hδ
    (hcont T.ell (by simp))
    (fun r hr => (hL r hr).1) (fun r hr => (hR r hr).1)
    hlog materialEndpointLogE0_symbol
    (fun r hr => congrArg Real.log (hL r hr).2.2.1)
    (fun r hr => congrArg Real.log (hR r hr).2.2.1) hn

end ContinuousFlexibility.Statements
