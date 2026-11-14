module

public import ContinuousFlexibility.Analysis.AffineMaterialData
public import ContinuousFlexibility.Radial.RadialSymbolBounds

/-!
# Uniform positive material derivatives of the three logarithms

In the endpoint variable x the material derivative has coefficient
of order minus two and differentiates once. The three logarithms
have order at most three. These estimates concern the actual
iterated derivatives and transfer back to the physical interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Real Set Filter
open ContinuousFlexibility.Analysis
open ContinuousFlexibility.Radial (RadialSymbolBounds)
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem materialRpow_symbol (s : ℝ) :
    RadialSymbolBounds 1 s (fun x : ℝ => x ^ s) := by
  refine ⟨contDiffOn_id.rpow_const_of_ne (fun _ hx => ne_of_gt hx), ?_⟩
  intro n
  refine ⟨‖(descPochhammer ℝ n).eval s‖, norm_nonneg _, ?_⟩
  intro x _ hx
  rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]

private theorem materialSymbol_weaken {s t : ℝ} {f : ℝ → ℝ}
    (hf : RadialSymbolBounds 1 s f) (hst : s ≤ t) : RadialSymbolBounds 1 t f := by
  refine ⟨hf.1, fun n => ?_⟩
  obtain ⟨C, hC, hb⟩ := hf.2 n
  exact ⟨C, hC, fun x hx hx₀ => (hb x hx hx₀).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (sub_le_sub_right hst _)) hC)⟩

private theorem materialConstant_symbol (c : ℝ) :
    RadialSymbolBounds 1 0 (fun _ : ℝ => c) := by
  simpa only [Real.rpow_zero, mul_one] using (materialRpow_symbol 0).const_mul c

private theorem materialDeriv_symbol {s : ℝ} {f : ℝ → ℝ}
    (hf : RadialSymbolBounds 1 s f) : RadialSymbolBounds 1 (s - 1) (deriv f) := by
  refine ⟨hf.1.deriv_of_isOpen isOpen_Ioi (by simp), fun n => ?_⟩
  obtain ⟨C, hC, hb⟩ := hf.2 (n + 1)
  refine ⟨C, hC, fun x hx hx₀ => ?_⟩
  rw [← iteratedDeriv_succ']
  have he : s - 1 - (n : ℝ) = s - ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [he]
  exact hb x hx hx₀

private theorem materialShiftedInverse_symbol (c : ℝ) (hc : 0 ≤ c) :
    RadialSymbolBounds 1 (-1) (fun x : ℝ => (x + c)⁻¹) := by
  have hs : ContDiffOn ℝ ∞ (fun x : ℝ => x + c) (Ioi 0) :=
    contDiffOn_id.add contDiffOn_const
  refine ⟨hs.inv (fun x hx => (add_pos_of_pos_of_nonneg hx hc).ne'), fun n => ?_⟩
  let s : ℝ := -1
  let f : ℝ → ℝ := fun x => x ^ s
  have hF : (fun x : ℝ => (x + c)⁻¹) = (fun x => f (x + c)) := by
    funext x
    exact (Real.rpow_neg_one (x + c)).symm
  obtain ⟨C, hC, hb⟩ := (materialRpow_symbol s).2 n
  refine ⟨C, hC, fun x hx hx₀ => ?_⟩
  rw [hF, iteratedDeriv_comp_add_const]
  have hle : x ≤ x + c := le_add_of_nonneg_right hc
  exact (hb (x + c) (hx.trans hle) (hx₀.trans_le hle)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx₀ hle
        (sub_nonpos.mpr (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (Nat.cast_nonneg _)))) hC)

private theorem materialShiftedLog_symbol (c : ℝ) (hc : 0 ≤ c) (s : ℝ) (hs : 0 < s) :
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
    obtain ⟨C, hC, hb⟩ := (materialShiftedInverse_symbol c hc).2 n
    refine ⟨C, hC, fun x hx hx₀ => ?_⟩
    have he : deriv (fun y : ℝ => Real.log (y + c)) =ᶠ[𝓝 x] (fun y => (y + c)⁻¹) := by
      filter_upwards [Ioi_mem_nhds hx₀] with y hy
      have hd := (((hasDerivAt_id' y).add_const c).log (hpos y hy).ne').deriv
      simpa only [one_div] using hd
    rw [iteratedDeriv_succ', (he.iteratedDeriv n).eq_of_nhds]
    exact (hb x hx hx₀).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by push_cast; linarith)) hC)

/-- The endpoint coefficient in the x variable, before the endpoint sign. -/
def materialEndpointLogCoefficient (x : ℝ) : ℝ := (1 / 2 : ℝ) * (x⁻¹ * (x + 1)⁻¹)

/-- Differentiation in the material coordinate written in the actual endpoint variable. -/
def materialEndpointLogDerivative (sign : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (sign * materialEndpointLogCoefficient x) * deriv f x

private theorem materialEndpointLogCoefficient_symbol :
    RadialSymbolBounds 1 (-2) materialEndpointLogCoefficient := by
  have hx : RadialSymbolBounds 1 (-1) (fun x : ℝ => x⁻¹) := by
    simpa only [Real.rpow_neg_one] using materialRpow_symbol (-1)
  have h := (hx.mul (materialShiftedInverse_symbol 1 zero_le_one)).const_mul (1 / 2)
  norm_num at h
  exact h

theorem materialEndpointLogDerivative_iterate_symbol {f : ℝ → ℝ} {s : ℝ}
    (hf : RadialSymbolBounds 1 s f) (sign : ℝ) (n : ℕ) :
    RadialSymbolBounds 1 (s - 3 * (n : ℝ)) ((materialEndpointLogDerivative sign)^[n] f) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, mul_zero, sub_zero, Function.iterate_zero, id_eq] using hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have he : s - 3 * ((n + 1 : ℕ) : ℝ) = -2 + (s - 3 * (n : ℝ) - 1) := by
      push_cast
      ring
    rw [he]
    exact (materialEndpointLogCoefficient_symbol.const_mul sign).mul (materialDeriv_symbol ih)

/-- The endpoint expression for the log of the physical density scale. -/
def materialEndpointLogEll (d0 x : ℝ) : ℝ := Real.log d0 - x ^ 2 - Real.log (1 + x)

private theorem materialEndpointLogH_symbol :
    RadialSymbolBounds 1 3 (fun x => Real.log (materialH x)) := by
  have h := (materialRpow_symbol 3).const_mul (-2 / 3)
  have he : (fun x => (-2 / 3 : ℝ) * x ^ (3 : ℝ)) = (fun x => Real.log (materialH x)) := by
    funext x
    change (-2 / 3 : ℝ) * x ^ ((3 : ℕ) : ℝ) = Real.log (materialH x)
    rw [Real.rpow_natCast, materialH, Real.log_exp]
    ring
  exact he ▸ h

private theorem materialEndpointLogM_symbol :
    RadialSymbolBounds 1 3 (fun x => Real.log (materialM x)) := by
  have hl : RadialSymbolBounds 1 (1 / 4) materialLogFactor := by
    have hlog : (fun x : ℝ => Real.log (x + Real.exp 1)) = materialLogFactor := by
      funext x
      change Real.log (x + Real.exp 1) = Real.log (Real.exp 1 + x)
      rw [add_comm x]
    rw [← hlog]
    exact materialShiftedLog_symbol (Real.exp 1) (Real.exp_pos 1).le (1 / 4) (by norm_num)
  have h := (materialRpow_symbol (5 / 2)).mul (hl.mul hl)
  have h₃ : RadialSymbolBounds 1 3
      (fun x => x ^ ((5 : ℝ) / 2) * (materialLogFactor x * materialLogFactor x)) := by
    norm_num at h
    exact h
  have hsum := (materialSymbol_weaken (materialConstant_symbol 1) (by norm_num : (0 : ℝ) ≤ 3)).add h₃
  have he :
      ((fun _ : ℝ => (1 : ℝ)) +
        (fun x => x ^ ((5 : ℝ) / 2) * (materialLogFactor x * materialLogFactor x))) =
      (fun x => Real.log (materialM x)) := by
    funext x
    simp only [Pi.add_apply, materialM, Real.log_exp, materialMExponent, pow_two]
  exact he ▸ hsum

private theorem materialEndpointLogEll_symbol (d0 : ℝ) :
    RadialSymbolBounds 1 3 (materialEndpointLogEll d0) := by
  have hp : RadialSymbolBounds 1 3 (fun x : ℝ => x ^ (2 : ℕ)) := by
    have h := materialSymbol_weaken (materialRpow_symbol 2) (by norm_num : (2 : ℝ) ≤ 3)
    simpa only [Real.rpow_two] using h
  have hl : RadialSymbolBounds 1 3 (fun x : ℝ => Real.log (1 + x)) := by
    simpa only [add_comm] using materialShiftedLog_symbol 1 zero_le_one 3 (by norm_num)
  exact ((materialSymbol_weaken (materialConstant_symbol (Real.log d0))
    (by norm_num : (0 : ℝ) ≤ 3)).sub hp).sub hl

private theorem materialEndpointLogIterate_bound {f : ℝ → ℝ}
    (hf : RadialSymbolBounds 1 3 f) (sign : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ (1 : ℝ),
      |((materialEndpointLogDerivative sign)^[n] f) x| ≤ C := by
  obtain ⟨C, hC, hb⟩ := (materialEndpointLogDerivative_iterate_symbol hf sign n).2 0
  refine ⟨C, hC, fun x hx => ?_⟩
  have hx₀ := zero_lt_one.trans_le hx
  have hn₁ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hn : 1 ≤ n)
  have hle : x ^ (3 - 3 * (n : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hx (show 3 - 3 * (n : ℝ) ≤ 0 by linarith)
  have h := hb x hx hx₀
  rw [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right hC hle)

private theorem endpointX_scaled_derivative {T : MaterialData} {d : ℝ → ℝ}
    {d0 η r : ℝ} (hd0 : 0 < d0) (hd : HasDerivAt d η r)
    (hdpos : 0 < d r) (hdlt : d r < d0)
    (hEll : T.ell r = endpointEll d0 (d r)) :
    ∃ dx : ℝ, HasDerivAt (fun t => endpointX d0 (d t)) dx r ∧
      T.ell r * dx = (-η) * materialEndpointLogCoefficient (endpointX d0 (d r)) := by
  have hX := hasDerivAt_endpointX hd0 hdpos hdlt
  refine ⟨_, hX.comp r hd, ?_⟩
  have hp := endpointX_pos hdpos hdlt
  rw [hEll, endpointEll, materialEndpointLogCoefficient]
  field_simp [hdpos.ne', hp.ne', (by linarith : 1 + endpointX d0 (d r) ≠ 0),
    (by linarith : endpointX d0 (d r) + 1 ≠ 0)]
  ring

private theorem materialDerivativeIterate_eqOn_endpoint {T : MaterialData} {U : Set ℝ}
    {d f g : ℝ → ℝ} {d0 η : ℝ}
    (hU : IsOpen U) (hd0 : 0 < d0)
    (hd : ∀ r ∈ U, HasDerivAt d η r) (hdist : ∀ r ∈ U, 0 < d r ∧ d r < d0)
    (hEll : ∀ r ∈ U, T.ell r = endpointEll d0 (d r))
    (hf : RadialSymbolBounds 1 3 f)
    (hfg : EqOn g (fun r => f (endpointX d0 (d r))) U) (n : ℕ) :
    EqOn (materialDerivativeIterate T n g)
      (fun r => ((materialEndpointLogDerivative (-η))^[n] f) (endpointX d0 (d r))) U := by
  induction n with
  | zero => exact hfg
  | succ n ih =>
    intro r hr
    let F := (materialEndpointLogDerivative (-η))^[n] f
    have hp := endpointX_pos (hdist r hr).1 (hdist r hr).2
    have hFd : DifferentiableAt ℝ F (endpointX d0 (d r)) :=
      ((materialEndpointLogDerivative_iterate_symbol hf (-η) n).contDiffAt hp).differentiableAt
        (by simp)
    obtain ⟨dx, hX, hdx⟩ := endpointX_scaled_derivative hd0 (hd r hr)
      (hdist r hr).1 (hdist r hr).2 (hEll r hr)
    have he : materialDerivativeIterate T n g =ᶠ[𝓝 r]
        (fun t => F (endpointX d0 (d t))) := by
      filter_upwards [hU.mem_nhds hr] with t ht
      exact ih ht
    have hdF : HasDerivAt (fun t => F (endpointX d0 (d t)))
        (deriv F (endpointX d0 (d r)) * dx) r :=
      hFd.hasDerivAt.comp r hX
    change ((materialDerivative T)^[n + 1] g) r =
      ((materialEndpointLogDerivative (-η))^[n + 1] f) (endpointX d0 (d r))
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change T.ell r * deriv (materialDerivativeIterate T n g) r =
      (-η * materialEndpointLogCoefficient (endpointX d0 (d r))) * deriv F (endpointX d0 (d r))
    rw [he.deriv_eq, hdF.deriv, ← hdx]
    ring

private theorem endpointX_ge_one {d0 d : ℝ} (hd : 0 < d)
    (hsmall : d < d0 * Real.exp (-1)) : 1 ≤ endpointX d0 d := by
  have hratio : Real.exp 1 < d0 / d := by
    apply (lt_div_iff₀ hd).mpr
    calc
      Real.exp 1 * d < Real.exp 1 * (d0 * Real.exp (-1)) :=
        mul_lt_mul_of_pos_left hsmall (Real.exp_pos _)
      _ = d0 := by
        rw [Real.exp_neg, mul_left_comm (Real.exp 1) d0, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
  have hlog : 1 < Real.log (d0 / d) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hratio
  exact le_of_lt ((Real.lt_sqrt zero_le_one).mpr (by simpa only [one_pow] using hlog))

private theorem materialDerivativeIterate_endpoint_bound {T : MaterialData} {U : Set ℝ}
    {d f g : ℝ → ℝ} {d0 η : ℝ}
    (hU : IsOpen U) (hd0 : 0 < d0) (hd : ∀ r ∈ U, HasDerivAt d η r)
    (hdist : ∀ r ∈ U, 0 < d r ∧ d r < d0 * Real.exp (-1))
    (hEll : ∀ r ∈ U, T.ell r = endpointEll d0 (d r))
    (hf : RadialSymbolBounds 1 3 f)
    (hfg : EqOn g (fun r => f (endpointX d0 (d r))) U) {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ U, |materialDerivativeIterate T n g r| ≤ C := by
  have hdist' (r : ℝ) (hr : r ∈ U) : 0 < d r ∧ d r < d0 := by
    exact ⟨(hdist r hr).1, (hdist r hr).2.trans_le
      (mul_le_of_le_one_right hd0.le (Real.exp_le_one_iff.mpr (by norm_num)))⟩
  have he := materialDerivativeIterate_eqOn_endpoint hU hd0 hd hdist' hEll hf hfg n
  obtain ⟨C, hC, hb⟩ := materialEndpointLogIterate_bound hf (-η) hn
  refine ⟨C, hC, fun r hr => ?_⟩
  rw [he hr]
  exact hb _ (endpointX_ge_one (hdist r hr).1 (hdist r hr).2)

private theorem log_endpointEll_eq {d0 d : ℝ} (hd0 : 0 < d0) (hd : 0 < d) (hlt : d < d0) :
    Real.log (endpointEll d0 d) = materialEndpointLogEll d0 (endpointX d0 d) := by
  have hp := endpointX_pos hd hlt
  have hlog := congrArg Real.log (endpointDistance_endpointX hd0 hd hlt)
  change Real.log (d0 * Real.exp (-(endpointX d0 d ^ 2))) = Real.log d at hlog
  rw [Real.log_mul hd0.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [endpointEll, Real.log_div hd.ne' (by linarith : 1 + endpointX d0 d ≠ 0),
    materialEndpointLogEll]
  linarith only [hlog]

private theorem contDiffOn_materialDerivativeIterate {T : MaterialData} {U : Set ℝ}
    (hU : IsOpen U) (hEll : ContDiffOn ℝ ∞ T.ell U) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) (n : ℕ) :
    ContDiffOn ℝ ∞ (materialDerivativeIterate T n g) U := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [materialDerivativeIterate, Function.iterate_succ_apply']
    exact hEll.mul (ih.deriv_of_isOpen hU (by simp))

private theorem affineMaterial_logJet_bound {D : ReferenceData} {T : MaterialData}
    {d0 δ : ℝ} (hd0 : 0 < d0) (hδ : 0 < δ)
    (hEll : ContDiffOn ℝ ∞ T.ell (Ioo D.a D.b))
    (hEllL : ∀ r ∈ Ioo D.a (D.a + δ), T.ell r = endpointEll d0 (r - D.a))
    (hEllR : ∀ r ∈ Ioo (D.b - δ) D.b, T.ell r = endpointEll d0 (D.b - r))
    {g f : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioo D.a D.b))
    (hf : RadialSymbolBounds 1 3 f)
    (hL : ∀ r ∈ Ioo D.a (D.a + δ), g r = f (endpointX d0 (r - D.a)))
    (hR : ∀ r ∈ Ioo (D.b - δ) D.b, g r = f (endpointX d0 (D.b - r)))
    {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo D.a D.b, |materialDerivativeIterate T n g r| ≤ C := by
  let e := min δ (d0 * Real.exp (-1))
  have he : 0 < e := lt_min hδ (mul_pos hd0 (Real.exp_pos _))
  have heδ : e ≤ δ := min_le_left _ _
  have he₀ : e ≤ d0 * Real.exp (-1) := min_le_right _ _
  have hsubL : Ioo D.a (D.a + e) ⊆ Ioo D.a (D.a + δ) :=
    fun _ hr => ⟨hr.1, hr.2.trans_le (by linarith only [heδ])⟩
  have hsubR : Ioo (D.b - e) D.b ⊆ Ioo (D.b - δ) D.b :=
    fun _ hr => ⟨(sub_le_sub_left heδ _).trans_lt hr.1, hr.2⟩
  obtain ⟨CL, hCL, hbL⟩ := materialDerivativeIterate_endpoint_bound
    (d := fun r => r - D.a) (η := 1) isOpen_Ioo hd0
    (fun r _ => (hasDerivAt_id' r).sub_const D.a)
    (fun r (hr : r ∈ Ioo D.a (D.a + e)) =>
      ⟨sub_pos.mpr hr.1, (show r - D.a < e by linarith [hr.2]).trans_le he₀⟩)
    (fun r hr => hEllL r (hsubL hr)) hf (fun r hr => hL r (hsubL hr)) hn
  obtain ⟨CR, hCR, hbR⟩ := materialDerivativeIterate_endpoint_bound
    (d := fun r => D.b - r) (η := -1) isOpen_Ioo hd0
    (fun r _ => (hasDerivAt_id' r).const_sub D.b)
    (fun r (hr : r ∈ Ioo (D.b - e) D.b) =>
      ⟨sub_pos.mpr hr.2, (show D.b - r < e by linarith [hr.1]).trans_le he₀⟩)
    (fun r hr => hEllR r (hsubR hr)) hf (fun r hr => hR r (hsubR hr)) hn
  have hsub : Icc (D.a + e) (D.b - e) ⊆ Ioo D.a D.b :=
    fun _ hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hc := (contDiffOn_materialDerivativeIterate isOpen_Ioo hEll hg n).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hc.abs.mono hsub)
  refine ⟨CL + CR + max 0 C, by positivity, fun r hr => ?_⟩
  by_cases hleft : r < D.a + e
  · exact (hbL r ⟨hr.1, hleft⟩).trans (by linarith [le_max_left (0 : ℝ) C])
  by_cases hright : D.b - e < r
  · exact (hbR r ⟨hright, hr.2⟩).trans (by linarith [le_max_left (0 : ℝ) C])
  exact (hC ⟨r, ⟨le_of_not_gt hleft, le_of_not_gt hright⟩, rfl⟩).trans
    (by linarith [le_max_right (0 : ℝ) C])

/-- All positive material derivatives of the actual three affine-model
logarithms are bounded on the whole physical interval. -/
theorem logarithmicDerivativeBounds_affineMaterialData {D : ReferenceData}
    {sample : ℕ → ℝ} (hab : D.a < D.b) :
    logarithmicDerivativeBounds D (affineMaterialData D sample) := by
  let T := affineMaterialData D sample
  have hdata := affineMaterialData_endpoint_formulas (sample := sample) hab
  obtain ⟨d0, δ, hd0, hδ, hδlt, hL, hR⟩ := hdata
  have hs := affineMaterialData_smooth_scalar (sample := sample) hab
  have hp (r : ℝ) (hr : r ∈ Ioo D.a D.b) := affineMaterialData_positive (sample := sample) hab hr
  have hell : ContDiffOn ℝ ∞ T.ell (Ioo D.a D.b) := hs _ (by simp [T])
  have hH : ContDiffOn ℝ ∞ T.H (Ioo D.a D.b) := hs _ (by simp [T])
  have hM : ContDiffOn ℝ ∞ T.M (Ioo D.a D.b) := hs _ (by simp [T])
  have hh : ContDiffOn ℝ ∞ (fun r => Real.log (T.H r)) (Ioo D.a D.b) :=
    hH.log (fun r hr => (hp r hr).2.1.ne')
  have hm : ContDiffOn ℝ ∞ (fun r => Real.log (T.M r)) (Ioo D.a D.b) :=
    hM.log (fun r hr => (zero_lt_one.trans_le (hp r hr).2.2.2).ne')
  have hlogell : ContDiffOn ℝ ∞ (fun r => Real.log (T.ell r)) (Ioo D.a D.b) :=
    hell.log (fun r hr => (hp r hr).1.ne')
  have hellL (r : ℝ) (hr : r ∈ Ioo D.a (D.a + δ)) :
      T.ell r = endpointEll d0 (r - D.a) := (hL r hr).1
  have hellR (r : ℝ) (hr : r ∈ Ioo (D.b - δ) D.b) :
      T.ell r = endpointEll d0 (D.b - r) := (hR r hr).1
  have hδ₀ : δ < d0 := hδlt.trans_le (min_le_left _ _)
  intro n hn
  obtain ⟨CH, hCH, hbH⟩ := affineMaterial_logJet_bound hd0 hδ hell hellL hellR hh
    materialEndpointLogH_symbol
    (fun r hr => congrArg Real.log (hL r hr).2.1)
    (fun r hr => congrArg Real.log (hR r hr).2.1) hn
  obtain ⟨CM, hCM, hbM⟩ := affineMaterial_logJet_bound hd0 hδ hell hellL hellR hm
    materialEndpointLogM_symbol
    (fun r hr => congrArg Real.log (hL r hr).2.2.2)
    (fun r hr => congrArg Real.log (hR r hr).2.2.2) hn
  obtain ⟨CE, hCE, hbE⟩ := affineMaterial_logJet_bound hd0 hδ hell hellL hellR hlogell
    (materialEndpointLogEll_symbol d0)
    (fun r hr => (congrArg Real.log (hellL r hr)).trans
      (log_endpointEll_eq hd0 (sub_pos.mpr hr.1) (by linarith [hr.2])))
    (fun r hr => (congrArg Real.log (hellR r hr)).trans
      (log_endpointEll_eq hd0 (sub_pos.mpr hr.2) (by linarith [hr.1]))) hn
  refine ⟨CH + CM + CE, by positivity, fun r hr => ?_⟩
  exact ⟨(hbH r hr).trans (by linarith), (hbM r hr).trans (by linarith),
    (hbE r hr).trans (by linarith)⟩

end ContinuousFlexibility.Statements
