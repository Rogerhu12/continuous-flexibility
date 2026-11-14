import ContinuousFlexibility.Analysis.MaterialLogJets

/-!
# Endpoint symbols and global material derivatives

This shared endpoint-to-global argument uses the actual endpoint expression
for ell and the existing endpoint material differentiation operator. It does
not specialize to H or M and does not change the installed logarithm proofs.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Real Set Filter
open ContinuousFlexibility.Analysis
open ContinuousFlexibility.Radial (RadialSymbolBounds)
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem endpointGlobal_iterate_bound {f : ℝ → ℝ}
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

private theorem endpointGlobal_scaled_derivative {T : MaterialData} {d : ℝ → ℝ}
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

private theorem endpointGlobal_iterate_eqOn {T : MaterialData} {U : Set ℝ}
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
    obtain ⟨dx, hX, hdx⟩ := endpointGlobal_scaled_derivative hd0 (hd r hr)
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

private theorem endpointGlobal_x_ge_one {d0 d : ℝ} (hd : 0 < d)
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

private theorem endpointGlobal_tail_bound {T : MaterialData} {U : Set ℝ}
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
  have he := endpointGlobal_iterate_eqOn hU hd0 hd hdist' hEll hf hfg n
  obtain ⟨C, hC, hb⟩ := endpointGlobal_iterate_bound hf (-η) hn
  refine ⟨C, hC, fun r hr => ?_⟩
  rw [he hr]
  exact hb _ (endpointGlobal_x_ge_one (hdist r hr).1 (hdist r hr).2)

private theorem endpointGlobal_iterate_contDiffOn {T : MaterialData} {U : Set ℝ}
    (hU : IsOpen U) (hEll : ContDiffOn ℝ ∞ T.ell U) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) (n : ℕ) :
    ContDiffOn ℝ ∞ (materialDerivativeIterate T n g) U := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [materialDerivativeIterate, Function.iterate_succ_apply']
    exact hEll.mul (ih.deriv_of_isOpen hU (by simp))

/-- A single endpoint symbol and ordinary smoothness on the middle interval
give global bounds for every positive material derivative. The weight g
is arbitrary: no height, material-envelope, or sample bound is assumed. -/
theorem materialDerivativeIterate_global_bound_of_endpoint_symbol {D : ReferenceData} {T : MaterialData}
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
  obtain ⟨CL, hCL, hbL⟩ := endpointGlobal_tail_bound
    (d := fun r => r - D.a) (η := 1) isOpen_Ioo hd0
    (fun r _ => (hasDerivAt_id' r).sub_const D.a)
    (fun r (hr : r ∈ Ioo D.a (D.a + e)) =>
      ⟨sub_pos.mpr hr.1, (show r - D.a < e by linarith [hr.2]).trans_le he₀⟩)
    (fun r hr => hEllL r (hsubL hr)) hf (fun r hr => hL r (hsubL hr)) hn
  obtain ⟨CR, hCR, hbR⟩ := endpointGlobal_tail_bound
    (d := fun r => D.b - r) (η := -1) isOpen_Ioo hd0
    (fun r _ => (hasDerivAt_id' r).const_sub D.b)
    (fun r (hr : r ∈ Ioo (D.b - e) D.b) =>
      ⟨sub_pos.mpr hr.2, (show D.b - r < e by linarith [hr.1]).trans_le he₀⟩)
    (fun r hr => hEllR r (hsubR hr)) hf (fun r hr => hR r (hsubR hr)) hn
  have hsub : Icc (D.a + e) (D.b - e) ⊆ Ioo D.a D.b :=
    fun _ hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hc := (endpointGlobal_iterate_contDiffOn isOpen_Ioo hEll hg n).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hc.abs.mono hsub)
  refine ⟨CL + CR + max 0 C, by positivity, fun r hr => ?_⟩
  by_cases hleft : r < D.a + e
  · exact (hbL r ⟨hr.1, hleft⟩).trans (by linarith [le_max_left (0 : ℝ) C])
  by_cases hright : D.b - e < r
  · exact (hbR r ⟨hright, hr.2⟩).trans (by linarith [le_max_left (0 : ℝ) C])
  exact (hC ⟨r, ⟨le_of_not_gt hleft, le_of_not_gt hright⟩, rfl⟩).trans
    (by linarith [le_max_right (0 : ℝ) C])

end ContinuousFlexibility.Statements
