module

public import ContinuousFlexibility.Analysis.ProjectiveNewtonRapidDecay
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Decay of parameter derivatives on inner intervals

Two applications of the real mean-value estimate bound the first derivative
by the size of the curve and its second derivative. A step that decreases
with the smoothing scale converts rapid decay and a coarse growth bound
into rapid decay for the next derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped BigOperators Topology

/-- A forward difference on a closed segment controls the actual derivative
at its left endpoint. -/
theorem norm_deriv_le_of_segment_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f₁ f₂ : ℝ → E} {t h L M : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (h₁ : ∀ s ∈ Icc t (t + h), HasDerivAt f (f₁ s) s)
    (h₂ : ∀ s ∈ Icc t (t + h), HasDerivAt f₁ (f₂ s) s)
    (hbound : ∀ s ∈ Icc t (t + h), ‖f₂ s‖ ≤ M)
    (hleft : ‖f t‖ ≤ L) (hright : ‖f (t + h)‖ ≤ L) :
    ‖f₁ t‖ ≤ 2 * L / h + M * h := by
  have hth : t ≤ t + h := by linarith only [hh]
  have hend : t + h ∈ Icc t (t + h) := ⟨hth, le_rfl⟩
  have hslope (s : ℝ) (hs : s ∈ Icc t (t + h)) : ‖f₁ s - f₁ t‖ ≤ M * h := by
    have hdiff := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u hu => (h₂ u hu).hasDerivWithinAt)
      (fun u hu => hbound u (Ico_subset_Icc_self hu)) s hs
    exact hdiff.trans (mul_le_mul_of_nonneg_left (by linarith only [hs.2]) hM)
  let g := fun s : ℝ => f s - (s - t) • f₁ t
  have hg (s : ℝ) (hs : s ∈ Icc t (t + h)) : HasDerivAt g (f₁ s - f₁ t) s := by
    have hline : HasDerivAt (fun u : ℝ => (u - t) • f₁ t) (f₁ t) s := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id s).sub_const t).smul_const (f₁ t)
    exact (h₁ s hs).sub hline
  have herror : ‖f (t + h) - f t - h • f₁ t‖ ≤ (M * h) * h := by
    have hb := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u hu => (hg u hu).hasDerivWithinAt)
      (fun u hu => hslope u (Ico_subset_Icc_self hu)) (t + h) hend
    have he : g (t + h) - g t = f (t + h) - f t - h • f₁ t := by
      dsimp only [g]
      rw [show t + h - t = h by ring, sub_self, zero_smul, sub_zero]
      abel
    rw [he, show t + h - t = h by ring] at hb
    exact hb
  have hprod : ‖f₁ t‖ * h ≤ 2 * L + (M * h) * h := by
    have he : h • f₁ t = (f (t + h) - f t) - (f (t + h) - f t - h • f₁ t) := by abel
    calc
      _ = ‖h • f₁ t‖ := by rw [norm_smul, Real.norm_of_nonneg hh.le, mul_comm]
      _ = ‖(f (t + h) - f t) - (f (t + h) - f t - h • f₁ t)‖ :=
        congrArg (fun y => ‖y‖) he
      _ ≤ ‖f (t + h) - f t‖ + ‖f (t + h) - f t - h • f₁ t‖ := norm_sub_le _ _
      _ ≤ (L + L) + (M * h) * h :=
        add_le_add ((norm_sub_le _ _).trans (add_le_add hright hleft)) herror
      _ = _ := by ring
  calc
    _ ≤ (2 * L + (M * h) * h) / h := (le_div_iff₀ hh).2 hprod
    _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hh.ne']

/-- Rapid decay of a family and coarse growth of its second derivative
give rapid decay of its first derivative on the buffered inner set. -/
theorem norm_deriv_rapid_of_segment_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f₁ f₂ : ℕ → ℝ → E} {I K : Set ℝ} (N : ℕ → ℕ)
    {η : ℝ} (hη : 0 < η)
    (hbuffer : ∀ t ∈ K, Icc t (t + η) ⊆ I)
    (h₁ : ∀ n t, t ∈ I → HasDerivAt (f n) (f₁ n t) t)
    (h₂ : ∀ n t, t ∈ I → HasDerivAt (f₁ n) (f₂ n t) t)
    (hrapid : ∀ β : ℝ, 0 < β → ∃ L : ℝ, 0 ≤ L ∧
      ∀ n t, t ∈ I → ‖f n t‖ ≤ L * Real.exp (-β * (N n : ℝ)))
    {M γ : ℝ} (hM : 0 ≤ M) (hγ : 0 ≤ γ)
    (hgrowth : ∀ n t, t ∈ I → ‖f₂ n t‖ ≤ M * Real.exp (γ * (N n : ℝ))) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t, t ∈ K → ‖f₁ n t‖ ≤ C * Real.exp (-δ * (N n : ℝ)) := by
  intro δ hδ
  let c := γ + δ + 1
  let β := δ + c
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hβ : 0 < β := add_pos_of_pos_of_nonneg hδ hc
  obtain ⟨L, hL, hLbound⟩ := hrapid β hβ
  refine ⟨2 * L / η + M * η,
    add_nonneg (div_nonneg (mul_nonneg (by norm_num) hL) hη.le) (mul_nonneg hM hη.le), ?_⟩
  intro n t ht
  let h := η * Real.exp (-c * (N n : ℝ))
  have hh : 0 < h := mul_pos hη (Real.exp_pos _)
  have hN : (0 : ℝ) ≤ N n := Nat.cast_nonneg _
  have hexp₁ : Real.exp (-c * (N n : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) hN)
  have hle : h ≤ η := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp₁ hη.le
  have hseg : Icc t (t + h) ⊆ I := by
    intro s hs
    exact hbuffer t ht ⟨hs.1, hs.2.trans (add_le_add le_rfl hle)⟩
  have hth : t ≤ t + h := by linarith only [hh]
  have hleft := hLbound n t (hseg ⟨le_rfl, hth⟩)
  have hright := hLbound n (t + h) (hseg ⟨hth, le_rfl⟩)
  have hderiv := norm_deriv_le_of_segment_bounds hh
    (mul_nonneg hM (Real.exp_pos _).le)
    (fun s hs => h₁ n s (hseg hs)) (fun s hs => h₂ n s (hseg hs))
    (fun s hs => hgrowth n s (hseg hs)) hleft hright
  have hdiv : 2 * (L * Real.exp (-β * (N n : ℝ))) / h =
      (2 * L / η) * Real.exp (-δ * (N n : ℝ)) := by
    dsimp only [h]
    rw [show -β * (N n : ℝ) = -δ * (N n : ℝ) + -c * (N n : ℝ) by dsimp only [β]; ring,
      Real.exp_add]
    field_simp [ne_of_gt hη, Real.exp_ne_zero]
  have hmul : M * Real.exp (γ * (N n : ℝ)) * h =
      (M * η) * Real.exp ((γ - c) * (N n : ℝ)) := by
    calc
      _ = (M * η) * (Real.exp (γ * (N n : ℝ)) * Real.exp (-c * (N n : ℝ))) := by
        dsimp only [h]
        ring
      _ = _ := by rw [← Real.exp_add, show γ * (N n : ℝ) + -c * (N n : ℝ) = (γ - c) * (N n : ℝ) by ring]
  have hγc : γ - c ≤ -δ := by dsimp only [c]; linarith
  calc
    _ ≤ 2 * (L * Real.exp (-β * (N n : ℝ))) / h + M * Real.exp (γ * (N n : ℝ)) * h := hderiv
    _ = (2 * L / η) * Real.exp (-δ * (N n : ℝ)) +
        (M * η) * Real.exp ((γ - c) * (N n : ℝ)) := by rw [hdiv, hmul]
    _ ≤ (2 * L / η) * Real.exp (-δ * (N n : ℝ)) +
        (M * η) * Real.exp (-δ * (N n : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hγc hN)) (mul_nonneg hM hη.le))
    _ = _ := by ring

/-- A genuine derivative tower whose zeroth order decays rapidly and whose
finite orders have coarse exponential bounds decays rapidly at every order
on every closed inner interval. -/
theorem parameter_derivatives_rapid_on_inner_intervals
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ → ℕ) {f : ℕ → ℕ → ℝ → E} {a b : ℝ}
    (hderiv : ∀ k n t, t ∈ Ioo a b → HasDerivAt (f k n) (f (k + 1) n t) t)
    (hzero : ∀ c d, a < c → c ≤ d → d < b → ∀ δ : ℝ, 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t ∈ Icc c d →
        ‖f 0 n t‖ ≤ C * Real.exp (-δ * (N n : ℝ)))
    (hcoarse : ∀ k c d, a < c → c ≤ d → d < b →
      ∃ M γ : ℝ, 0 ≤ M ∧ 0 ≤ γ ∧ ∀ n t, t ∈ Icc c d →
        ‖f k n t‖ ≤ M * Real.exp (γ * (N n : ℝ))) :
    ∀ k c d, a < c → c ≤ d → d < b → ∀ δ : ℝ, 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t ∈ Icc c d →
        ‖f k n t‖ ≤ C * Real.exp (-δ * (N n : ℝ)) := by
  intro k
  induction k with
  | zero => exact hzero
  | succ k ih =>
    intro c d hac hcd hdb
    let d' := (d + b) / 2
    have hdd' : d < d' := by dsimp only [d']; linarith only [hdb]
    have hd'b : d' < b := by dsimp only [d']; linarith only [hdb]
    have hcd' : c ≤ d' := hcd.trans hdd'.le
    have hsub : Icc c d' ⊆ Ioo a b :=
      fun t ht => ⟨hac.trans_le ht.1, ht.2.trans_lt hd'b⟩
    have hbuffer : ∀ t ∈ Icc c d, Icc t (t + (d' - d)) ⊆ Icc c d' := by
      intro t ht s hs
      refine ⟨ht.1.trans hs.1, ?_⟩
      linarith only [ht.2, hs.2]
    obtain ⟨M, γ, hM, hγ, hgrowth⟩ := hcoarse (k + 2) c d' hac hcd' hd'b
    exact norm_deriv_rapid_of_segment_growth N (sub_pos.mpr hdd') hbuffer
      (fun n t ht => hderiv k n t (hsub ht)) (fun n t ht => hderiv (k + 1) n t (hsub ht))
      (ih c d' hac hcd' hd'b) hM hγ hgrowth

/-- A single summable majorant for each derivative order, uniform in the
parameter on the chosen inner set. -/
theorem exists_parameter_derivative_summable_majorants
    {E : Type*} [NormedAddCommGroup E] {f : ℕ → ℕ → ℝ → E}
    {N₀ : ℕ} (hN₀ : 0 < N₀) (K : Set ℝ)
    (hrapid : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t ∈ K →
      ‖f k n t‖ ≤ C * Real.exp (-(1 : ℝ) * (newtonSmoothingIndex N₀ n : ℝ))) :
    ∃ D : ℕ → ℕ → ℝ, (∀ k, Summable (D k)) ∧ (∀ k n, 0 ≤ D k n) ∧
      ∀ k n t, t ∈ K → ‖f k n t‖ ≤ D k n := by
  choose C hC hbound using hrapid
  let D := fun k n => C k * Real.exp (-(1 : ℝ) * (newtonSmoothingIndex N₀ n : ℝ))
  exact ⟨D, fun k => (newton_summable_exponential hN₀ zero_lt_one).mul_left (C k),
    fun k n => mul_nonneg (hC k) (Real.exp_pos _).le, hbound⟩

/-- Summing a family of genuine derivative towers term by term gives a
genuine derivative tower on the whole original open interval. -/
theorem hasDerivAt_tsum_parameter_tower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℕ → ℕ → ℝ → E} {a b : ℝ}
    (hderiv : ∀ k n t, t ∈ Ioo a b → HasDerivAt (f k n) (f (k + 1) n t) t)
    (hmajor : ∀ k c d, a < c → c ≤ d → d < b →
      ∃ D : ℕ → ℝ, Summable D ∧ ∀ n t, t ∈ Icc c d → ‖f k n t‖ ≤ D n)
    (k : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => ∑' n, f k n s) (∑' n, f (k + 1) n t) t := by
  let c := (a + t) / 2
  let d := (t + b) / 2
  have hac : a < c := by dsimp only [c]; linarith only [ht.1]
  have hct : c < t := by dsimp only [c]; linarith only [ht.1]
  have htd : t < d := by dsimp only [d]; linarith only [ht.2]
  have hdb : d < b := by dsimp only [d]; linarith only [ht.2]
  have hcd : c ≤ d := (hct.trans htd).le
  obtain ⟨D₀, hD₀, hf₀⟩ := hmajor k c d hac hcd hdb
  obtain ⟨D₁, hD₁, hf₁⟩ := hmajor (k + 1) c d hac hcd hdb
  have hlim₀ := tendstoUniformlyOn_tsum_nat hD₀ (s := Ioo c d)
    (fun n s hs => hf₀ n s (Ioo_subset_Icc_self hs))
  have hlim₁ := tendstoUniformlyOn_tsum_nat hD₁ (s := Ioo c d)
    (fun n s hs => hf₁ n s (Ioo_subset_Icc_self hs))
  refine hasDerivAt_of_tendstoUniformlyOn
    (f := fun N (x : ℝ) => ∑ n ∈ Finset.range N, f k n x) isOpen_Ioo hlim₁ ?_ ?_ ⟨hct, htd⟩
  · exact Eventually.of_forall fun N s hs =>
      HasDerivAt.fun_sum (fun n _ => hderiv k n s ⟨hac.trans hs.1, hs.2.trans hdb⟩)
  · exact fun s hs => hlim₀.tendsto_at hs

end ContinuousFlexibility.Analysis
