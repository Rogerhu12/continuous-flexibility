import ContinuousFlexibility.Analysis.MaterialOrdinaryJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform ordinary jets of the material radius

The endpoint formula bounds the positive material length scale globally.
Its bounded logarithmic material jets then bound every ordinary derivative
after composition with the radius. Consequently all jets of the radius
are bounded, and composing a scalar function with this actual coordinate
costs only a constant at each fixed derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n02n03_materialEll_bounded {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b, |T.ell r| ≤ K := by
  obtain ⟨hsmooth, hpos, _, _, _, _, _, _, _, _, hend, _⟩ := hT
  obtain ⟨d₀, δ, _, hδ, _, hleft, hright⟩ := hend
  have hcore : Icc (D.a + δ) (D.b - δ) ⊆ Ioo D.a D.b := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  have hc : ContinuousOn T.ell (Icc (D.a + δ) (D.b - δ)) :=
    (hsmooth T.ell (by simp)).continuousOn.mono hcore
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max (max A δ) 0, le_max_right _ _, fun r hr => ?_⟩
  have hell : 0 < T.ell r := (hpos r hr).1
  rw [abs_of_pos hell]
  by_cases hl : r < D.a + δ
  · rw [(hleft r ⟨hr.1, hl⟩).1]
    have hx : 0 ≤ ContinuousFlexibility.Analysis.endpointX d₀ (r - D.a) :=
      Real.sqrt_nonneg _
    apply (div_le_self (sub_nonneg.mpr hr.1.le) (by linarith :
      1 ≤ 1 + ContinuousFlexibility.Analysis.endpointX d₀ (r - D.a))).trans
    exact (show r - D.a ≤ δ by linarith).trans
      ((le_max_right A δ).trans (le_max_left _ _))
  · by_cases hr' : D.b - δ < r
    · rw [(hright r ⟨hr', hr.2⟩).1]
      have hx : 0 ≤ ContinuousFlexibility.Analysis.endpointX d₀ (D.b - r) :=
        Real.sqrt_nonneg _
      apply (div_le_self (sub_nonneg.mpr hr.2.le) (by linarith :
        1 ≤ 1 + ContinuousFlexibility.Analysis.endpointX d₀ (D.b - r))).trans
      exact (show D.b - r ≤ δ by linarith).trans
        ((le_max_right A δ).trans (le_max_left _ _))
    · have hb := hA r ⟨le_of_not_gt hl, le_of_not_gt hr'⟩
      have hb' : T.ell r ≤ A := by
        simpa only [Real.norm_eq_abs, abs_of_pos hell] using hb
      exact hb'.trans ((le_max_left A δ).trans (le_max_left _ _))

theorem materialRadius_comp_contDiff {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b)) :
    ContDiff ℝ ∞ (fun x => f (T.radius x)) := by
  obtain ⟨_, _, _, _, _, _, hradius, hinside, _⟩ := hT
  exact hf.comp_contDiff hradius (fun x => (hinside x).1)

theorem materialEll_radius_iteratedDeriv_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
      |iteratedDeriv n (fun t => T.ell (T.radius t)) x| ≤ K := by
  have hdata := hT
  obtain ⟨hsmooth, hpos, _, _, _, _, _, hinside, _, _, _, _, _, hlog, _⟩ := hdata
  have hp (x : ℝ) : 0 < T.ell (T.radius x) := (hpos _ (hinside x).1).1
  have hlogell : ContDiffOn ℝ ∞ (fun r => Real.log (T.ell r)) (Ioo D.a D.b) :=
    (hsmooth T.ell (by simp)).log (fun r hr => (hpos r hr).1.ne')
  have hL : ContDiff ℝ ∞ (fun x => Real.log (T.ell (T.radius x))) :=
    materialRadius_comp_contDiff hT hlogell
  have hLb (k : ℕ) (hk : 0 < k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        |iteratedDeriv k (fun t => Real.log (T.ell (T.radius t))) x| ≤ C := by
    obtain ⟨C, hC, hb⟩ := hlog k hk
    refine ⟨C, hC, fun x => ?_⟩
    rw [iteratedDeriv_comp_materialRadius hT hlogell]
    exact (hb (T.radius x) (hinside x).1).2.2
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_exp_majorant hL hLb n
  obtain ⟨A, hA, hAb⟩ := n02n03_materialEll_bounded hT
  have heq : (fun t => T.ell (T.radius t)) =
      (fun t => Real.exp (Real.log (T.ell (T.radius t)))) :=
    funext (fun t => (Real.exp_log (hp t)).symm)
  refine ⟨C * A, mul_nonneg hC hA, fun x => ?_⟩
  rw [heq]
  apply (hb x).trans
  rw [Real.exp_log (hp x)]
  apply mul_le_mul_of_nonneg_left _ hC
  simpa only [abs_of_pos (hp x)] using hAb (T.radius x) (hinside x).1

/-- Every ordinary jet of the supplied inverse material coordinate is bounded. -/
theorem materialRadius_iteratedDeriv_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |iteratedDeriv n T.radius x| ≤ K := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, hinside, _, hderiv, _⟩ := hdata
  cases n with
  | zero =>
    refine ⟨|D.a| + |D.b|, add_nonneg (abs_nonneg _) (abs_nonneg _), fun x => ?_⟩
    simp only [iteratedDeriv_zero]
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le D.a
      have ha := (hinside x).1.1
      linarith [abs_nonneg D.b]
    · have h := le_abs_self D.b
      have hb := (hinside x).1.2
      linarith [abs_nonneg D.a]
  | succ n =>
    obtain ⟨K, hK, hb⟩ := materialEll_radius_iteratedDeriv_bounded hT n
    refine ⟨K, hK, fun x => ?_⟩
    have hd : deriv T.radius = fun t => T.ell (T.radius t) :=
      funext (fun t => (hderiv t).deriv)
    rw [iteratedDeriv_succ', hd]
    exact hb x

/-- Uniform bounds for finitely many scalar jets give an actual composition
bound, with a constant depending only on the material coordinate and order. -/
theorem iteratedDeriv_comp_materialRadius_le
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
      ∀ K : ℝ, 0 ≤ K →
      (∀ i : ℕ, i ≤ n → ∀ r : ℝ, |iteratedDeriv i f r| ≤ K) →
      ∀ x : ℝ, |iteratedDeriv n (fun t => f (T.radius t)) x| ≤ C * K := by
  classical
  have hjet (i : Fin (n + 1)) := materialRadius_iteratedDeriv_bounded hT i.val
  choose B hB hBb using hjet
  let Q : ℝ := 1 + ∑ i : Fin (n + 1), B i
  have hQ : 1 ≤ Q := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
  refine ⟨(n.factorial : ℝ) * Q ^ n,
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hQ₀ n), ?_⟩
  intro f hf K hK hfB x
  have houter (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (T.radius x)‖ ≤ K := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      hfB i hi (T.radius x)
  have hinner (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i T.radius x‖ ≤ Q ^ i := by
    let j : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hin⟩
    have hsum : B j ≤ ∑ k : Fin (n + 1), B k :=
      Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ j)
    have hb : |iteratedDeriv i T.radius x| ≤ Q :=
      (hBb j x).trans (hsum.trans (by dsimp only [Q]; linarith))
    have hpow : Q ≤ Q ^ i := by simpa only [pow_one] using pow_le_pow_right₀ hQ hi
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb.trans hpow
  have h := norm_iteratedFDeriv_comp_le hf hT.2.2.2.2.2.2.1
    (n := n) (by simp) x houter hinner
  have h' : |iteratedDeriv n (fun t => f (T.radius t)) x| ≤
      (n.factorial : ℝ) * K * Q ^ n := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      Function.comp_def] using h
  exact h'.trans_eq (by ring)

end ContinuousFlexibility.Statements
