module

public import ContinuousFlexibility.Scalar.WeightedMaterialScale
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Bounded jets of the actual material radius

The two endpoint formulas and compactness of the middle interval bound the
material scale. Its bounded logarithmic jets then bound every ordinary jet
of the actual radius. Consequently composition with that radius preserves
arbitrarily small material-envelope growth.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData}

private theorem materialEndpointScale_le_distance (d0 : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    d / (1 + ContinuousFlexibility.Analysis.endpointX d0 d) ≤ d := by
  have hx : 0 ≤ ContinuousFlexibility.Analysis.endpointX d0 d :=
    Real.sqrt_nonneg _
  apply (div_le_iff₀ (by linarith : 0 <
    1 + ContinuousFlexibility.Analysis.endpointX d0 d)).2
  nlinarith only [mul_nonneg hd hx]

/-- The actual scale is bounded on the full physical interval, including
both endpoint collars through the same estimate. -/
theorem materialEll_bounded (hT : IsMaterialData D T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo D.a D.b, |T.ell r| ≤ C := by
  obtain ⟨hsmooth, hpos, _, _, _, _, _, _, _, _, hend, _⟩ := hT
  obtain ⟨d0, δ, _, hδ, _, hleft, hright⟩ := hend
  have hsub : Icc (D.a + δ) (D.b - δ) ⊆ Ioo D.a D.b := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (D.a + δ) (D.b - δ))).bddAbove_image
    (((hsmooth T.ell (by simp)).continuousOn.abs).mono hsub)
  let C : ℝ := max δ (max B 0)
  have hδC : δ ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left B 0).trans (le_max_right δ (max B 0))
  refine ⟨C, hδ.le.trans hδC, fun r hr => ?_⟩
  by_cases hl : r < D.a + δ
  · rw [abs_of_pos (hpos r hr).1, (hleft r ⟨hr.1, hl⟩).1]
    exact (materialEndpointScale_le_distance d0 (sub_pos.mpr hr.1).le).trans
      ((by linarith only [hl] : r - D.a ≤ δ).trans hδC)
  by_cases hr' : D.b - δ < r
  · rw [abs_of_pos (hpos r hr).1, (hright r ⟨hr', hr.2⟩).1]
    exact (materialEndpointScale_le_distance d0 (sub_pos.mpr hr.2).le).trans
      ((by linarith only [hr'] : D.b - r ≤ δ).trans hδC)
  exact (hB ⟨r, ⟨le_of_not_gt hl, le_of_not_gt hr'⟩, rfl⟩).trans hBC

/-- Every actual material-coordinate jet of the scale is globally bounded. -/
theorem iteratedDeriv_materialEll_bounded (hT : IsMaterialData D T) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => T.ell (T.radius t)) x| ≤ C := by
  have hell : ContDiffOn ℝ ∞ T.ell (Ioo D.a D.b) := hT.1 T.ell (by simp)
  have hpos : ∀ r ∈ Ioo D.a D.b, 0 < T.ell r := fun r hr => (hT.2.1 r hr).1
  have hinside := hT.2.2.2.2.2.2.2.1
  let L : ℝ → ℝ := fun x => Real.log (T.ell (T.radius x))
  have hL : ContDiff ℝ ∞ L := contDiff_materialLog_pullback hT hell hpos
  have hLb (k : ℕ) (hk : 0 < k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv k L x| ≤ C := by
    obtain ⟨C, hC, hb⟩ := iteratedDeriv_materialLogs_bound hT k hk
    exact ⟨C, hC, fun x => (hb x).2.2⟩
  obtain ⟨A, hA, hAb⟩ := iteratedDeriv_exp_majorant hL hLb n
  obtain ⟨B, hB, hBb⟩ := materialEll_bounded hT
  have heq : (fun x => Real.exp (L x)) = fun x => T.ell (T.radius x) := by
    funext x
    exact Real.exp_log (hpos _ (hinside x).1)
  refine ⟨A * B, mul_nonneg hA hB, fun x => ?_⟩
  have hx := hAb x
  rw [heq, congrFun heq x] at hx
  exact hx.trans (mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (hBb _ (hinside x).1)) hA)

/-- The radius itself and every one of its ordinary derivatives are bounded. -/
theorem iteratedDeriv_materialRadius_bounded (hT : IsMaterialData D T) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n T.radius x| ≤ C := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, hinside, _, hderiv, _⟩ := hdata
  cases n with
  | zero =>
    refine ⟨|D.a| + |D.b|, add_nonneg (abs_nonneg _) (abs_nonneg _), fun x => ?_⟩
    rw [iteratedDeriv_zero]
    apply abs_le.mpr
    have hx := (hinside x).1
    constructor
    · linarith only [hx.1, neg_abs_le D.a, abs_nonneg D.b]
    · linarith only [hx.2, le_abs_self D.b, abs_nonneg D.a]
  | succ n =>
    have hd : deriv T.radius = fun x => T.ell (T.radius x) := by
      funext x
      exact (hderiv x).deriv
    rw [iteratedDeriv_succ', hd]
    exact iteratedDeriv_materialEll_bounded hT n

/-- Passing from physical radius to the actual material coordinate does not
increase a subpower exponent. The composition estimate uses smoothness only
on the physical interval. -/
theorem materialSubpower_comp_radius (hT : IsMaterialData D T) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b))
    (hb : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo D.a D.b,
        |iteratedDeriv n f r| ≤ C * T.M r ^ ε) :
    MaterialSubpower T (fun x => f (T.radius x)) := by
  classical
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, hradius, hinside, _⟩ := hdata
  refine ⟨hf.comp_contDiff hradius (fun x => (hinside x).1), fun n ε hε => ?_⟩
  have houter (i : Fin (n + 1)) := hb i.val ε hε
  have hinner (i : Fin (n + 1)) := iteratedDeriv_materialRadius_bounded hT i.val
  choose A hA hAb using houter
  choose B hB hBb using hinner
  let K : ℝ := ∑ i : Fin (n + 1), A i
  let L : ℝ := 1 + ∑ i : Fin (n + 1), B i
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i _ => hA i)
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith only [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      hB i)]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLpow (i : ℕ) (hi : 1 ≤ i) : L ≤ L ^ i := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    calc
      L = 1 * L := (one_mul _).symm
      _ ≤ L ^ j * L := mul_le_mul_of_nonneg_right (one_le_pow₀ hL) hL0
      _ = L ^ (j + 1) := (pow_succ _ _).symm
  refine ⟨(n.factorial : ℝ) * K * L ^ n,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK) (pow_nonneg hL0 _), fun x => ?_⟩
  have hr := (hinside x).1
  have hM : 0 ≤ T.M (T.radius x) ^ ε :=
    Real.rpow_nonneg (zero_le_one.trans (hpos _ hr).2.2.2) _
  have hout (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i f (Ioo D.a D.b) (T.radius x)‖ ≤
        K * T.M (T.radius x) ^ ε := by
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_of_isOpen isOpen_Ioo hr, Real.norm_eq_abs]
    let j : Fin (n + 1) := ⟨i, by omega⟩
    exact (hAb j _ hr).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ j)) hM)
  have hin (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i T.radius x‖ ≤ L ^ i := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    let j : Fin (n + 1) := ⟨i, by omega⟩
    have hj : B j ≤ L := by
      have hs := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ j)
      dsimp only [L]
      linarith only [hs]
    exact (hBb j x).trans (hj.trans (hLpow i hi))
  have hcomp := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) (g := f) (f := T.radius) (n := n)
    (t := Ioo D.a D.b) (by
      rintro r ⟨x, rfl⟩
      exact (hinside x).1) isOpen_Ioo.uniqueDiffOn hf hradius (by simp) x hout hin
  have hfinal : |iteratedDeriv n (fun t => f (T.radius t)) x| ≤
      (n.factorial : ℝ) * (K * T.M (T.radius x) ^ ε) * L ^ n := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      Function.comp_def] using hcomp
  exact hfinal.trans_eq (by ring)

end ContinuousFlexibility.Statements
