module

public import ContinuousFlexibility.Analysis.MaterialLogJets

/-!
# Ordinary radial derivatives in the actual material coordinate

The normalized coefficients have bounded ordinary derivatives in the
global material variable. Their recurrence is obtained by differentiating
the actual finite expansion. The only growing factor is the inverse
physical density scale raised to the radial derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Real Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private def BoundedOrdinaryJets (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv k f x‖ ≤ C

private theorem boundedOrdinaryJets_const (a : ℝ) :
    BoundedOrdinaryJets (fun _ => a) := by
  refine ⟨contDiff_const, fun k => ⟨‖a‖, norm_nonneg _, fun x => ?_⟩⟩
  cases k with
  | zero => simp [iteratedDeriv_zero]
  | succ k => simp [iteratedDeriv_const]

private theorem BoundedOrdinaryJets.deriv {f : ℝ → ℝ} (hf : BoundedOrdinaryJets f) :
    BoundedOrdinaryJets (deriv f) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hf.1).2, fun k => ?_⟩
  obtain ⟨C, hC, hb⟩ := hf.2 (k + 1)
  exact ⟨C, hC, fun x => by simpa only [iteratedDeriv_succ'] using hb x⟩

private theorem BoundedOrdinaryJets.add {f g : ℝ → ℝ}
    (hf : BoundedOrdinaryJets f) (hg : BoundedOrdinaryJets g) :
    BoundedOrdinaryJets (f + g) := by
  refine ⟨hf.1.add hg.1, fun k => ?_⟩
  obtain ⟨C, hC, hfb⟩ := hf.2 k
  obtain ⟨D, hD, hgb⟩ := hg.2 k
  refine ⟨C + D, add_nonneg hC hD, fun x => ?_⟩
  rw [iteratedDeriv_add (hf.1.contDiffAt.of_le (by simp)) (hg.1.contDiffAt.of_le (by simp))]
  exact (norm_add_le _ _).trans (add_le_add (hfb x) (hgb x))

private theorem BoundedOrdinaryJets.sub {f g : ℝ → ℝ}
    (hf : BoundedOrdinaryJets f) (hg : BoundedOrdinaryJets g) :
    BoundedOrdinaryJets (f - g) := by
  refine ⟨hf.1.sub hg.1, fun k => ?_⟩
  obtain ⟨C, hC, hfb⟩ := hf.2 k
  obtain ⟨D, hD, hgb⟩ := hg.2 k
  refine ⟨C + D, add_nonneg hC hD, fun x => ?_⟩
  rw [iteratedDeriv_sub (hf.1.contDiffAt.of_le (by simp)) (hg.1.contDiffAt.of_le (by simp))]
  exact (norm_sub_le _ _).trans (add_le_add (hfb x) (hgb x))

private theorem BoundedOrdinaryJets.mul {f g : ℝ → ℝ}
    (hf : BoundedOrdinaryJets f) (hg : BoundedOrdinaryJets g) :
    BoundedOrdinaryJets (f * g) := by
  classical
  choose C hC hfb using hf.2
  choose D hD hgb using hg.2
  refine ⟨hf.1.mul hg.1, fun k =>
    ⟨∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * C j * D (k - j),
      Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j)) (hD _)),
      fun x => ?_⟩⟩
  rw [iteratedDeriv_mul (hf.1.contDiffAt.of_le (by simp)) (hg.1.contDiffAt.of_le (by simp))]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg (α := ℝ) (k.choose j))]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb j x) (Nat.cast_nonneg _))
    (hgb (k - j) x) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC j))

/-- Coefficients of the normalized radial derivative in the material
variable. The logarithm argument is the log of the pulled-back scale. -/
def materialRadialNormalizedCoefficient (L : ℝ → ℝ) :
    (n : ℕ) → Fin (n + 1) → ℝ → ℝ
  | 0, _ => fun _ => 1
  | n + 1, j =>
    Fin.snoc (α := fun _ : Fin (n + 2) => ℝ → ℝ)
      (fun i : Fin (n + 1) =>
        deriv (materialRadialNormalizedCoefficient L n i) -
          ((fun _ => (n : ℝ)) * deriv L) * materialRadialNormalizedCoefficient L n i)
      (fun _ => 0) j +
    Fin.cons (α := fun _ : Fin (n + 2) => ℝ → ℝ)
      (fun _ => 0) (materialRadialNormalizedCoefficient L n) j

private theorem materialRadialNormalizedCoefficient_bounded {L : ℝ → ℝ}
    (hL : BoundedOrdinaryJets (deriv L)) (n : ℕ) :
    ∀ j : Fin (n + 1), BoundedOrdinaryJets (materialRadialNormalizedCoefficient L n j) := by
  induction n with
  | zero => exact fun _ => boundedOrdinaryJets_const 1
  | succ n ih =>
    let A (i : Fin (n + 1)) : ℝ → ℝ :=
      deriv (materialRadialNormalizedCoefficient L n i) -
        ((fun _ => (n : ℝ)) * deriv L) * materialRadialNormalizedCoefficient L n i
    let O : ℝ → ℝ := fun _ => 0
    have hA (i : Fin (n + 1)) : BoundedOrdinaryJets (A i) :=
      (ih i).deriv.sub (((boundedOrdinaryJets_const (n : ℝ)).mul hL).mul (ih i))
    have hsnoc (j : Fin (n + 2)) :
        BoundedOrdinaryJets (Fin.snoc (α := fun _ : Fin (n + 2) => ℝ → ℝ) A O j) := by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]
        exact boundedOrdinaryJets_const 0
      · rw [Fin.snoc_castSucc]
        exact hA i
    have hcons (j : Fin (n + 2)) :
        BoundedOrdinaryJets (Fin.cons (α := fun _ : Fin (n + 2) => ℝ → ℝ)
          O (materialRadialNormalizedCoefficient L n) j) := by
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [Fin.cons_zero]
        exact boundedOrdinaryJets_const 0
      · rw [Fin.cons_succ]
        exact ih i
    exact fun j => (hsnoc j).add (hcons j)

private theorem materialRadialNormalizedCoefficient_sum_succ (L : ℝ → ℝ)
    (n : ℕ) (x : ℝ) (v : ℕ → ℝ) :
    (∑ j : Fin (n + 2), materialRadialNormalizedCoefficient L (n + 1) j x * v j.val) =
      (∑ i : Fin (n + 1), (deriv (materialRadialNormalizedCoefficient L n i) x -
        (n : ℝ) * deriv L x * materialRadialNormalizedCoefficient L n i x) * v i.val) +
      ∑ i : Fin (n + 1), materialRadialNormalizedCoefficient L n i x * v (i.val + 1) := by
  let A (i : Fin (n + 1)) : ℝ → ℝ :=
    deriv (materialRadialNormalizedCoefficient L n i) -
      ((fun _ => (n : ℝ)) * deriv L) * materialRadialNormalizedCoefficient L n i
  let O : ℝ → ℝ := fun _ => 0
  let left : Fin (n + 2) → ℝ → ℝ := Fin.snoc (α := fun _ : Fin (n + 2) => ℝ → ℝ) A O
  let right : Fin (n + 2) → ℝ → ℝ :=
    Fin.cons (α := fun _ : Fin (n + 2) => ℝ → ℝ) O (materialRadialNormalizedCoefficient L n)
  have hsnoc :
      (∑ j : Fin (n + 2), left j x * v j.val) = ∑ i : Fin (n + 1), A i x * v i.val := by
    rw [Fin.sum_univ_castSucc]
    simp only [left, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, O, zero_mul, add_zero]
  have hcons :
      (∑ j : Fin (n + 2), right j x * v j.val) =
        ∑ i : Fin (n + 1), materialRadialNormalizedCoefficient L n i x * v (i.val + 1) := by
    rw [Fin.sum_univ_succ]
    simp only [right, Fin.cons_zero, Fin.cons_succ, Fin.val_succ, O, zero_mul, zero_add]
  change (∑ j : Fin (n + 2), (left j x + right j x) * v j.val) = _
  simp only [add_mul, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hsnoc hcons

private theorem materialRadialNormalizedCoefficient_formula {L G : ℝ → ℝ}
    (hL : ContDiff ℝ ∞ L) (hbL : BoundedOrdinaryJets (deriv L))
    (hG : ContDiff ℝ ∞ G) (F : ℕ → ℝ → ℝ) (hF0 : F 0 = G)
    (hFstep : ∀ n, F (n + 1) = fun x => Real.exp (-L x) * deriv (F n) x)
    (n : ℕ) :
    F n = fun x => Real.exp (-(n : ℝ) * L x) *
      ∑ j : Fin (n + 1), materialRadialNormalizedCoefficient L n j x * iteratedDeriv j.val G x := by
  induction n with
  | zero =>
    rw [hF0]
    funext x
    simp [materialRadialNormalizedCoefficient, iteratedDeriv_zero]
  | succ n ih =>
    rw [hFstep n, ih]
    funext x
    let C := materialRadialNormalizedCoefficient L n
    let S (y : ℝ) : ℝ := ∑ i : Fin (n + 1), C i y * iteratedDeriv i.val G y
    let P (y : ℝ) : ℝ := Real.exp (-(n : ℝ) * L y)
    have hCi (i : Fin (n + 1)) : DifferentiableAt ℝ (C i) x :=
      ((materialRadialNormalizedCoefficient_bounded hbL n i).1.differentiable (by simp)) x
    have hGsmooth (k : ℕ) : ContDiff ℝ ∞ (iteratedDeriv k G) := by
      induction k with
      | zero => simpa only [iteratedDeriv_zero] using hG
      | succ k hk =>
        rw [iteratedDeriv_succ]
        exact (contDiff_infty_iff_deriv.mp hk).2
    have hGi (i : Fin (n + 1)) :
        HasDerivAt (iteratedDeriv i.val G) (iteratedDeriv (i.val + 1) G x) x := by
      rw [iteratedDeriv_succ]
      exact ((hGsmooth i.val).differentiable (by simp) x).hasDerivAt
    have hS : HasDerivAt S (∑ i : Fin (n + 1), (deriv (C i) x * iteratedDeriv i.val G x +
        C i x * iteratedDeriv (i.val + 1) G x)) x :=
      HasDerivAt.fun_sum (fun i _ => (hCi i).hasDerivAt.mul (hGi i))
    have hP : HasDerivAt P (P x * (-(n : ℝ) * deriv L x)) x :=
      (((hL.differentiable (by simp) x).hasDerivAt).const_mul (-(n : ℝ))).exp
    have hscale : Real.exp (-L x) * P x = Real.exp (-((n + 1 : ℕ) : ℝ) * L x) := by
      change Real.exp (-L x) * Real.exp (-(n : ℝ) * L x) = _
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hsum :
        (∑ j : Fin (n + 2), materialRadialNormalizedCoefficient L (n + 1) j x *
          iteratedDeriv j.val G x) =
        (-(n : ℝ) * deriv L x) * S x +
          (∑ i : Fin (n + 1), (deriv (C i) x * iteratedDeriv i.val G x +
            C i x * iteratedDeriv (i.val + 1) G x)) := by
      rw [materialRadialNormalizedCoefficient_sum_succ L n x (fun j => iteratedDeriv j G x)]
      change (∑ i : Fin (n + 1), (deriv (C i) x - (n : ℝ) * deriv L x * C i x) *
          iteratedDeriv i.val G x) +
        (∑ i : Fin (n + 1), C i x * iteratedDeriv (i.val + 1) G x) = _
      unfold S
      simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc,
        neg_mul, Finset.sum_neg_distrib]
      ring
    change Real.exp (-L x) * deriv (fun y => P y * S y) x =
      Real.exp (-((n + 1 : ℕ) : ℝ) * L x) * _
    have hprod :
        deriv (fun y => P y * S y) x =
          (P x * (-(n : ℝ) * deriv L x)) * S x +
            P x * (∑ i : Fin (n + 1), (deriv (C i) x * iteratedDeriv i.val G x +
              C i x * iteratedDeriv (i.val + 1) G x)) :=
      (hP.mul hS).deriv
    rw [hprod, hsum, ← hscale]
    ring

private theorem contDiffOn_iteratedDeriv_radial {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hU (by simp)

private theorem contDiff_comp_affineMaterialRadius {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b)) :
    ContDiff ℝ ∞ (fun x => f ((affineMaterialData D sample).radius x)) :=
  hf.comp_contDiff contDiff_affineMaterialData_radius
    (fun x => (affineMaterialData_radius_mem_rho hab x).1)

/-- The material derivative chain rule uses only the scalar affine model. -/
theorem iteratedDeriv_comp_affineMaterialRadius {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b))
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t => f ((affineMaterialData D sample).radius t)) x =
      materialDerivativeIterate (affineMaterialData D sample) n f
        ((affineMaterialData D sample).radius x) := by
  let T := affineMaterialData D sample
  have hell : ContDiffOn ℝ ∞ T.ell (Ioo D.a D.b) :=
    affineMaterialData_smooth_scalar (sample := sample) hab _ (by simp [T])
  induction n generalizing f with
  | zero => simp [materialDerivativeIterate]
  | succ n ih =>
    have hderiv : deriv (fun t => f (T.radius t)) =
        (fun t => materialDerivative T f (T.radius t)) := by
      funext t
      have ht := (affineMaterialData_radius_mem_rho (sample := sample) hab t).1
      have hd : DifferentiableAt ℝ f (T.radius t) :=
        (hf.differentiableOn (by simp) _ ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
      simpa only [materialDerivative, Function.comp_def, mul_comm] using
        (hd.hasDerivAt.comp t (hasDerivAt_affineMaterialData_radius (sample := sample) hab t)).deriv
    have hnext : ContDiffOn ℝ ∞ (materialDerivative T f) (Ioo D.a D.b) :=
      hell.mul (hf.deriv_of_isOpen isOpen_Ioo (by simp))
    change iteratedDeriv (n + 1) (fun t => f (T.radius t)) x = _
    rw [iteratedDeriv_succ', hderiv]
    exact ih hnext

private theorem inverse_endpointEll_le_E0_sq {d0 d : ℝ} (hd0 : 0 < d0) (hd : 0 < d)
    (hdlt : d < d0) :
    (endpointEll d0 d)⁻¹ ≤ d0⁻¹ * (materialE0 (endpointX d0 d)) ^ (2 : ℕ) := by
  let x := endpointX d0 d
  have hx : 0 < x := endpointX_pos hd hdlt
  have hdist : d = d0 * Real.exp (-(x ^ 2)) := (endpointDistance_endpointX hd0 hd hdlt).symm
  have hl : 1 ≤ materialLogFactor x := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hx.le)
    simpa only [materialLogFactor, Real.log_exp] using h
  have hp : 0 ≤ x ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hx.le _
  have hprod : x ^ ((5 : ℝ) / 2) ≤ x ^ ((5 : ℝ) / 2) * materialLogFactor x :=
    le_mul_of_one_le_right hp hl
  have hpoly : x ^ 2 + x ≤ materialE0Exponent x + materialE0Exponent x := by
    unfold materialE0Exponent
    by_cases hx1 : 1 ≤ x
    · have h₂ : x ^ (2 : ℕ) ≤ x ^ ((5 : ℝ) / 2) := by
        simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hx1
          (by norm_num : (2 : ℝ) ≤ 5 / 2)
      have h₁ : x ≤ x ^ (2 : ℕ) := by nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
      linarith only [h₂, h₁, hprod]
    · have h₁ := (le_of_not_ge hx1)
      have h₂ : x ^ (2 : ℕ) ≤ 1 := pow_le_one₀ hx.le h₁
      linarith only [h₁, h₂, hprod, hp]
  have hexp : Real.exp (x ^ 2 + x) ≤ (materialE0 x) ^ (2 : ℕ) := by
    rw [materialE0, pow_two (Real.exp (materialE0Exponent x)), ← Real.exp_add]
    exact Real.exp_le_exp.mpr hpoly
  have hlinear : 1 + x ≤ Real.exp x := by simpa only [add_comm] using Real.add_one_le_exp x
  calc
    (endpointEll d0 d)⁻¹ = d0⁻¹ * (Real.exp (x ^ 2) * (1 + x)) := by
      change (d / (1 + x))⁻¹ = _
      rw [inv_div, hdist, Real.exp_neg, div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ ≤ d0⁻¹ * (Real.exp (x ^ 2) * Real.exp x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlinear (Real.exp_nonneg _))
        (inv_nonneg.mpr hd0.le)
    _ ≤ d0⁻¹ * (materialE0 x) ^ (2 : ℕ) := by
      rw [← Real.exp_add]
      exact mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr hd0.le)

/-- One inverse density scale costs at most the square of the actual E0
weight, with a constant depending on the physical interval. -/
theorem affineMaterialData_inv_ell_le_E0_sq {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo D.a D.b,
      ((affineMaterialData D sample).ell r)⁻¹ ≤ C * ((affineMaterialData D sample).E0 r) ^ (2 : ℕ) := by
  let T := affineMaterialData D sample
  obtain ⟨d0, δ, hd0, hδ, hδlt, hL, hR⟩ :=
    affineMaterialData_endpoint_formulas (sample := sample) hab
  have hδ₀ : δ < d0 := hδlt.trans_le (min_le_left _ _)
  have hp (r : ℝ) (hr : r ∈ Ioo D.a D.b) :=
    affineMaterialData_positive (sample := sample) hab hr
  have hs := affineMaterialData_smooth_scalar (sample := sample) hab
  have hEll : ContinuousOn T.ell (Ioo D.a D.b) := (hs T.ell (by simp [T])).continuousOn
  have hE0 : ContinuousOn T.E0 (Ioo D.a D.b) := (hs T.E0 (by simp [T])).continuousOn
  have hc : ContinuousOn (fun r => (T.ell r)⁻¹ / (T.E0 r) ^ (2 : ℕ)) (Ioo D.a D.b) :=
    (hEll.inv₀ (fun r hr => (hp r hr).1.ne')).div₀ (hE0.pow 2)
      (fun r hr => (pow_pos (hp r hr).2.2.1 _).ne')
  have hsub : Icc (D.a + δ) (D.b - δ) ⊆ Ioo D.a D.b :=
    fun _ hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hc.mono hsub)
  let C := max d0⁻¹ (max B 0)
  have hC₀ : 0 ≤ C := (le_max_right B 0).trans (le_max_right d0⁻¹ (max B 0))
  have hC₁ : d0⁻¹ ≤ C := le_max_left _ _
  refine ⟨C, hC₀, fun r hr => ?_⟩
  have hE : 0 ≤ (T.E0 r) ^ (2 : ℕ) := sq_nonneg _
  by_cases hl : r < D.a + δ
  · have hf := hL r ⟨hr.1, hl⟩
    change (T.ell r)⁻¹ ≤ C * (T.E0 r) ^ (2 : ℕ)
    have he : T.ell r = endpointEll d0 (r - D.a) := hf.1
    rw [he, hf.2.2.1]
    exact (inverse_endpointEll_le_E0_sq hd0 (sub_pos.mpr hr.1) (by linarith)).trans
      (mul_le_mul_of_nonneg_right hC₁ (sq_nonneg _))
  by_cases hright : D.b - δ < r
  · have hf := hR r ⟨hright, hr.2⟩
    change (T.ell r)⁻¹ ≤ C * (T.E0 r) ^ (2 : ℕ)
    have he : T.ell r = endpointEll d0 (D.b - r) := hf.1
    rw [he, hf.2.2.1]
    exact (inverse_endpointEll_le_E0_sq hd0 (sub_pos.mpr hr.2) (by linarith)).trans
      (mul_le_mul_of_nonneg_right hC₁ (sq_nonneg _))
  have hb : (T.ell r)⁻¹ / (T.E0 r) ^ (2 : ℕ) ≤ B :=
    hB ⟨r, ⟨le_of_not_gt hl, le_of_not_gt hright⟩, rfl⟩
  have hb' := (div_le_iff₀ (pow_pos (hp r hr).2.2.1 2)).mp hb
  have hBC : B ≤ C := (le_max_left B 0).trans (le_max_right d0⁻¹ (max B 0))
  exact hb'.trans (mul_le_mul_of_nonneg_right hBC hE)

/-- The affine material model satisfies the actual ordinary radial
derivative expansion of W01, with exponent 2n in the coefficient bound. -/
theorem radialMaterialExpansion_affineMaterialData {D : ReferenceData} {sample : ℕ → ℝ}
    (hab : D.a < D.b) : RadialMaterialExpansion D (affineMaterialData D sample) := by
  let T := affineMaterialData D sample
  let l : ℝ → ℝ := fun r => Real.log (T.ell r)
  let L : ℝ → ℝ := fun x => l (T.radius x)
  have hrad (x : ℝ) : T.radius x ∈ Ioo D.a D.b :=
    (affineMaterialData_radius_mem_rho (sample := sample) hab x).1
  have hp (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < T.ell r :=
    (affineMaterialData_positive (sample := sample) hab hr).1
  have hs := affineMaterialData_smooth_scalar (sample := sample) hab
  have hEll : ContDiffOn ℝ ∞ T.ell (Ioo D.a D.b) := hs _ (by simp [T])
  have hlog : ContDiffOn ℝ ∞ l (Ioo D.a D.b) :=
    hEll.log (fun r hr => (hp r hr).ne')
  have hL : ContDiff ℝ ∞ L := contDiff_comp_affineMaterialRadius (sample := sample) hab hlog
  have hbL : BoundedOrdinaryJets (deriv L) := by
    refine ⟨(contDiff_infty_iff_deriv.mp hL).2, fun k => ?_⟩
    obtain ⟨B, hB, hb⟩ :=
      logarithmicDerivativeBounds_affineMaterialData (sample := sample) hab (k + 1) (Nat.succ_pos k)
    refine ⟨B, hB, fun x => ?_⟩
    rw [← iteratedDeriv_succ']
    change ‖iteratedDeriv (k + 1) (fun t => l (T.radius t)) x‖ ≤ B
    rw [iteratedDeriv_comp_affineMaterialRadius hab hlog, Real.norm_eq_abs]
    exact (hb (T.radius x) (hrad x)).2.2
  have hinvExp (x : ℝ) : Real.exp (-L x) = (T.ell (T.radius x))⁻¹ := by
    change Real.exp (-Real.log (T.ell (T.radius x))) = _
    rw [Real.exp_neg, Real.exp_log (hp _ (hrad x))]
  obtain ⟨E, hE, hEbound⟩ := affineMaterialData_inv_ell_le_E0_sq (sample := sample) hab
  intro n
  let C := materialRadialNormalizedCoefficient L n
  let c (j : Fin (n + 1)) : ℝ → ℝ :=
    fun r => Real.exp (-(n : ℝ) * L (T.rho r)) * C j (T.rho r)
  have hC (j : Fin (n + 1)) : BoundedOrdinaryJets (C j) :=
    materialRadialNormalizedCoefficient_bounded hbL n j
  have hj (j : Fin (n + 1)) := (hC j).2 0
  choose K hK hKb using hj
  let B : ℝ := ∑ j : Fin (n + 1), K j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hK j)
  have hslope : ContDiffOn ℝ ∞ T.rho (Ioo D.a D.b) := hs _ (by simp [T])
  refine ⟨c, ?_, ⟨E ^ n * B, ((2 * n : ℕ) : ℝ), mul_nonneg (pow_nonneg hE _) hB,
    Nat.cast_nonneg _, ?_⟩, ?_⟩
  · intro j
    have hS : ContDiff ℝ ∞ (fun x => Real.exp (-(n : ℝ) * L x)) :=
      (contDiff_const.mul hL).exp
    exact (hS.mul (hC j).1).comp_contDiffOn hslope
  · intro j r hr
    have hρ : T.radius (T.rho r) = r := affineMaterialData_radius_rho hab hr
    have hscale : Real.exp (-(n : ℝ) * L (T.rho r)) = ((T.ell r)⁻¹) ^ n := by
      have he : -(n : ℝ) * L (T.rho r) = (n : ℝ) * (-L (T.rho r)) := by ring
      rw [he, Real.exp_nat_mul, hinvExp, hρ]
    have hb : |C j (T.rho r)| ≤ B := by
      have h := hKb j (T.rho r)
      rw [iteratedDeriv_zero, Real.norm_eq_abs] at h
      exact h.trans (Finset.single_le_sum (fun i _ => hK i) (Finset.mem_univ j))
    have hPow : ((T.ell r)⁻¹) ^ n ≤ E ^ n * T.E0 r ^ ((2 * n : ℕ) : ℝ) := by
      have h := pow_le_pow_left₀ (inv_nonneg.mpr (hp r hr).le) (hEbound r hr) n
      simpa only [mul_pow, ← pow_mul, Real.rpow_natCast] using h
    change |Real.exp (-(n : ℝ) * L (T.rho r)) * C j (T.rho r)| ≤ _
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), hscale]
    calc
      _ ≤ (E ^ n * T.E0 r ^ ((2 * n : ℕ) : ℝ)) * B :=
        mul_le_mul hPow hb (abs_nonneg _)
          (mul_nonneg (pow_nonneg hE _) (Real.rpow_nonneg
            (affineMaterialData_positive (sample := sample) hab hr).2.2.1.le _))
      _ = _ := by ring
  · intro f hf r hr
    let G : ℝ → ℝ := fun x => f (T.radius x)
    let F (k : ℕ) : ℝ → ℝ := fun x => iteratedDeriv k f (T.radius x)
    have hG : ContDiff ℝ ∞ G := contDiff_comp_affineMaterialRadius (sample := sample) hab hf
    have hF0 : F 0 = G := by funext x; simp [F, G, iteratedDeriv_zero]
    have hFstep (k : ℕ) : F (k + 1) = fun x => Real.exp (-L x) * deriv (F k) x := by
      funext x
      have hdk : DifferentiableAt ℝ (iteratedDeriv k f) (T.radius x) :=
        ((contDiffOn_iteratedDeriv_radial isOpen_Ioo hf k).differentiableOn (by simp) _
          (hrad x)).differentiableAt (isOpen_Ioo.mem_nhds (hrad x))
      have hd := (hdk.hasDerivAt.comp x
        (hasDerivAt_affineMaterialData_radius (sample := sample) hab x)).deriv
      change iteratedDeriv (k + 1) f (T.radius x) =
        Real.exp (-L x) * deriv (fun y => iteratedDeriv k f (T.radius y)) x
      change deriv (fun y => iteratedDeriv k f (T.radius y)) x =
        deriv (iteratedDeriv k f) (T.radius x) * T.ell (T.radius x) at hd
      rw [iteratedDeriv_succ, hinvExp, hd]
      rw [mul_left_comm ((T.ell (T.radius x))⁻¹), inv_mul_cancel₀ (hp _ (hrad x)).ne', mul_one]
    have heq := congrFun (materialRadialNormalizedCoefficient_formula hL hbL hG F hF0 hFstep n)
      (T.rho r)
    have hρ : T.radius (T.rho r) = r := affineMaterialData_radius_rho hab hr
    change iteratedDeriv n f (T.radius (T.rho r)) =
      Real.exp (-(n : ℝ) * L (T.rho r)) *
        ∑ j : Fin (n + 1), C j (T.rho r) * iteratedDeriv j.val G (T.rho r) at heq
    rw [hρ] at heq
    rw [heq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hDj : iteratedDeriv j.val G (T.rho r) = materialDerivativeIterate T j.val f r := by
      change iteratedDeriv j.val (fun x => f (T.radius x)) (T.rho r) = _
      rw [iteratedDeriv_comp_affineMaterialRadius hab hf, hρ]
    change Real.exp (-(n : ℝ) * L (T.rho r)) *
      (C j (T.rho r) * iteratedDeriv j.val G (T.rho r)) =
      c j r * materialDerivativeIterate T j.val f r
    rw [hDj]
    dsimp [c]
    ring

end ContinuousFlexibility.Statements
