module

public import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Ordinary mixed jets from bounded material jets

The radius transports each actual material derivative to an ordinary
derivative. Uniform logarithmic jet bounds control differentiation of
the positive weight. The physical derivative expansion then loses just
one factor of the envelope M.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem contDiff_materialRadius_comp {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b)) :
    ContDiff ℝ ∞ (fun x => f (T.radius x)) := by
  obtain ⟨_, _, _, _, _, _, hradius, hinside, _⟩ := hT
  exact hf.comp_contDiff hradius fun x => (hinside x).1

/-- Every material derivative is the actual derivative in the radius coordinate. -/
theorem iteratedDeriv_comp_materialRadius {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b))
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t => f (T.radius t)) x =
      materialDerivativeIterate T n f (T.radius x) := by
  obtain ⟨hsmooth, _, _, _, _, _, _, hinside, _, hrad, _⟩ := hT
  have hell : ContDiffOn ℝ ∞ T.ell (Ioo D.a D.b) := hsmooth T.ell (by simp)
  induction n generalizing f with
  | zero => simp [materialDerivativeIterate]
  | succ n ih =>
    have hderiv : deriv (fun t => f (T.radius t)) =
        (fun t => materialDerivative T f (T.radius t)) := by
      funext t
      have ht := (hinside t).1
      have hd : DifferentiableAt ℝ f (T.radius t) :=
        (hf.differentiableOn (by simp) _ ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
      simpa only [materialDerivative, Function.comp_def, mul_comm] using
        (hd.hasDerivAt.comp t (hrad t)).deriv
    have hnext : ContDiffOn ℝ ∞ (materialDerivative T f) (Ioo D.a D.b) :=
      hell.mul (hf.deriv_of_isOpen isOpen_Ioo (by simp))
    rw [iteratedDeriv_succ', hderiv]
    exact ih hnext

private theorem iteratedDeriv_product_majorant {ι : Type*} {F W : ℝ → ℝ}
    {G : ι → ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ∀ θ, ContDiff ℝ ∞ (G θ))
    (hW : ∀ x, 0 ≤ W x) (n : ℕ)
    (hFb : ∀ i : ℕ, i ≤ n → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |iteratedDeriv i F x| ≤ C * W x)
    (hGb : ∀ i : ℕ, i ≤ n → ∃ C : ℝ, 0 ≤ C ∧
      ∀ θ x, |iteratedDeriv i (G θ) x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ x, |iteratedDeriv n (fun t => F t * G θ t) x| ≤ C * W x := by
  have hA (i : Fin (n + 1)) := hFb i.val (Nat.le_of_lt_succ i.isLt)
  have hB (i : Fin (n + 1)) := hGb i.val (Nat.le_of_lt_succ i.isLt)
  choose A hA₀ hAb using hA
  choose B hB₀ hBb using hB
  let d (i : Fin (n + 1)) : Fin (n + 1) :=
    ⟨n - i.val, Nat.lt_succ_of_le (Nat.sub_le n i.val)⟩
  let c (i : Fin (n + 1)) : ℝ := (n.choose i.val : ℝ) * A i * B (d i)
  have hc (i : Fin (n + 1)) : 0 ≤ c i := by
    dsimp [c]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA₀ i)) (hB₀ (d i))
  refine ⟨∑ i, c i, Finset.sum_nonneg (fun i _ => hc i), fun θ x => ?_⟩
  let term (i : ℕ) : ℝ :=
    (n.choose i : ℝ) * iteratedDeriv i F x * iteratedDeriv (n - i) (G θ) x
  have hleibniz : iteratedDeriv n (fun t => F t * G θ t) x =
      ∑ i : Fin (n + 1), term i.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_mul (hF.contDiffAt.of_le (by simp))
      ((hG θ).contDiffAt.of_le (by simp))
  rw [hleibniz, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  unfold term
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n.choose i.val))]
  calc
    _ ≤ (n.choose i.val : ℝ) * (A i * W x) * B (d i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hAb i x) (Nat.cast_nonneg _))
        (hBb (d i) θ x) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA₀ i) (hW x)))
    _ = c i * W x := by dsimp [c]; ring

/-- All derivatives of the exponential retain its exponential factor. -/
theorem iteratedDeriv_exp_majorant {L : ℝ → ℝ} (hL : ContDiff ℝ ∞ L)
    (h : ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n L x| ≤ C)
    (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |iteratedDeriv n (fun t => Real.exp (L t)) x| ≤ C * Real.exp (L x) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact ⟨1, zero_le_one, fun x => by
        simp [iteratedDeriv_zero, abs_of_pos (Real.exp_pos (L x))]⟩
    | succ n =>
      have hderiv : deriv (fun t => Real.exp (L t)) =
          (fun t => Real.exp (L t) * deriv L t) :=
        funext fun x => ((hL.differentiable (by simp) x).hasDerivAt.exp).deriv
      have hD : ContDiff ℝ ∞ (deriv L) := (contDiff_infty_iff_deriv.mp hL).2
      have hDb (i : ℕ) (_ : i ≤ n) : ∃ C : ℝ, 0 ≤ C ∧
          ∀ (_ : Unit) x, |iteratedDeriv i (deriv L) x| ≤ C := by
        obtain ⟨C, hC, hb⟩ := h (i + 1) (Nat.succ_pos i)
        exact ⟨C, hC, fun _ x => by rw [← iteratedDeriv_succ']; exact hb x⟩
      obtain ⟨C, hC, hb⟩ := iteratedDeriv_product_majorant (G := fun _ : Unit => deriv L)
        hL.exp (fun _ => hD) (fun x => (Real.exp_pos (L x)).le) n
        (fun i hi => ih i (Nat.lt_succ_of_le hi)) hDb
      refine ⟨C, hC, fun x => ?_⟩
      rw [iteratedDeriv_succ', hderiv]
      exact hb () x

/-- The positive material weight retains its original power after any fixed
number of material-coordinate differentiations. -/
theorem iteratedDeriv_materialH_rpow_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (γ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n (fun t => T.H (T.radius t) ^ γ) x| ≤ C * T.H (T.radius x) ^ γ := by
  have hdata := hT
  obtain ⟨hcont, hpos, _, _, _, _, _, hinside, _, _, _, _, _, hlog, _⟩ := hdata
  have hp (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < T.H r := (hpos r hr).2.1
  have hlogH : ContDiffOn ℝ ∞ (fun r => Real.log (T.H r)) (Ioo D.a D.b) :=
    (hcont T.H (by simp)).log (fun r hr => (hp r hr).ne')
  let L : ℝ → ℝ := fun x => Real.log (T.H (T.radius x)) * γ
  have hL : ContDiff ℝ ∞ L := (contDiff_materialRadius_comp hT hlogH).mul contDiff_const
  have hLb (k : ℕ) (hk : 0 < k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv k L x| ≤ C := by
    obtain ⟨C, hC, hb⟩ := hlog k hk
    refine ⟨C * |γ|, mul_nonneg hC (abs_nonneg _), fun x => ?_⟩
    change |iteratedDeriv k (fun t => Real.log (T.H (T.radius t)) * γ) x| ≤ _
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_comp_materialRadius hT hlogH, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb (T.radius x) (hinside x).1).1 (abs_nonneg _)
  have hpow : (fun x => T.H (T.radius x) ^ γ) = (fun x => Real.exp (L x)) := by
    funext x
    exact Real.rpow_def_of_pos (hp _ (hinside x).1) γ
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_exp_majorant hL hLb n
  refine ⟨C, hC, fun x => ?_⟩
  rw [hpow, congrFun hpow x]
  exact hb x

private theorem contDiffOn_angular_slice {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (b : ℕ) (θ : ℝ) :
    ContDiffOn ℝ ∞ (fun r => iteratedDeriv b (fun t => f (r, t)) θ) (Ioo D.a D.b) := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hs : ContDiff ℝ ∞ (fun r : ℝ => (r, θ)) := contDiff_id.prodMk contDiff_const
  have hm : MapsTo (fun r : ℝ => (r, θ)) (Ioo D.a D.b) (annularOpen D) :=
    fun _ hr => ⟨hr, mem_univ _⟩
  simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero] using
    (contDiffOn_mixedDerivative hU hf 0 b).comp hs.contDiffOn hm

/-- Bounded material-coordinate jets give a uniform material derivative
bound for each actual angular slice of the unweighted height. -/
theorem materialDerivative_angular_slice_bound {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hbounded : ∀ a b : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ p : PolarPoint, |mixedDerivative a b (materialPullback T γ f) p| ≤ K)
    (a b : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ θ r, r ∈ Ioo D.a D.b →
      |materialDerivativeIterate T a (fun s => iteratedDeriv b (fun t => f (s, t)) θ) r|
        ≤ K * T.H r ^ γ := by
  have hdata := hT
  obtain ⟨hcont, hpos, _, _, _, _, _, hinside, hinv, _⟩ := hdata
  let F : ℝ → ℝ := fun x => T.H (T.radius x) ^ γ
  let g (θ : ℝ) : ℝ → ℝ := fun r => iteratedDeriv b (fun t => f (r, t)) θ
  let G (θ : ℝ) : ℝ → ℝ :=
    fun x => iteratedDeriv b (fun t => materialPullback T γ f (x, t)) θ
  have hp (x : ℝ) : 0 < T.H (T.radius x) := (hpos _ (hinside x).1).2.1
  have hH : ContDiff ℝ ∞ (fun x => T.H (T.radius x)) :=
    contDiff_materialRadius_comp hT (hcont T.H (by simp))
  have hF : ContDiff ℝ ∞ F := hH.rpow_const_of_ne (fun x => (hp x).ne')
  have hg (θ : ℝ) : ContDiffOn ℝ ∞ (g θ) (Ioo D.a D.b) := contDiffOn_angular_slice hf b θ
  have hGform (θ : ℝ) : G θ =
      (fun x => T.H (T.radius x) ^ (-γ) * g θ (T.radius x)) := by
    funext x
    change iteratedDeriv b (fun t => T.H (T.radius x) ^ (-γ) * f (T.radius x, t)) θ =
      T.H (T.radius x) ^ (-γ) * iteratedDeriv b (fun t => f (T.radius x, t)) θ
    exact iteratedDeriv_const_mul_field (T.H (T.radius x) ^ (-γ)) (fun t => f (T.radius x, t))
  have hG (θ : ℝ) : ContDiff ℝ ∞ (G θ) := by
    rw [hGform θ]
    exact (hH.rpow_const_of_ne (fun x => (hp x).ne')).mul (contDiff_materialRadius_comp hT (hg θ))
  have hGb (i : ℕ) (_ : i ≤ a) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ θ x, |iteratedDeriv i (G θ) x| ≤ K := by
    obtain ⟨K, hK, hb⟩ := hbounded i b
    exact ⟨K, hK, fun θ x => hb (x, θ)⟩
  have hrestore (θ : ℝ) : (fun x => F x * G θ x) = (fun x => g θ (T.radius x)) := by
    funext x
    change T.H (T.radius x) ^ γ * G θ x = _
    rw [hGform θ]
    change T.H (T.radius x) ^ γ * (T.H (T.radius x) ^ (-γ) * g θ (T.radius x)) = _
    rw [← mul_assoc, ← Real.rpow_add (hp x), add_neg_cancel, Real.rpow_zero, one_mul]
  obtain ⟨K, hK, hb⟩ := iteratedDeriv_product_majorant hF hG
    (fun x => (Real.rpow_pos_of_pos (hp x) γ).le) a
    (fun i _ => iteratedDeriv_materialH_rpow_bound hT γ i) hGb
  refine ⟨K, hK, fun θ r hr => ?_⟩
  have hh := hb θ (T.rho r)
  change |iteratedDeriv a (fun t => F t * G θ t) (T.rho r)| ≤ K * T.H (T.radius (T.rho r)) ^ γ at hh
  rw [hrestore θ, iteratedDeriv_comp_materialRadius hT (hg θ), hinv r hr] at hh
  exact hh

/-- Uniform bounds for the actual material pullback imply ordinary mixed
jet bounds with one fixed factor of the material envelope. -/
theorem mixedDerivative_bound_of_materialPullback {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hbounded : ∀ a b : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ p : PolarPoint, |mixedDerivative a b (materialPullback T γ f) p| ≤ K) :
    ∀ a b : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D,
      |mixedDerivative a b f p| ≤ K * T.H p.1 ^ γ * T.M p.1 := by
  intro a b
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, henv, _, _, hexpansion, _⟩ := hdata
  obtain ⟨c, _, ⟨C, A, hC, _, hc⟩, hformula⟩ := hexpansion a
  obtain ⟨E, hE, he⟩ := henv A
  have hj (j : Fin (a + 1)) := materialDerivative_angular_slice_bound hT hf hbounded j.val b
  choose K hK hKb using hj
  let B (j : Fin (a + 1)) : ℝ := C * E * K j
  have hB (j : Fin (a + 1)) : 0 ≤ B j := mul_nonneg (mul_nonneg hC hE.le) (hK j)
  refine ⟨∑ j, B j, Finset.sum_nonneg (fun j _ => hB j), ?_⟩
  intro p hp
  let g : ℝ → ℝ := fun r => iteratedDeriv b (fun t => f (r, t)) p.2
  have hg : ContDiffOn ℝ ∞ g (Ioo D.a D.b) := contDiffOn_angular_slice hf b p.2
  have hr : p.1 ∈ Ioo D.a D.b := hp.1
  have hM : 0 ≤ T.M p.1 := zero_le_one.trans (hpos _ hr).2.2.2
  change |iteratedDeriv a g p.1| ≤ _
  rw [hformula g hg p.1 hr]
  calc
    _ ≤ ∑ j : Fin (a + 1), |c j p.1 * materialDerivativeIterate T j.val g p.1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (a + 1), B j * T.H p.1 ^ γ * T.M p.1 := by
      apply Finset.sum_le_sum
      intro j _
      have hcoef : |c j p.1| ≤ C * (E * T.M p.1) :=
        (hc j p.1 hr).trans (mul_le_mul_of_nonneg_left (he p.1 hr) hC)
      rw [abs_mul]
      calc
        _ ≤ (C * (E * T.M p.1)) * (K j * T.H p.1 ^ γ) :=
          mul_le_mul hcoef (hKb j p.2 p.1 hr) (abs_nonneg _)
            (mul_nonneg hC (mul_nonneg hE.le hM))
        _ = _ := by dsimp [B]; ring
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end ContinuousFlexibility.Statements
