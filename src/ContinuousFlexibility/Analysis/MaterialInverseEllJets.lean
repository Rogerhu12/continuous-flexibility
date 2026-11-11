import ContinuousFlexibility.Analysis.MaterialRadiusJets

/-!
# A fixed material-weight loss for the inverse length scale

The first radial expansion identifies its leading coefficient with
the inverse material length. Its envelope costs one power of M.
Differentiating the inverse length in the actual material coordinate
retains that same power in every order, because all positive logarithmic
jets are bounded.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

theorem material_inv_ell_le_M {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b, (T.ell r)⁻¹ ≤ K * T.M r := by
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, henv, _, _, hrad, _⟩ := hT
  obtain ⟨c, _, ⟨C, A, hC, hA, hb⟩, hformula⟩ := hrad 1
  obtain ⟨B, hB, hBM⟩ := henv A
  refine ⟨C * B, mul_nonneg hC hB.le, fun r hr => ?_⟩
  have hell : T.ell r ≠ 0 := (hpos r hr).1.ne'
  have hc0 : c 0 r = 0 := by
    have h := hformula (fun _ => (1 : ℝ)) contDiff_const.contDiffOn r hr
    simpa [Fin.sum_univ_two, materialDerivativeIterate, materialDerivative,
      iteratedDeriv_one] using h.symm
  have hc1mul : c 1 r * T.ell r = 1 := by
    have h := hformula (fun t : ℝ => t) contDiff_id.contDiffOn r hr
    simpa [Fin.sum_univ_two, materialDerivativeIterate, materialDerivative,
      iteratedDeriv_one, hc0] using h.symm
  have hc1 : c 1 r = (T.ell r)⁻¹ := by
    calc
      c 1 r = (c 1 r * T.ell r) * (T.ell r)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hell, mul_one]
      _ = (T.ell r)⁻¹ := by rw [hc1mul, one_mul]
  have hbound := hb (1 : Fin 2) r hr
  rw [hc1, abs_of_pos (inv_pos.mpr (hpos r hr).1)] at hbound
  exact hbound.trans ((mul_le_mul_of_nonneg_left (hBM r hr) hC).trans_eq
    (mul_assoc C B (T.M r)).symm)

theorem materialInvEll_radius_contDiff {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ContDiff ℝ ∞ (fun x => (T.ell (T.radius x))⁻¹) := by
  apply materialRadius_comp_contDiff hT
  exact (hT.1 T.ell (by simp)).inv (fun r hr => (hT.2.1 r hr).1.ne')

theorem materialInvEll_radius_iteratedDeriv_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
      |iteratedDeriv n (fun t => (T.ell (T.radius t))⁻¹) x| ≤
        K * T.M (T.radius x) := by
  have hdata := hT
  obtain ⟨hsmooth, hpos, _, _, _, _, _, hinside, _, _, _, _, _, hlog, _⟩ := hdata
  have hp (x : ℝ) : 0 < T.ell (T.radius x) := (hpos _ (hinside x).1).1
  have hlogell : ContDiffOn ℝ ∞ (fun r => Real.log (T.ell r)) (Ioo D.a D.b) :=
    (hsmooth T.ell (by simp)).log (fun r hr => (hpos r hr).1.ne')
  let L : ℝ → ℝ := fun x => Real.log (T.ell (T.radius x)) * (-1 : ℝ)
  have hL : ContDiff ℝ ∞ L :=
    (materialRadius_comp_contDiff hT hlogell).mul contDiff_const
  have hLb (k : ℕ) (hk : 0 < k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv k L x| ≤ C := by
    obtain ⟨C, hC, hb⟩ := hlog k hk
    refine ⟨C, hC, fun x => ?_⟩
    change |iteratedDeriv k
      (fun t => Real.log (T.ell (T.radius t)) * (-1 : ℝ)) x| ≤ C
    rw [iteratedDeriv_mul_const_field, abs_mul, abs_neg, abs_one, mul_one,
      iteratedDeriv_comp_materialRadius hT hlogell]
    exact (hb (T.radius x) (hinside x).1).2.2
  have hexp (x : ℝ) : Real.exp (L x) = (T.ell (T.radius x))⁻¹ := by
    dsimp only [L]
    rw [mul_neg_one, Real.exp_neg, Real.exp_log (hp x)]
  have heq : (fun t => (T.ell (T.radius t))⁻¹) = fun t => Real.exp (L t) :=
    funext (fun t => (hexp t).symm)
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_exp_majorant hL hLb n
  obtain ⟨B, hB, hBM⟩ := material_inv_ell_le_M hT
  refine ⟨C * B, mul_nonneg hC hB, fun x => ?_⟩
  rw [heq]
  calc
    _ ≤ C * Real.exp (L x) := hb x
    _ = C * (T.ell (T.radius x))⁻¹ := by rw [hexp]
    _ ≤ C * (B * T.M (T.radius x)) :=
      mul_le_mul_of_nonneg_left (hBM (T.radius x) (hinside x).1) hC
    _ = (C * B) * T.M (T.radius x) := (mul_assoc _ _ _).symm

theorem materialLogH_radius_deriv_iteratedDeriv_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
      |iteratedDeriv n (deriv (fun t => Real.log (T.H (T.radius t)))) x| ≤ K := by
  have hdata := hT
  obtain ⟨hsmooth, hpos, _, _, _, _, _, hinside, _, _, _, _, _, hlog, _⟩ := hdata
  have hlogH : ContDiffOn ℝ ∞ (fun r => Real.log (T.H r)) (Ioo D.a D.b) :=
    (hsmooth T.H (by simp)).log (fun r hr => (hpos r hr).2.1.ne')
  obtain ⟨K, hK, hb⟩ := hlog (n + 1) (Nat.succ_pos n)
  refine ⟨K, hK, fun x => ?_⟩
  rw [← iteratedDeriv_succ', iteratedDeriv_comp_materialRadius hT hlogH]
  exact (hb (T.radius x) (hinside x).1).1

theorem materialInvEll_mixedDerivative_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (a b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : PolarPoint,
      |mixedDerivative a b (fun q => (T.ell (T.radius q.1))⁻¹) p| ≤
        K * T.M (T.radius p.1) := by
  cases b with
  | zero =>
    obtain ⟨K, hK, hb⟩ := materialInvEll_radius_iteratedDeriv_bound hT a
    exact ⟨K, hK, fun p => by
      simpa only [mixedDerivative, iteratedDeriv_zero] using hb p.1⟩
  | succ b =>
    refine ⟨0, le_rfl, fun p => ?_⟩
    simp [mixedDerivative, iteratedDeriv_const]

end ContinuousFlexibility.Statements
