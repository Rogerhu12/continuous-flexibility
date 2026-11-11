import ContinuousFlexibility.Analysis.N01OpticalCollarJetBounds
import ContinuousFlexibility.Analysis.PolynomialJetPowers

/-!
# All reference optical-speed jets on the actual correction collars

The profile and its derivative have uniform jets on the compact annulus.
The original reference inverse-profile bound supplies a fixed component
power for the reciprocal. The selected optical-speed lower bound then
controls the square root at every order. Thus no component-dependent
compactness constant enters the radial reference-flow jet estimates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem scalar_positive_interval_jet_bound
    {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hf : ContDiffOn ℝ ∞ f (Ioi (0 : ℝ))) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r ∈ Icc a b, ‖iteratedFDeriv ℝ n f r‖ ≤ A := by
  have hc₀ : ContinuousOn (iteratedDerivWithin n f (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) :=
    hf.continuousOn_iteratedDerivWithin (by simp) isOpen_Ioi.uniqueDiffOn
  have hc : ContinuousOn (iteratedDeriv n f) (Ioi (0 : ℝ)) :=
    hc₀.congr (fun r hr => (iteratedDerivWithin_of_isOpen isOpen_Ioi hr).symm)
  have hcompact := hc.mono (show Icc a b ⊆ Ioi (0 : ℝ) from fun r hr => ha.trans_le hr.1)
  obtain ⟨A, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hcompact
  refine ⟨max A 0, le_max_right _ _, fun r hr => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hb r hr).trans (le_max_left _ _)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

theorem N01Properties.reference_opticalSpeed_collar_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (j : ℕ → ℕ) (x δ : ℕ → ℝ) {B : ℝ} (hB : 0 < B)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hinside : ∀ m, C.left m < x m - δ m ∧ x m + δ m < C.right m)
    (hspeed : ∀ m r, r ∈ Icc (x m - δ m) (x m + δ m) →
      radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r)
    (n : ℕ) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      r ∈ Ioo (x m - δ m) (x m + δ m) →
      |iteratedDeriv n (opticalSpeed D.w) r| ≤ A * radialE (D.cellIndex (j m)) ^ P := by
  let W (m : ℕ) : ℝ := radialE (D.cellIndex (j m))
  let U (m : ℕ) : Set ℝ := Ioo (x m - δ m) (x m + δ m)
  have hW (m : ℕ) : 1 ≤ W m := by
    have hn : 0 ≤ (D.cellIndex (j m) : ℝ) := Nat.cast_nonneg _
    have he : 1 ≤ Real.exp 1 + (D.cellIndex (j m) : ℝ) :=
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans
        (le_add_of_nonneg_right hn)
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (Real.rpow_nonneg hn _) (Real.log_nonneg he))
  have hW₀ (m : ℕ) : 0 < W m := zero_lt_one.trans_le (hW m)
  have hU (m : ℕ) : IsOpen (U m) := isOpen_Ioo
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hg : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hwd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hm (m : ℕ) (r : ℝ) (hr : r ∈ U m) : r ∈ Ioo (C.left m) (C.right m) :=
    ⟨(hinside m).1.trans hr.1, hr.2.trans (hinside m).2⟩
  have hcore (m : ℕ) (r : ℝ) (hr : r ∈ U m) : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans (hm m r hr).1, (hm m r hr).2.trans (hC.1 m).2.2⟩
  have hrpos (m : ℕ) (r : ℝ) (hr : r ∈ U m) : 0 < r := hg.1.trans (hcore m r hr).1
  have hwpos (m : ℕ) (r : ℝ) (hr : r ∈ U m) : 0 < D.w r :=
    hg.2.2.2.2.1 r (hcore m r hr)
  have hwbound (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      r ∈ U m → ‖iteratedFDeriv ℝ k D.w r‖ ≤ A * W m ^ P := by
    obtain ⟨A, hA, hb⟩ := scalar_positive_interval_jet_bound hg.1 hw.contDiffOn k
    refine ⟨A, 0, hA, le_rfl, fun m r hr => ?_⟩
    simpa only [Real.rpow_zero, mul_one] using
      hb r ⟨(hcore m r hr).1.le, (hcore m r hr).2.le⟩
  obtain ⟨L, hL, hInv⟩ := hN.1.1.inverse_first_jets_cell_bound
  have hwlower (m : ℕ) (r : ℝ) (hr : r ∈ U m) :
      L⁻¹ * W m ^ (-L) ≤ D.w r := by
    have hb := hInv (j m) r (hcell m (hm m r hr))
    have hi : (D.w r)⁻¹ ≤ L * W m ^ L :=
      (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans hb)
    have h : (L * W m ^ L)⁻¹ ≤ D.w r := by
      apply (inv_le_iff₀ (mul_pos hL (Real.rpow_pos_of_pos (hW₀ m) _))).mpr
      simpa only [mul_comm] using (inv_le_iff₀ (hwpos m r hr)).mp hi
    simpa only [mul_inv, Real.rpow_neg (hW₀ m).le] using h
  have hwi (m : ℕ) : ContDiffOn ℝ ∞ (fun r => (D.w r)⁻¹) (U m) :=
    hw.contDiffOn.inv (fun r hr => (hwpos m r hr).ne')
  have hwib (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      r ∈ U m → ‖iteratedFDeriv ℝ k (fun t => (D.w t)⁻¹) r‖ ≤ A * W m ^ P :=
    norm_iteratedFDeriv_inv_polynomial_bound W hW U hU (fun _ => D.w)
      (fun _ => hw.contDiffOn) (inv_pos.mpr hL) hL.le hwlower hwbound k
  let c (r : ℝ) : ℝ := -deriv D.w r / r
  have hc₀ : ContDiffOn ℝ ∞ c (Ioi (0 : ℝ)) :=
    hwd.contDiffOn.neg.div contDiffOn_id (fun r hr => (ne_of_gt hr))
  have hc (m : ℕ) : ContDiffOn ℝ ∞ c (U m) :=
    hc₀.mono (fun r hr => hrpos m r hr)
  have hcb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      r ∈ U m → ‖iteratedFDeriv ℝ k c r‖ ≤ A * W m ^ P := by
    obtain ⟨A, hA, hb⟩ := scalar_positive_interval_jet_bound hg.1 hc₀ k
    refine ⟨A, 0, hA, le_rfl, fun m r hr => ?_⟩
    simpa only [Real.rpow_zero, mul_one] using
      hb r ⟨(hcore m r hr).1.le, (hcore m r hr).2.le⟩
  let q (r : ℝ) : ℝ := c r * (D.w r)⁻¹
  have hq (m : ℕ) : ContDiffOn ℝ ∞ q (U m) := (hc m).mul (hwi m)
  have hqb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      r ∈ U m → ‖iteratedFDeriv ℝ k q r‖ ≤ A * W m ^ P :=
    norm_iteratedFDeriv_mul_polynomial_bound W hW U hU (fun _ => c)
      (fun _ r => (D.w r)⁻¹) hc hwi k (fun l _ => hcb l) (fun l _ => hwib l)
  have heq : (fun r => Real.sqrt (q r)) = opticalSpeed D.w := by
    funext r
    unfold opticalSpeed
    congr 1
    dsimp only [q, c]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  let R : ℝ := D.b - D.a
  let lam : ℝ := ((2 * R)⁻¹) ^ 2
  have hR : 0 < R := sub_pos.mpr hg.2.1
  have hlam : 0 < lam := sq_pos_of_pos (inv_pos.mpr (mul_pos (by norm_num) hR))
  have hqlower (m : ℕ) (r : ℝ) (hr : r ∈ U m) :
      lam * W m ^ (-(2 * B)) ≤ q r := by
    have hs := hspeed m r ⟨hr.1.le, hr.2.le⟩
    rw [← heq] at hs
    have hτ : 0 < W m ^ (-B) / (2 * R) :=
      div_pos (Real.rpow_pos_of_pos (hW₀ m) _) (mul_pos (by norm_num) hR)
    have hqpos : 0 < q r := Real.sqrt_pos.mp (hτ.trans_le hs)
    have hsquare : (W m ^ (-B) / (2 * R)) ^ 2 ≤ q r := by
      simpa only [Real.sq_sqrt hqpos.le] using pow_le_pow_left₀ hτ.le hs 2
    have hpow : W m ^ (-(2 * B)) = (W m ^ (-B)) ^ 2 := by
      rw [pow_two, ← Real.rpow_add (hW₀ m)]
      congr 1
      ring
    have hscale : lam * W m ^ (-(2 * B)) = (W m ^ (-B) / (2 * R)) ^ 2 := by
      rw [hpow, div_pow]
      dsimp only [lam]
      field_simp [(mul_pos (by norm_num : (0 : ℝ) < 2) hR).ne'] <;> ring
    exact hscale.trans_le hsquare
  obtain ⟨A, P, hA, hP, hb⟩ := norm_iteratedFDeriv_sqrt_polynomial_bound
    W hW U hU (fun _ => q) hq hlam (mul_nonneg (by norm_num) hB.le) hqlower hqb n
  refine ⟨A, P, hA, hP, fun m r hr => ?_⟩
  have h := hb m r hr
  change ‖iteratedFDeriv ℝ n (fun t => Real.sqrt (q t)) r‖ ≤ A * W m ^ P at h
  rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  exact h

end ContinuousFlexibility.Statements
