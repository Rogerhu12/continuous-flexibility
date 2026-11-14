module

public import ContinuousFlexibility.Analysis.N01cPhysicalHeightJets

/-!
# Ordinary physical height jets with the actual E0 coefficient weight

Restoring the factor `H^γ` costs a finite Leibniz sum whose constants are
uniform in the material coordinate.  The ordinary radial expansion then
costs its stated power of `E0`.  The height grading loses exactly two
orders, independently of the requested physical derivative order.

The envelope `M` is not used to enlarge the coefficient weight.  Finite
collections of `E0` powers can be combined because `E0 ≥ 1` near the
endpoints and `E0` is positive and continuous on the compact middle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem one_le_materialE0_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ materialE0 x := by
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hlog : 0 ≤ materialLogFactor x :=
    Real.log_nonneg (he.trans (le_add_of_nonneg_right hx))
  apply Real.one_le_exp_iff.mpr
  exact add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg hx _) hlog)

/-- Increasing an `E0` exponent costs only a spatially uniform constant.
This uses the actual endpoint formula and the compact middle; it does not
assume the interior weight is at least one. -/
theorem materialE0_rpow_le_of_exponent_le
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {A B : ℝ} (hAB : A ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b, T.E0 r ^ A ≤ K * T.E0 r ^ B := by
  have hdata := hT
  obtain ⟨hs, hp, _, _, _, _, _, _, _, _, hends, _⟩ := hdata
  obtain ⟨d0, δ, _, hδ, _, hL, hR⟩ := hends
  have hc : ContinuousOn (fun r => T.E0 r ^ (A - B)) (Ioo D.a D.b) :=
    ((hs T.E0 (by simp)).rpow_const_of_ne (fun r hr => (hp r hr).2.2.1.ne')).continuousOn
  have hsub : Icc (D.a + δ) (D.b - δ) ⊆ Ioo D.a D.b :=
    fun _ hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.bddAbove_image (hc.mono hsub)
  let K : ℝ := max 1 K₀
  have hK : 0 ≤ K := zero_le_one.trans (le_max_left _ _)
  refine ⟨K, hK, fun r hr => ?_⟩
  have hratio : T.E0 r ^ (A - B) ≤ K := by
    by_cases hl : r < D.a + δ
    · have he : 1 ≤ T.E0 r := by
        rw [(hL r ⟨hr.1, hl⟩).2.2.1]
        exact one_le_materialE0_of_nonneg (Real.sqrt_nonneg _)
      exact (Real.rpow_le_one_of_one_le_of_nonpos he (sub_nonpos.mpr hAB)).trans
        (le_max_left _ _)
    by_cases hright : D.b - δ < r
    · have he : 1 ≤ T.E0 r := by
        rw [(hR r ⟨hright, hr.2⟩).2.2.1]
        exact one_le_materialE0_of_nonneg (Real.sqrt_nonneg _)
      exact (Real.rpow_le_one_of_one_le_of_nonpos he (sub_nonpos.mpr hAB)).trans
        (le_max_left _ _)
    exact (hK₀ ⟨r, ⟨le_of_not_gt hl, le_of_not_gt hright⟩, rfl⟩).trans
      (le_max_right _ _)
  calc
    T.E0 r ^ A = T.E0 r ^ (A - B) * T.E0 r ^ B := by
      rw [← Real.rpow_add (hp r hr).2.2.1, sub_add_cancel]
    _ ≤ K * T.E0 r ^ B := mul_le_mul_of_nonneg_right hratio
      (Real.rpow_nonneg (hp r hr).2.2.1.le _)

/-- All angular orders share the same material restoration constant at a
fixed radial order. The norm input has exactly two extra derivatives. -/
theorem sobolevModel_materialAngularJet_le_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b s : ℕ, a + b + 2 ≤ s →
      ∀ u : M.Space, ∀ r θ : ℝ, r ∈ Ioo D.a D.b →
        |materialDerivativeIterate T a
          (fun t => iteratedDeriv b (fun φ => M.decode u (t, φ)) θ) r| ≤
          K * T.H r ^ γ * M.grading s u := by
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, hinv, _⟩ := hdata
  have hw (i : Fin (a + 1)) := iteratedDeriv_materialH_rpow_bound hT γ i.val
  choose W hW hWbound using hw
  let K : ℝ := ∑ i : Fin (a + 1), (a.choose i.val : ℝ) * W i * (4 * Real.sqrt Real.pi)
  have hK : 0 ≤ K := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hW i))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  refine ⟨K, hK, fun b s hab u r θ hr => ?_⟩
  have hH : 0 ≤ T.H r ^ γ := Real.rpow_nonneg (hpos r hr).2.1.le _
  rw [materialDerivative_angular_slice_eq_materialJets hT (hM.2.2.2.1 u).1 a b r θ hr]
  calc
    _ ≤ ∑ i : Fin (a + 1),
        |(a.choose i.val : ℝ) *
          iteratedDeriv i.val (fun x => T.H (T.radius x) ^ γ) (T.rho r) *
          mixedDerivative (a - i.val) b (materialPullback T γ (M.decode u))
            (T.rho r, θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (a + 1),
        ((a.choose i.val : ℝ) * W i * (4 * Real.sqrt Real.pi)) *
          T.H r ^ γ * M.grading s u := by
      apply Finset.sum_le_sum
      intro i _
      have hweight := hWbound i (T.rho r)
      rw [hinv r hr] at hweight
      have hjet := sobolevModel_materialPullback_mixedDerivative_le_grading
        hT hM u (a := a - i.val) (b := b) (s := s) (by omega) (T.rho r, θ)
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (a.choose i.val))]
      calc
        _ ≤ (a.choose i.val : ℝ) * (W i * T.H r ^ γ) *
            ((4 * Real.sqrt Real.pi) * M.grading s u) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hweight (Nat.cast_nonneg _)) hjet
            (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hW i) hH))
        _ = _ := by ring
    _ = K * T.H r ^ γ * M.grading s u := by
      simp only [K, Finset.sum_mul]

private theorem smooth_angularJet_slice_for_bound
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (b : ℕ) (θ : ℝ) :
    ContDiffOn ℝ ∞ (fun r => iteratedDeriv b (fun t => f (r, t)) θ)
      (Ioo D.a D.b) := by
  have hs : ContDiff ℝ ∞ (fun r : ℝ => (r, θ)) :=
    contDiff_id.prodMk contDiff_const
  have hm : MapsTo (fun r : ℝ => (r, θ)) (Ioo D.a D.b) (annularOpen D) :=
    fun _ hr => ⟨hr, mem_univ _⟩
  simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero] using
    (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf 0 b).comp hs.contDiffOn hm

/-- The exact ordinary radial expansion retains its `E0` power. The
constant is uniform in the height, spatial point, angular order and any
higher input grading. -/
theorem sobolevModel_physicalJet_le_E0_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M) (a : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ b s : ℕ, a + b + 2 ≤ s →
      ∀ u : M.Space, ∀ p ∈ annularOpen D,
        |mixedDerivative a b (M.decode u) p| ≤
          C * T.E0 p.1 ^ A * T.H p.1 ^ γ * M.grading s u := by
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, _, _, hexpansion, _⟩ := hdata
  obtain ⟨c, _, ⟨C₀, A, hC₀, hA, hc⟩, hformula⟩ := hexpansion a
  have hmaterial (j : Fin (a + 1)) := sobolevModel_materialAngularJet_le_grading hT hM j.val
  choose K hK hKbound using hmaterial
  let C : ℝ := ∑ j : Fin (a + 1), C₀ * K j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => mul_nonneg hC₀ (hK j))
  refine ⟨C, A, hC, hA, fun b s hab u p hp => ?_⟩
  have hE : 0 ≤ T.E0 p.1 ^ A := Real.rpow_nonneg (hpos p.1 hp.1).2.2.1.le _
  change |iteratedDeriv a (fun r => iteratedDeriv b (fun θ => M.decode u (r, θ)) p.2) p.1| ≤ _
  rw [hformula _ (smooth_angularJet_slice_for_bound (hM.2.2.2.1 u).1 b p.2) p.1 hp.1]
  calc
    _ ≤ ∑ j : Fin (a + 1),
        |c j p.1 * materialDerivativeIterate T j.val
          (fun r => iteratedDeriv b (fun θ => M.decode u (r, θ)) p.2) p.1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (a + 1),
        (C₀ * K j) * T.E0 p.1 ^ A * T.H p.1 ^ γ * M.grading s u := by
      apply Finset.sum_le_sum
      intro j _
      have hj : j.val + b + 2 ≤ s := by have := j.isLt; omega
      rw [abs_mul]
      calc
        _ ≤ (C₀ * T.E0 p.1 ^ A) * (K j * T.H p.1 ^ γ * M.grading s u) :=
          mul_le_mul (hc j p.1 hp.1) (hKbound j b s hj u p.1 p.2 hp.1)
            (abs_nonneg _) (mul_nonneg hC₀ hE)
        _ = _ := by ring
    _ = C * T.E0 p.1 ^ A * T.H p.1 ^ γ * M.grading s u := by
      simp only [C, Finset.sum_mul]

/-- One constant and one `E0` power control every ordinary mixed jet of
total order at most `s`. The input order is always `s + 2`. -/
theorem sobolevModel_physicalMixedJets_le_E0_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ u : M.Space, ∀ a b : ℕ, a + b ≤ s →
      ∀ p ∈ annularOpen D,
        |mixedDerivative a b (M.decode u) p| ≤
          C * T.E0 p.1 ^ A * T.H p.1 ^ γ * M.grading (s + 2) u := by
  have hb (j : Fin (s + 1)) := sobolevModel_physicalJet_le_E0_grading hT hM j.val
  choose C A hC hA hbound using hb
  let B : ℝ := ∑ j : Fin (s + 1), A j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hA j)
  have hAB (j : Fin (s + 1)) : A j ≤ B :=
    Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ j)
  have hk (j : Fin (s + 1)) := materialE0_rpow_le_of_exponent_le hT (hAB j)
  choose K hK hKbound using hk
  let L : ℝ := ∑ j : Fin (s + 1), C j * K j
  have hL : 0 ≤ L := Finset.sum_nonneg (fun j _ => mul_nonneg (hC j) (hK j))
  refine ⟨L, B, hL, hB, fun u a b hab p hp => ?_⟩
  let j : Fin (s + 1) := ⟨a, by omega⟩
  have hE : 0 ≤ T.E0 p.1 ^ B := Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.2.1.le _
  have hH : 0 ≤ T.H p.1 ^ γ := Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.1.le _
  have hG : 0 ≤ M.grading (s + 2) u := apply_nonneg _ _
  have hj : C j * K j ≤ L :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hC i) (hK i)) (Finset.mem_univ j)
  calc
    |mixedDerivative a b (M.decode u) p| ≤
        C j * T.E0 p.1 ^ A j * T.H p.1 ^ γ * M.grading (s + 2) u :=
      hbound j b (s + 2) (by dsimp [j]; omega) u p hp
    _ ≤ C j * (K j * T.E0 p.1 ^ B) * T.H p.1 ^ γ * M.grading (s + 2) u :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hKbound j p.1 hp.1) (hC j)) hH) hG
    _ = (C j * K j) * T.E0 p.1 ^ B * T.H p.1 ^ γ * M.grading (s + 2) u := by ring
    _ ≤ L * T.E0 p.1 ^ B * T.H p.1 ^ γ * M.grading (s + 2) u :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj hE) hH) hG

end ContinuousFlexibility.Statements
