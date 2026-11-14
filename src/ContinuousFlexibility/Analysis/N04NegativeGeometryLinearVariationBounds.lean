module

public import ContinuousFlexibility.Analysis.ExpPolynomialEnvelope
public import ContinuousFlexibility.Analysis.N01cFlowVariation
public import ContinuousFlexibility.Analysis.ParametricSpatialIntegralJets
public import ContinuousFlexibility.Analysis.PointwiseProductMaterialJets
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Spatial jet bounds for actual linear flow variations

The variation-of-constants formula is applied to the actual scalar ODE.
Its spatial jets are estimated before enlarging their derivative orders.
The common geometric scale therefore occurs to precisely the spatial
order, while the forcing amplitude occurs once. In particular, an
external sampled-height factor in the forcing survives unchanged.

The exponential depends on an integral of the zeroth coefficient only.
Higher coefficient jets contribute polynomially. No high-order norm is
assumed small, and the finite-order constant is chosen before the
coefficient functions, the forcing, and their amplitudes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff BigOperators

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- The partition formula preserves a geometric weight at its exact
derivative order. The exponent value enters only through its amplitude. -/
theorem n04NegativeGeometry_exp_weighted_prefix (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M A ρ : ℝ}, 1 ≤ M → 0 ≤ A → 0 ≤ ρ →
      ∀ (f : Q → ℝ) (x : Q), ContDiffAt ℝ ∞ f x → Real.exp (f x) ≤ A →
      (∀ k, 1 ≤ k → k ≤ N → ‖iteratedFDeriv ℝ k f x‖ ≤ M * ρ ^ k) →
      ∀ k, k ≤ N →
        ‖iteratedFDeriv ℝ k (fun y => Real.exp (f y)) x‖ ≤ C * A * M ^ N * ρ ^ k := by
  classical
  let K : ℕ → ℝ := fun k => Fintype.card (OrderedFinpartition k)
  have hK (k : ℕ) : 0 ≤ K k := Nat.cast_nonneg _
  let C : ℝ := 1 + ∑ j ∈ Finset.range (N + 1), K j
  have hC : 1 ≤ C := by
    have hp : 0 ≤ ∑ j ∈ Finset.range (N + 1), K j :=
      Finset.sum_nonneg fun j _ => hK j
    dsimp only [C]
    linarith only [hp]
  refine ⟨C, hC, ?_⟩
  intro M A ρ hM hA hρ f x hf hexp hraw k hk
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hout (j : ℕ) : ‖iteratedFDeriv ℝ j Real.exp (f x)‖ ≤ A := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hexp
  have hterm (π : OrderedFinpartition k) :
      ‖iteratedFDeriv ℝ π.length Real.exp (f x)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) f x‖ ≤ A * M ^ N * ρ ^ k := by
    have hsum : ∑ j, π.partSize j = k := by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using
        Fintype.card_congr π.equivSigma
    have hprod : (∏ j, ‖iteratedFDeriv ℝ (π.partSize j) f x‖) ≤
        M ^ π.length * ρ ^ k := by
      calc
        _ ≤ ∏ j : Fin π.length, M * ρ ^ π.partSize j :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            (fun j _ => hraw (π.partSize j) (π.partSize_pos j)
              ((π.partSize_le j).trans hk))
        _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, Finset.prod_pow_eq_pow_sum, hsum]
    calc
      _ ≤ A * (M ^ π.length * ρ ^ k) :=
        mul_le_mul (hout π.length) hprod
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) hA
      _ ≤ A * (M ^ N * ρ ^ k) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hM (π.length_le.trans hk)) (pow_nonneg hρ k)) hA
      _ = _ := (mul_assoc _ _ _).symm
  have hcard : K k ≤ C := by
    have hm : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun j _ => hK j) hm).trans
      (le_add_of_nonneg_left zero_le_one)
  calc
    _ ≤ ∑ π : OrderedFinpartition k,
        ‖iteratedFDeriv ℝ π.length Real.exp (f x)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) f x‖ :=
      norm_iteratedFDeriv_comp_le_partition_sum Real.contDiff_exp.contDiffAt hf k
    _ ≤ ∑ _π : OrderedFinpartition k, A * M ^ N * ρ ^ k :=
      Finset.sum_le_sum fun π _ => hterm π
    _ = K k * (A * M ^ N * ρ ^ k) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K]
    _ ≤ C * (A * M ^ N * ρ ^ k) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (mul_nonneg hA (pow_nonneg hM0 N)) (pow_nonneg hρ k))
    _ = C * A * M ^ N * ρ ^ k := by ring

/-- The two amplitudes occur once, and the common spatial scale keeps
the actual total derivative order. -/
theorem n04NegativeGeometry_weighted_product_jet_le
    {f g : Q → ℝ} {x : Q} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) {A B ρ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ) {k N : ℕ} (hk : k ≤ N)
    (hfj : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ A * ρ ^ j)
    (hgj : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g x‖ ≤ B * ρ ^ j) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ N * A * B * ρ ^ k := by
  have hchoose : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  have hpower : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hk
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (k - j) g x‖ :=
      norm_iteratedFDeriv_mul_le_at hf hg k
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (A * B * ρ ^ k) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      calc
        _ ≤ (k.choose j : ℝ) * (A * ρ ^ j) * (B * ρ ^ (k - j)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (hfj j hjk) (Nat.cast_nonneg _))
            (hgj (k - j) (Nat.sub_le k j)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hA (pow_nonneg hρ j)))
        _ = (k.choose j : ℝ) * (A * B * (ρ ^ j * ρ ^ (k - j))) := by ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjk]
    _ = (2 : ℝ) ^ k * (A * B * ρ ^ k) := by rw [← Finset.sum_mul, hchoose]
    _ ≤ (2 : ℝ) ^ N * (A * B * ρ ^ k) :=
      mul_le_mul_of_nonneg_right hpower (mul_nonneg (mul_nonneg hA hB) (pow_nonneg hρ k))
    _ = _ := by ring

variable [FiniteDimensional ℝ Q]

private theorem spatial_integral_jet_le
    {f : Q × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : Q) (k : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ k (fun y : Q => f (y, t)) x‖ ≤ A)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖iteratedFDeriv ℝ k (fun y : Q => ∫ r in (0 : ℝ)..t, f (y, r)) x‖ ≤ A := by
  have hI := parametricIntervalIntegral_contDiff_and_iteratedFDeriv f
    (fun r => hf.comp (contDiff_id.prodMk contDiff_const))
    (fun n => (contDiff_parametricSpatialJet hf n).continuous) 0 t
  rw [hI.2 k x]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := A)
    (f := fun r => parametricSpatialJet f k (x, r)) (fun r hr => by
      have hr' : r ∈ Icc (0 : ℝ) t := by
        simpa only [uIcc_of_le ht.1] using uIoc_subset_uIcc hr
      exact hbound r ⟨hr'.1, hr'.2.trans ht.2⟩)
  have hb' : ‖∫ r in (0 : ℝ)..t, parametricSpatialJet f k (x, r)‖ ≤ A * t := by
    simpa only [sub_zero, abs_of_nonneg ht.1] using hb
  exact hb'.trans (mul_le_of_le_one_right hA ht.2)

/-- The explicit integral solution preserves one forcing amplitude and
the exact spatial scale. Its exponential cost uses only the primitive
of the zeroth coefficient. -/
theorem n04NegativeGeometry_variationIntegral_weighted_prefix (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {κ F : Q × ℝ → ℝ},
      ContDiff ℝ ∞ κ → ContDiff ℝ ∞ F → ∀ (x : Q) {M W ρ Λ : ℝ},
      1 ≤ M → 0 ≤ W → 0 ≤ ρ →
      (∀ t ∈ Icc (0 : ℝ) 1, |∫ r in (0 : ℝ)..t, κ (x, r)| ≤ Λ) →
      (∀ j, 1 ≤ j → j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : Q => κ (y, t)) x‖ ≤ M * ρ ^ j) →
      (∀ j, j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : Q => F (y, t)) x‖ ≤ W * M * ρ ^ j) →
      ∀ k, k ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ k (fun y : Q =>
          Real.exp (∫ r in (0 : ℝ)..t, κ (y, r)) *
            ∫ s in (0 : ℝ)..t,
              Real.exp (-(∫ r in (0 : ℝ)..s, κ (y, r))) * F (y, s)) x‖ ≤
          C * Real.exp (2 * Λ) * W * M ^ (2 * N + 1) * ρ ^ k := by
  obtain ⟨C, hC, hExp⟩ := n04NegativeGeometry_exp_weighted_prefix (Q := Q) N
  refine ⟨((2 : ℝ) ^ N * C) ^ 2,
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hC), ?_⟩
  intro κ F hκ hF x M W ρ Λ hM hW hρ hamp hκj hFj
  let P : Q × ℝ → ℝ := fun z => ∫ r in (0 : ℝ)..z.2, κ (z.1, r)
  have hP : ContDiff ℝ ∞ P := contDiff_parametric_primitive hκ 0
  have hPs (t : ℝ) : ContDiff ℝ ∞ (fun y : Q => P (y, t)) :=
    hP.comp (contDiff_id.prodMk contDiff_const)
  have hPj (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ j (fun y : Q => P (y, t)) x‖ ≤ M * ρ ^ j :=
    spatial_integral_jet_le hκ x j
      (mul_nonneg (zero_le_one.trans hM) (pow_nonneg hρ j)) (hκj j hj hjN) ht
  let A : ℝ := C * Real.exp Λ * M ^ N
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (zero_le_one.trans hC) (Real.exp_pos Λ).le)
    (pow_nonneg (zero_le_one.trans hM) N)
  have hplus (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun y : Q => Real.exp (P (y, t))) x‖ ≤ A * ρ ^ j := by
    exact hExp hM (Real.exp_pos Λ).le hρ (fun y => P (y, t)) x
      (hPs t).contDiffAt (Real.exp_le_exp.mpr (le_abs_self _ |>.trans (hamp t ht)))
      (fun i hi hiN => hPj i hi hiN t ht) j hj
  have hminus (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun y : Q => Real.exp (-P (y, t))) x‖ ≤ A * ρ ^ j := by
    apply hExp hM (Real.exp_pos Λ).le hρ (fun y => -P (y, t)) x (hPs t).neg.contDiffAt
      (Real.exp_le_exp.mpr ((neg_le_abs _).trans (hamp t ht)))
      (fun i hi hiN => ?_) j hj
    have he : ‖iteratedFDeriv ℝ i (fun y : Q => -P (y, t)) x‖ =
        ‖iteratedFDeriv ℝ i (fun y : Q => P (y, t)) x‖ := by
      simpa only [Pi.neg_def, norm_neg] using congrArg norm
        (iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := i)
          (f := fun y : Q => P (y, t)) (x := x))
    rw [he]
    exact hPj i hi hiN t ht
  let G : Q × ℝ → ℝ := fun z => Real.exp (-P z) * F z
  have hG : ContDiff ℝ ∞ G := (Real.contDiff_exp.comp hP.neg).mul hF
  let B : ℝ := (2 : ℝ) ^ N * A * (W * M)
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (pow_nonneg (by norm_num) N) hA)
    (mul_nonneg hW (zero_le_one.trans hM))
  have hGj (j : ℕ) (hj : j ≤ N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ j (fun y : Q => G (y, t)) x‖ ≤ B * ρ ^ j :=
    n04NegativeGeometry_weighted_product_jet_le
      (Real.contDiff_exp.comp (hPs t).neg).contDiffAt
      (hF.comp (contDiff_id.prodMk contDiff_const)).contDiffAt
      hA (mul_nonneg hW (zero_le_one.trans hM)) hρ hj
      (fun i hi => hminus t ht i (hi.trans hj))
      (fun i hi => hFj i (hi.trans hj) t ht)
  have hI (t : ℝ) : ContDiff ℝ ∞ (fun y : Q => ∫ s in (0 : ℝ)..t, G (y, s)) :=
    contDiff_parametric_intervalIntegral hG 0 t
  have hIj (j : ℕ) (hj : j ≤ N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ j (fun y : Q => ∫ s in (0 : ℝ)..t, G (y, s)) x‖ ≤ B * ρ ^ j :=
    spatial_integral_jet_le hG x j (mul_nonneg hB (pow_nonneg hρ j)) (hGj j hj) ht
  intro k hk t ht
  have hb := n04NegativeGeometry_weighted_product_jet_le
    (Real.contDiff_exp.comp (hPs t)).contDiffAt (hI t).contDiffAt hA hB hρ hk
    (fun j hj => hplus t ht j (hj.trans hk))
    (fun j hj => hIj j (hj.trans hk) t ht)
  change ‖iteratedFDeriv ℝ k (fun y : Q => Real.exp (P (y, t)) *
    ∫ s in (0 : ℝ)..t, G (y, s)) x‖ ≤ _
  refine hb.trans_eq ?_
  have hpower : M ^ (2 * N + 1) = (M ^ N * M ^ N) * M := by
    rw [show 2 * N + 1 = N + N + 1 by omega, pow_succ, pow_add]
  have hexp : Real.exp (2 * Λ) = Real.exp Λ * Real.exp Λ := by
    rw [two_mul, Real.exp_add]
  rw [hpower, hexp]
  dsimp only [A, B]
  ring

/-- This is a bound on the actual solution of the original linear
variation equation, including every mixed spatial derivative. No jet
equation or derivative of the solution is assumed. -/
theorem n04NegativeGeometry_linearVariation_weighted_prefix (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {κ F : Q × ℝ → ℝ} {w : Q → ℝ → ℝ},
      ContDiff ℝ ∞ κ → ContDiff ℝ ∞ F →
      (∀ y, ContinuousOn (w y) (Icc (0 : ℝ) 1)) →
      (∀ y, w y 0 = 0) →
      (∀ y t, t ∈ Ioo (0 : ℝ) 1 →
        HasDerivAt (w y) (κ (y, t) * w y t + F (y, t)) t) →
      ∀ (x : Q) {M W ρ Λ : ℝ}, 1 ≤ M → 0 ≤ W → 0 ≤ ρ →
      (∀ t ∈ Icc (0 : ℝ) 1, |∫ r in (0 : ℝ)..t, κ (x, r)| ≤ Λ) →
      (∀ j, 1 ≤ j → j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : Q => κ (y, t)) x‖ ≤ M * ρ ^ j) →
      (∀ j, j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : Q => F (y, t)) x‖ ≤ W * M * ρ ^ j) →
      ∀ k, k ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ k (fun y : Q => w y t) x‖ ≤
          C * Real.exp (2 * Λ) * W * M ^ (2 * N + 1) * ρ ^ k := by
  obtain ⟨C, hC, hbound⟩ :=
    n04NegativeGeometry_variationIntegral_weighted_prefix (Q := Q) N
  refine ⟨C, hC, ?_⟩
  intro κ F w hκ hF hw hzero hderiv x M W ρ Λ hM hW hρ hamp hκj hFj k hk t ht
  have heq : (fun y : Q => w y t) = fun y : Q =>
      Real.exp (∫ r in (0 : ℝ)..t, κ (y, r)) *
        ∫ s in (0 : ℝ)..t,
          Real.exp (-(∫ r in (0 : ℝ)..s, κ (y, r))) * F (y, s) := by
    funext y
    have h := scalar_inhomogeneousODE_eq_exp_mul ht.1
      (hκ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      ((hw y).mono (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => hderiv y s ⟨hs.1, hs.2.trans_le ht.2⟩)
    simpa only [hzero y, zero_add, Function.comp_apply, id_eq] using h
  rw [heq]
  exact hbound hκ hF x hM hW hρ hamp hκj hFj k hk t ht

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_exp_weighted_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_exp_weighted_prefix

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_linearVariation_weighted_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_linearVariation_weighted_prefix
