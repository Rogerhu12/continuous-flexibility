module

public import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Algebra of the actual spatial-parameter bounds

The mixed Leibniz formula is local on the original open annulus.
Every factor retains its assigned spatial order until its product is
formed. Thus the interpolation indices are unchanged by addition and
multiplication.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The actual mixed Leibniz identity needs smoothness only on the open
spatial domain. -/
theorem mixedDerivative_mul_on_open
    {Ω : Set PolarPoint} {f g : PolarPoint → ℝ} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (a b : ℕ) {q : PolarPoint} (hq : q ∈ Ω) :
    mixedDerivative a b (fun p => f p * g p) q =
      ∑ i : Fin (a + 1), ∑ j : Fin (b + 1),
        (a.choose i.val : ℝ) * (b.choose j.val : ℝ) *
          (mixedDerivative i.val j.val f q *
            mixedDerivative (a - i.val) (b - j.val) g q) := by
  have hnear : ∀ᶠ r in 𝓝 q.1, (r, q.2) ∈ Ω :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hΩ.mem_nhds hq)
  have hfr (j : ℕ) : ContDiffAt ℝ ∞
      (fun r => iteratedDeriv j (fun θ => f (r, θ)) q.2) q.1 := by
    have h := ((contDiffOn_mixedDerivative hΩ hf 0 j).contDiffAt
      (hΩ.mem_nhds hq)).comp q.1 (contDiffAt_id.prodMk contDiffAt_const)
    simpa only [Function.comp_def, id_eq, mixedDerivative, iteratedDeriv_zero] using h
  have hgr (j : ℕ) : ContDiffAt ℝ ∞
      (fun r => iteratedDeriv j (fun θ => g (r, θ)) q.2) q.1 := by
    have h := ((contDiffOn_mixedDerivative hΩ hg 0 j).contDiffAt
      (hΩ.mem_nhds hq)).comp q.1 (contDiffAt_id.prodMk contDiffAt_const)
    simpa only [Function.comp_def, id_eq, mixedDerivative, iteratedDeriv_zero] using h
  have he : (fun r => iteratedDeriv b (fun θ => f (r, θ) * g (r, θ)) q.2) =ᶠ[𝓝 q.1]
      (fun r => ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) *
        (iteratedDeriv j (fun θ => f (r, θ)) q.2 *
          iteratedDeriv (b - j) (fun θ => g (r, θ)) q.2)) := by
    filter_upwards [hnear] with r hr
    have hft := (hf.contDiffAt (hΩ.mem_nhds hr)).comp q.2
      (contDiffAt_const.prodMk contDiffAt_id)
    have hgt := (hg.contDiffAt (hΩ.mem_nhds hr)).comp q.2
      (contDiffAt_const.prodMk contDiffAt_id)
    simpa only [Function.comp_def, id_eq, mul_assoc] using
      iteratedDeriv_fun_mul (hft.of_le (by simp)) (hgt.of_le (by simp))
  have hfin (F : ℕ → ℕ → ℝ) :
      (∑ i : Fin (a + 1), ∑ j : Fin (b + 1), F i.val j.val) =
        ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), F i j := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      ∑ j : Fin (b + 1), F i j.val) (a + 1)]
    exact Finset.sum_congr rfl (fun i _ =>
      Fin.sum_univ_eq_sum_range (F i) (b + 1))
  rw [hfin (fun i j => (a.choose i : ℝ) * (b.choose j : ℝ) *
    (mixedDerivative i j f q * mixedDerivative (a - i) (b - j) g q))]
  unfold mixedDerivative
  rw [he.iteratedDeriv_eq a,
    iteratedDeriv_fun_sum (fun j _ =>
      (contDiffAt_const.mul ((hfr j).mul (hgr (b - j)))).of_le (by simp))]
  simp_rw [iteratedDeriv_const_mul_field]
  have hh (j : ℕ) :
      iteratedDeriv a
        (fun r => iteratedDeriv j (fun θ => f (r, θ)) q.2 *
          iteratedDeriv (b - j) (fun θ => g (r, θ)) q.2) q.1 =
        ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) *
          iteratedDeriv i (fun r => iteratedDeriv j (fun θ => f (r, θ)) q.2) q.1 *
          iteratedDeriv (a - i)
            (fun r => iteratedDeriv (b - j) (fun θ => g (r, θ)) q.2) q.1 :=
    iteratedDeriv_fun_mul ((hfr j).of_le (by simp)) ((hgr (b - j)).of_le (by simp))
  simp_rw [hh, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mixedDerivative_add_on_open
    {Ω : Set PolarPoint} {f g : PolarPoint → ℝ} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (a b : ℕ) {q : PolarPoint} (hq : q ∈ Ω) :
    mixedDerivative a b (fun p => f p + g p) q =
      mixedDerivative a b f q + mixedDerivative a b g q := by
  rw [mixedDerivative_eq_iteratedFDeriv_word hΩ (hf.add hg) a b hq,
    mixedDerivative_eq_iteratedFDeriv_word hΩ hf a b hq,
    mixedDerivative_eq_iteratedFDeriv_word hΩ hg a b hq]
  have h : iteratedFDeriv ℝ (a + b) (fun p => f p + g p) q =
      iteratedFDeriv ℝ (a + b) f q + iteratedFDeriv ℝ (a + b) g q := by
    simpa only [Pi.add_def] using iteratedFDeriv_add_apply (i := a + b)
      ((hf.contDiffAt (hΩ.mem_nhds hq)).of_le (by simp))
      ((hg.contDiffAt (hΩ.mem_nhds hq)).of_le (by simp))
  simpa only [add_apply] using congrArg (fun A : PolarPoint [×(a + b)]→L[ℝ] ℝ =>
    A (fun i => cylinderBasisVector (cylinderMixedWord a b i))) h

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
  {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}
  {f g : X → PolarPoint → ℝ}

/-- A parameter-independent field costs no height weight at order zero
and has zero genuine jets at every positive parameter order. -/
theorem mixedPowerBounds_parameterIndependent
    (hH : ∀ q ∈ Ω, 0 ≤ H q) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    (f : PolarPoint → ℝ)
    (hf : ∀ s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ Ω,
        ‖mixedDerivative a b f q‖ ≤ C * E q ^ A) :
    MixedPowerBounds p center base loss U Ω H E (fun _ => f) := by
  intro K s
  obtain ⟨C, A, hC, hA, hb⟩ := hf s
  refine ⟨C, A, hC, hA, ?_⟩
  intro k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  by_cases hk0 : k = 0
  · subst k
    rw [smoothDirections_D_zero_apply J hx v]
    have ht := Real.one_le_rpow hR (spatialOrder_fraction_nonneg (a + b) s)
    simpa only [parameterHeightWeight, ite_true, mul_one] using
      (hb a b hab q hq).trans (le_mul_of_one_le_right
        (mul_nonneg (zero_le_one.trans hC)
          (Real.rpow_nonneg (zero_le_one.trans (hE q hq)) _)) ht)
  · rw [smoothDirections_D_constant J (Nat.pos_of_ne_zero hk0) hx v, norm_zero]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (zero_le_one.trans hC)
        (Real.rpow_nonneg (zero_le_one.trans (hE q hq)) _))
      (parameterHeightWeight_nonneg (hH q hq) k))
      (Real.rpow_nonneg (zero_le_one.trans hR) _)

theorem MixedPowerBounds.add
    (hf : MixedPowerBounds p center base loss U Ω H E f)
    (hg : MixedPowerBounds p center base loss U Ω H E g)
    (F : MixedJetRegularity U Ω f) (G : MixedJetRegularity U Ω g)
    (hΩ : IsOpen Ω) (hH : ∀ q ∈ Ω, 0 ≤ H q) (hE : ∀ q ∈ Ω, 1 ≤ E q) :
    MixedPowerBounds p center base loss U Ω H E (fun x q => f x q + g x q) := by
  intro K s
  obtain ⟨Cf, Af, hCf, hAf, hfb⟩ := hf K s
  obtain ⟨Cg, Ag, hCg, hAg, hgb⟩ := hg K s
  refine ⟨Cf + Cg, Af + Ag, by linarith, add_nonneg hAf hAg, ?_⟩
  intro k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  let Jf := F.parameter a b q hq
  let Jg := G.parameter a b q hq
  let Jadd := (smoothDirectionsAdd Jf Jg).congr (fun y hy =>
    (mixedDerivative_add_on_open hΩ (F.spatial y hy) (G.spatial y hy) a b hq).symm)
  have heq := HasProjectiveJetsOn.unique J.open_domain
    J.hasProjectiveJetsOn Jadd.hasProjectiveJetsOn k x hx
  have hd : J.D k x v = Jf.D k x v + Jg.D k x v := by
    have hh := congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq
    simpa only [Jadd, SmoothDirections.congr, smoothDirectionsAdd, add_apply] using hh
  have hW : 0 ≤ parameterHeightWeight (H q) k *
      R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
    mul_nonneg (parameterHeightWeight_nonneg (hH q hq) k)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hef := Real.rpow_le_rpow_of_exponent_le (hE q hq)
    (le_add_of_nonneg_right hAg : Af ≤ Af + Ag)
  have heg := Real.rpow_le_rpow_of_exponent_le (hE q hq)
    (le_add_of_nonneg_left hAf : Ag ≤ Af + Ag)
  have hbf := hfb k hk a b hab q hq Jf x hx hlow v hv R hR hhigh hvhigh
  have hbg := hgb k hk a b hab q hq Jg x hx hlow v hv R hR hhigh hvhigh
  rw [hd]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ Cf * E q ^ Af * parameterHeightWeight (H q) k *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) +
        Cg * E q ^ Ag * parameterHeightWeight (H q) k *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := add_le_add hbf hbg
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hef (zero_le_one.trans hCf)) hW
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heg (zero_le_one.trans hCg)) hW
      nlinarith only [h1, h2]

/-- The total coefficient in the two-coordinate Leibniz formula. -/
theorem mixedLeibniz_coefficient_sum (a b : ℕ) :
    (∑ i : Fin (a + 1), ∑ j : Fin (b + 1),
      (a.choose i.val : ℝ) * (b.choose j.val : ℝ)) = (2 : ℝ) ^ (a + b) := by
  have hsum (n : ℕ) : (∑ i : Fin (n + 1), (n.choose i.val : ℝ)) = (2 : ℝ) ^ n := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (n.choose i : ℝ)) (n + 1)]
    exact_mod_cast Nat.sum_range_choose n
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, hsum, hsum, pow_add]

/-- Multiplication preserves the original interpolation indices. -/
theorem MixedPowerBounds.mul
    (hf : MixedPowerBounds p center base loss U Ω H E f)
    (hg : MixedPowerBounds p center base loss U Ω H E g)
    (F : MixedJetRegularity U Ω f) (G : MixedJetRegularity U Ω g)
    (hΩ : IsOpen Ω) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    {RH : ℝ} (hH : ∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH) :
    MixedPowerBounds p center base loss U Ω H E (fun x q => f x q * g x q) := by
  classical
  intro K s
  obtain ⟨Cf, Af, hCf, hAf, hfb⟩ := hf K s
  obtain ⟨Cg, Ag, hCg, hAg, hgb⟩ := hg K s
  choose c hc hcb using
    (fun k : Fin (K + 1) => exists_finiteProduct_allParameterJet_bound (X := X) 2 k.val RH)
  let Cp : ℝ := 1 + ∑ k : Fin (K + 1), c k
  have hCp : 0 ≤ Cp := add_nonneg zero_le_one
    (Finset.sum_nonneg (fun i _ => (hc i).le))
  have hcCp (k : Fin (K + 1)) : c k ≤ Cp :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ k)).trans
      (le_add_of_nonneg_left zero_le_one)
  let C : ℝ := (2 : ℝ) ^ s * Cp * Cf * Cg
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCp)
      (zero_le_one.trans hCf)) (zero_le_one.trans hCg)
  refine ⟨1 + C, Af + Ag, by linarith, add_nonneg hAf hAg, ?_⟩
  intro k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  have hEpos : 0 < E q := zero_lt_one.trans_le (hE q hq)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let I := Fin (a + 1) × Fin (b + 1)
  let coeff : I → ℝ := fun t => (a.choose t.1.val : ℝ) * (b.choose t.2.val : ℝ)
  let terms : I → X → ℝ := fun t y =>
    mixedDerivative t.1.val t.2.val (f y) q *
      mixedDerivative (a - t.1.val) (b - t.2.val) (g y) q
  let JT : ∀ t, SmoothDirections U (terms t) := fun t =>
    smoothDirections_realMul (F.parameter t.1.val t.2.val q hq)
      (G.parameter (a - t.1.val) (b - t.2.val) q hq)
  let W : ℝ := E q ^ (Af + Ag) * parameterHeightWeight (H q) k *
    R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hW : 0 ≤ W := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hEpos.le _)
      (parameterHeightWeight_nonneg (hH q hq).1 k))
    (Real.rpow_nonneg hRpos.le _)
  have hterm (t : I) : ‖(JT t).D k x v‖ ≤ Cp * Cf * Cg * W := by
    have hi : t.1.val ≤ a := Nat.le_of_lt_succ t.1.isLt
    have hj : t.2.val ≤ b := Nat.le_of_lt_succ t.2.isLt
    have hfs : t.1.val + t.2.val ≤ s := by omega
    have hgs : (a - t.1.val) + (b - t.2.val) ≤ s := by omega
    have htotal : (t.1.val + t.2.val) + ((a - t.1.val) + (b - t.2.val)) = a + b := by omega
    let f₀ : X → ℝ := fun y => mixedDerivative t.1.val t.2.val (f y) q
    let g₀ : X → ℝ := fun y => mixedDerivative (a - t.1.val) (b - t.2.val) (g y) q
    let Jf := F.parameter t.1.val t.2.val q hq
    let Jg := G.parameter (a - t.1.val) (b - t.2.val) q hq
    let Bf : ℝ := Cf * E q ^ Af *
      R ^ (((t.1.val + t.2.val : ℕ) : ℝ) / ((s : ℝ) + 1))
    let Bg : ℝ := Cg * E q ^ Ag *
      R ^ ((((a - t.1.val) + (b - t.2.val) : ℕ) : ℝ) / ((s : ℝ) + 1))
    have hBf : 0 < Bf := mul_pos
      (mul_pos (zero_lt_one.trans_le hCf) (Real.rpow_pos_of_pos hEpos _))
      (Real.rpow_pos_of_pos hRpos _)
    have hBg : 0 < Bg := mul_pos
      (mul_pos (zero_lt_one.trans_le hCg) (Real.rpow_pos_of_pos hEpos _))
      (Real.rpow_pos_of_pos hRpos _)
    have hbasef : ‖f₀ x‖ ≤ Bf := by
      have hh := hfb 0 (Nat.zero_le K) t.1.val t.2.val hfs q hq Jf x hx hlow
        Fin.elim0 (fun i => i.elim0) R hR hhigh (fun i => i.elim0)
      simpa only [smoothDirections_D_zero_apply Jf hx, parameterHeightWeight,
        ite_true, mul_one] using hh
    have hbaseg : ‖g₀ x‖ ≤ Bg := by
      have hh := hgb 0 (Nat.zero_le K) (a - t.1.val) (b - t.2.val) hgs q hq Jg x hx hlow
        Fin.elim0 (fun i => i.elim0) R hR hhigh (fun i => i.elim0)
      simpa only [smoothDirections_D_zero_apply Jg hx, parameterHeightWeight,
        ite_true, mul_one] using hh
    have hjetf (d : OrderedFinpartition k) (j : Fin d.length) :
        ‖Jf.D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H q * Bf := by
      have hh := hfb (d.partSize j) ((d.partSize_le j).trans hk)
        t.1.val t.2.val hfs q hq Jf x hx hlow (v ∘ d.emb j)
        (fun i => hv _) R hR hhigh (fun i => hvhigh _)
      simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos j)),
        Bf, mul_assoc, mul_left_comm, mul_comm] using hh
    have hjetg (d : OrderedFinpartition k) (j : Fin d.length) :
        ‖Jg.D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H q * Bg := by
      have hh := hgb (d.partSize j) ((d.partSize_le j).trans hk)
        (a - t.1.val) (b - t.2.val) hgs q hq Jg x hx hlow (v ∘ d.emb j)
        (fun i => hv _) R hR hhigh (fun i => hvhigh _)
      simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos j)),
        Bg, mul_assoc, mul_left_comm, mul_comm] using hh
    let ff : Fin 2 → X → ℝ := Fin.cases f₀ (fun _ => g₀)
    let JJ : ∀ i, SmoothDirections U (ff i) := Fin.cases Jf (fun _ => Jg)
    let BB : Fin 2 → ℝ := Fin.cases Bf (fun _ => Bg)
    have hff₀ : ff 0 = f₀ := by simp only [ff, Fin.cases_zero]
    have hff₁ : ff 1 = g₀ := by
      rw [show (1 : Fin 2) = (0 : Fin 1).succ from by decide]
      simp only [ff, Fin.cases_succ]
    let JP : SmoothDirections U (fun y => ∏ i, ff i y) :=
      (JT t).congr (fun y _ => by
        simp only [Fin.prod_univ_two, hff₀, hff₁, terms, f₀, g₀])
    have hBB : ∀ i : Fin 2, 0 < BB i := Fin.cases hBf (fun _ => hBg)
    have hBP := hcb ⟨k, Nat.lt_succ_of_le hk⟩ JJ JP x hx (H q)
      (hH q hq).1 (hH q hq).2 BB hBB
      (Fin.cases hbasef (fun _ => hbaseg)) v
      (Fin.cases hjetf (fun _ => hjetg))
    have hprod : (∏ i, BB i) =
        Cf * Cg * E q ^ (Af + Ag) *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      simp only [Fin.prod_univ_two, BB, Fin.cases_zero, Fin.cases_succ]
      calc
        Bf * Bg = (Cf * Cg) * (E q ^ Af * E q ^ Ag) *
            (R ^ (((t.1.val + t.2.val : ℕ) : ℝ) / ((s : ℝ) + 1)) *
              R ^ ((((a - t.1.val) + (b - t.2.val) : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
          dsimp only [Bf, Bg]
          ring
        _ = _ := by rw [← Real.rpow_add hEpos, rpow_spatialOrder_mul hRpos, htotal]
    have hBprod : 0 ≤ ∏ i, BB i :=
      Finset.prod_nonneg (fun i _ => (hBB i).le)
    calc
      ‖(JT t).D k x v‖ ≤ c ⟨k, Nat.lt_succ_of_le hk⟩ *
          parameterHeightWeight (H q) k * ∏ i, BB i := hBP
      _ ≤ Cp * parameterHeightWeight (H q) k * ∏ i, BB i :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcCp _) (parameterHeightWeight_nonneg (hH q hq).1 k))
          hBprod
      _ = Cp * Cf * Cg * W := by rw [hprod]; dsimp only [W]; ring
  have hsplit (F : I → ℝ) : (∑ t : I, F t) =
      ∑ i : Fin (a + 1), ∑ j : Fin (b + 1), F (i, j) :=
    Fintype.sum_prod_type (fun t : Fin (a + 1) × Fin (b + 1) => F t)
  have hd := smoothDirections_D_eq_linearCombination J JT coeff
    (fun y hy => by
      rw [hsplit (fun t => coeff t * terms t y)]
      exact mixedDerivative_mul_on_open hΩ (F.spatial y hy) (G.spatial y hy) a b hq)
    k hx v
  have hcoeff (t : I) : 0 ≤ coeff t :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnormCoeff (t : I) : ‖coeff t‖ = coeff t := Real.norm_of_nonneg (hcoeff t)
  have hsum : (∑ t : I, coeff t) = (2 : ℝ) ^ (a + b) := by
    rw [hsplit coeff]
    exact mixedLeibniz_coefficient_sum a b
  have hpow : (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ s :=
    pow_le_pow_right₀ (by norm_num) hab
  calc
    ‖J.D k x v‖ ≤ ∑ t, coeff t * ‖(JT t).D k x v‖ := by
      rw [hd]
      simpa only [norm_mul, hnormCoeff] using
        norm_sum_le (Finset.univ : Finset I) (fun t : I => coeff t * (JT t).D k x v)
    _ ≤ ∑ t, coeff t * (Cp * Cf * Cg * W) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hterm t) (hcoeff t))
    _ = (2 : ℝ) ^ (a + b) * (Cp * Cf * Cg * W) := by rw [← Finset.sum_mul, hsum]
    _ ≤ C * W := by
      have hh := mul_le_mul_of_nonneg_right hpow
        (mul_nonneg (mul_nonneg (mul_nonneg hCp (zero_le_one.trans hCf))
          (zero_le_one.trans hCg)) hW)
      simpa only [C, mul_assoc] using hh
    _ ≤ (1 + C) * E q ^ (Af + Ag) * parameterHeightWeight (H q) k *
        R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      have hh := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left zero_le_one : C ≤ 1 + C) hW
      simpa only [W, mul_assoc] using hh


end ContinuousFlexibility.Analysis
