module

public import ContinuousFlexibility.Analysis.N01cMixedPowerAlgebra
public import ContinuousFlexibility.Analysis.N01cHeightParameterJets

/-!
# Endpoint weights in the actual spatial-parameter product formula

The radial endpoint power is assigned to the two genuine spatial jets
before multiplication. The finite-dimensional parameter product theorem
is then applied to their scalar rescalings. Every spatial order remains
in its original interpolation power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Uniform endpoint-weighted bounds before multilinear normalization.
The index can be the actual negative component; all constants precede it. -/
def EndpointMixedPowerBounds (p : ℕ → Seminorm ℝ X) (center : X)
    (base loss : ℕ) (U : Set X) (Ω : I → Set PolarPoint)
    (δ H E : I → PolarPoint → ℝ) (f : I → X → PolarPoint → ℝ) : Prop :=
  ∀ K s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
    ∀ m : I, ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
    ∀ q ∈ Ω m, ∀ J : SmoothDirections U (fun x => mixedDerivative a b (f m x) q),
    ∀ x ∈ U, p base (x - center) ≤ 1 →
    ∀ v : Fin k → X, (∀ i, p base (v i) ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → p (s + loss) (x - center) ≤ R →
      (∀ i, p (s + loss) (v i) ≤ R) →
      δ m q ^ a * ‖J.D k x v‖ ≤
        C * E m q ^ A * parameterHeightWeight (H m q) k *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))

variable {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
  {U : Set X} {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
  {f g : I → X → PolarPoint → ℝ}

theorem EndpointMixedPowerBounds.add
    (hf : EndpointMixedPowerBounds p center base loss U Ω δ H E f)
    (hg : EndpointMixedPowerBounds p center base loss U Ω δ H E g)
    (F : ∀ m, MixedJetRegularity U (Ω m) (f m))
    (G : ∀ m, MixedJetRegularity U (Ω m) (g m))
    (hΩ : ∀ m, IsOpen (Ω m)) (hδ : ∀ m q, q ∈ Ω m → 0 ≤ δ m q)
    (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q) :
    EndpointMixedPowerBounds p center base loss U Ω δ H E (fun m x q => f m x q + g m x q) := by
  intro K s
  obtain ⟨Cf, Af, hCf, hAf, hfb⟩ := hf K s
  obtain ⟨Cg, Ag, hCg, hAg, hgb⟩ := hg K s
  refine ⟨Cf + Cg, Af + Ag, by linarith, add_nonneg hAf hAg, ?_⟩
  intro m k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  let Jf := (F m).parameter a b q hq
  let Jg := (G m).parameter a b q hq
  let Jadd := (smoothDirectionsAdd Jf Jg).congr (fun y hy =>
    (mixedDerivative_add_on_open (hΩ m) ((F m).spatial y hy) ((G m).spatial y hy) a b hq).symm)
  have heq := HasProjectiveJetsOn.unique J.open_domain
    J.hasProjectiveJetsOn Jadd.hasProjectiveJetsOn k x hx
  have hd : J.D k x v = Jf.D k x v + Jg.D k x v := by
    have hh := congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq
    simpa only [Jadd, SmoothDirections.congr, smoothDirectionsAdd, add_apply] using hh
  have hW : 0 ≤ parameterHeightWeight (H m q) k *
      R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
    mul_nonneg (parameterHeightWeight_nonneg (hH m q hq) k)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hef := Real.rpow_le_rpow_of_exponent_le (hE m q hq)
    (le_add_of_nonneg_right hAg : Af ≤ Af + Ag)
  have heg := Real.rpow_le_rpow_of_exponent_le (hE m q hq)
    (le_add_of_nonneg_left hAf : Ag ≤ Af + Ag)
  have hbf := hfb m k hk a b hab q hq Jf x hx hlow v hv R hR hhigh hvhigh
  have hbg := hgb m k hk a b hab q hq Jg x hx hlow v hv R hR hhigh hvhigh
  rw [hd]
  have hδa : 0 ≤ δ m q ^ a := pow_nonneg (hδ m q hq) a
  apply ((mul_le_mul_of_nonneg_left (norm_add_le _ _) hδa).trans_eq
    (mul_add _ _ _)).trans
  calc
    _ ≤ Cf * E m q ^ Af * parameterHeightWeight (H m q) k *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) +
        Cg * E m q ^ Ag * parameterHeightWeight (H m q) k *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := add_le_add hbf hbg
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hef (zero_le_one.trans hCf)) hW
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heg (zero_le_one.trans hCg)) hW
      nlinarith only [h1, h2]

/-- Multiplication preserves the original interpolation indices. -/
theorem EndpointMixedPowerBounds.mul
    (hf : EndpointMixedPowerBounds p center base loss U Ω δ H E f)
    (hg : EndpointMixedPowerBounds p center base loss U Ω δ H E g)
    (F : ∀ m, MixedJetRegularity U (Ω m) (f m))
    (G : ∀ m, MixedJetRegularity U (Ω m) (g m))
    (hΩ : ∀ m, IsOpen (Ω m)) (hδ : ∀ m q, q ∈ Ω m → 0 ≤ δ m q)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q)
    {RH : ℝ} (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q ∧ H m q ≤ RH) :
    EndpointMixedPowerBounds p center base loss U Ω δ H E (fun m x q => f m x q * g m x q) := by
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
  intro m k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  have hEpos : 0 < E m q := zero_lt_one.trans_le (hE m q hq)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let IJ := Fin (a + 1) × Fin (b + 1)
  let coeff : IJ → ℝ := fun t => (a.choose t.1.val : ℝ) * (b.choose t.2.val : ℝ)
  let terms : IJ → X → ℝ := fun t y =>
    mixedDerivative t.1.val t.2.val (f m y) q *
      mixedDerivative (a - t.1.val) (b - t.2.val) (g m y) q
  let JT : ∀ t, SmoothDirections U (terms t) := fun t =>
    smoothDirections_realMul ((F m).parameter t.1.val t.2.val q hq)
      ((G m).parameter (a - t.1.val) (b - t.2.val) q hq)
  let W : ℝ := E m q ^ (Af + Ag) * parameterHeightWeight (H m q) k *
    R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hW : 0 ≤ W := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hEpos.le _)
      (parameterHeightWeight_nonneg (hH m q hq).1 k))
    (Real.rpow_nonneg hRpos.le _)
  have hδa : 0 ≤ δ m q ^ a := pow_nonneg (hδ m q hq) a
  have hterm (t : IJ) : δ m q ^ a * ‖(JT t).D k x v‖ ≤ Cp * Cf * Cg * W := by
    have hi : t.1.val ≤ a := Nat.le_of_lt_succ t.1.isLt
    have hj : t.2.val ≤ b := Nat.le_of_lt_succ t.2.isLt
    have hfs : t.1.val + t.2.val ≤ s := by omega
    have hgs : (a - t.1.val) + (b - t.2.val) ≤ s := by omega
    have htotal : (t.1.val + t.2.val) + ((a - t.1.val) + (b - t.2.val)) = a + b := by omega
    let sf : ℝ := δ m q ^ t.1.val
    let sg : ℝ := δ m q ^ (a - t.1.val)
    have hsf : 0 ≤ sf := pow_nonneg (hδ m q hq) _
    have hsg : 0 ≤ sg := pow_nonneg (hδ m q hq) _
    let Lf : ℝ →L[ℝ] ℝ := sf • ContinuousLinearMap.id ℝ ℝ
    let Lg : ℝ →L[ℝ] ℝ := sg • ContinuousLinearMap.id ℝ ℝ
    let La : ℝ →L[ℝ] ℝ := (δ m q ^ a) • ContinuousLinearMap.id ℝ ℝ
    let f₀ : X → ℝ := fun y => sf * mixedDerivative t.1.val t.2.val (f m y) q
    let g₀ : X → ℝ := fun y => sg * mixedDerivative (a - t.1.val) (b - t.2.val) (g m y) q
    let Jf₀ := (F m).parameter t.1.val t.2.val q hq
    let Jg₀ := (G m).parameter (a - t.1.val) (b - t.2.val) q hq
    let Jf : SmoothDirections U f₀ := smoothDirections_postcompCLM Jf₀ Lf
    let Jg : SmoothDirections U g₀ := smoothDirections_postcompCLM Jg₀ Lg
    let Bf : ℝ := Cf * E m q ^ Af *
      R ^ (((t.1.val + t.2.val : ℕ) : ℝ) / ((s : ℝ) + 1))
    let Bg : ℝ := Cg * E m q ^ Ag *
      R ^ ((((a - t.1.val) + (b - t.2.val) : ℕ) : ℝ) / ((s : ℝ) + 1))
    have hBf : 0 < Bf := mul_pos
      (mul_pos (zero_lt_one.trans_le hCf) (Real.rpow_pos_of_pos hEpos _))
      (Real.rpow_pos_of_pos hRpos _)
    have hBg : 0 < Bg := mul_pos
      (mul_pos (zero_lt_one.trans_le hCg) (Real.rpow_pos_of_pos hEpos _))
      (Real.rpow_pos_of_pos hRpos _)
    have hbasef : ‖f₀ x‖ ≤ Bf := by
      have hh := hfb m 0 (Nat.zero_le K) t.1.val t.2.val hfs q hq Jf₀ x hx hlow
        Fin.elim0 (fun i => i.elim0) R hR hhigh (fun i => i.elim0)
      simpa only [smoothDirections_D_zero_apply Jf₀ hx, parameterHeightWeight,
        ite_true, mul_one, f₀, norm_mul, Real.norm_of_nonneg hsf, sf] using hh
    have hbaseg : ‖g₀ x‖ ≤ Bg := by
      have hh := hgb m 0 (Nat.zero_le K) (a - t.1.val) (b - t.2.val) hgs q hq Jg₀ x hx hlow
        Fin.elim0 (fun i => i.elim0) R hR hhigh (fun i => i.elim0)
      simpa only [smoothDirections_D_zero_apply Jg₀ hx, parameterHeightWeight,
        ite_true, mul_one, g₀, norm_mul, Real.norm_of_nonneg hsg, sg] using hh
    have hjetf (d : OrderedFinpartition k) (j : Fin d.length) :
        ‖Jf.D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H m q * Bf := by
      have hh := hfb m (d.partSize j) ((d.partSize_le j).trans hk)
        t.1.val t.2.val hfs q hq Jf₀ x hx hlow (v ∘ d.emb j)
        (fun i => hv _) R hR hhigh (fun i => hvhigh _)
      simpa only [Jf, smoothDirections_postcompCLM_D_apply, Lf, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hsf,
        sf, parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos j)),
        Bf, mul_assoc, mul_left_comm, mul_comm] using hh
    have hjetg (d : OrderedFinpartition k) (j : Fin d.length) :
        ‖Jg.D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H m q * Bg := by
      have hh := hgb m (d.partSize j) ((d.partSize_le j).trans hk)
        (a - t.1.val) (b - t.2.val) hgs q hq Jg₀ x hx hlow (v ∘ d.emb j)
        (fun i => hv _) R hR hhigh (fun i => hvhigh _)
      simpa only [Jg, smoothDirections_postcompCLM_D_apply, Lg, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hsg,
        sg, parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos j)),
        Bg, mul_assoc, mul_left_comm, mul_comm] using hh
    let ff : Fin 2 → X → ℝ := Fin.cases f₀ (fun _ => g₀)
    let JJ : ∀ i, SmoothDirections U (ff i) := Fin.cases Jf (fun _ => Jg)
    let BB : Fin 2 → ℝ := Fin.cases Bf (fun _ => Bg)
    have hff₀ : ff 0 = f₀ := by simp only [ff, Fin.cases_zero]
    have hff₁ : ff 1 = g₀ := by
      rw [show (1 : Fin 2) = (0 : Fin 1).succ from by decide]
      simp only [ff, Fin.cases_succ]
    have hscale : δ m q ^ a = sf * sg := by
      dsimp only [sf, sg]
      rw [← pow_add, Nat.add_sub_of_le hi]
    let JP : SmoothDirections U (fun y => ∏ i, ff i y) :=
      (smoothDirections_postcompCLM (JT t) La).congr (fun y _ => by
        simp only [Function.comp_apply, La, smul_apply, ContinuousLinearMap.id_apply,
          smul_eq_mul, terms, Fin.prod_univ_two, hff₀, hff₁]
        rw [hscale]
        dsimp only [f₀, g₀]
        ring)
    have hJP : ‖JP.D k x v‖ = δ m q ^ a * ‖(JT t).D k x v‖ := by
      change ‖(smoothDirections_postcompCLM (JT t) La).D k x v‖ = _
      simp only [smoothDirections_postcompCLM_D_apply, La, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hδa]
    have hBB : ∀ i : Fin 2, 0 < BB i := Fin.cases hBf (fun _ => hBg)
    have hBP := hcb ⟨k, Nat.lt_succ_of_le hk⟩ JJ JP x hx (H m q)
      (hH m q hq).1 (hH m q hq).2 BB hBB
      (Fin.cases hbasef (fun _ => hbaseg)) v
      (Fin.cases hjetf (fun _ => hjetg))
    have hprod : (∏ i, BB i) =
        Cf * Cg * E m q ^ (Af + Ag) *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      simp only [Fin.prod_univ_two, BB, Fin.cases_zero, Fin.cases_succ]
      calc
        Bf * Bg = (Cf * Cg) * (E m q ^ Af * E m q ^ Ag) *
            (R ^ (((t.1.val + t.2.val : ℕ) : ℝ) / ((s : ℝ) + 1)) *
              R ^ ((((a - t.1.val) + (b - t.2.val) : ℕ) : ℝ) / ((s : ℝ) + 1))) := by
          dsimp only [Bf, Bg]
          ring
        _ = _ := by rw [← Real.rpow_add hEpos, rpow_spatialOrder_mul hRpos, htotal]
    have hBprod : 0 ≤ ∏ i, BB i :=
      Finset.prod_nonneg (fun i _ => (hBB i).le)
    calc
      δ m q ^ a * ‖(JT t).D k x v‖ ≤ c ⟨k, Nat.lt_succ_of_le hk⟩ *
          parameterHeightWeight (H m q) k * ∏ i, BB i := by
        simpa only [hJP, parameterHeightWeight] using hBP
      _ ≤ Cp * parameterHeightWeight (H m q) k * ∏ i, BB i :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcCp _) (parameterHeightWeight_nonneg (hH m q hq).1 k))
          hBprod
      _ = Cp * Cf * Cg * W := by rw [hprod]; dsimp only [W]; ring
  have hsplit (F : IJ → ℝ) : (∑ t : IJ, F t) =
      ∑ i : Fin (a + 1), ∑ j : Fin (b + 1), F (i, j) :=
    Fintype.sum_prod_type (fun t : Fin (a + 1) × Fin (b + 1) => F t)
  have hd := smoothDirections_D_eq_linearCombination J JT coeff
    (fun y hy => by
      rw [hsplit (fun t => coeff t * terms t y)]
      exact mixedDerivative_mul_on_open (hΩ m) ((F m).spatial y hy)
        ((G m).spatial y hy) a b hq)
    k hx v
  have hcoeff (t : IJ) : 0 ≤ coeff t :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnormCoeff (t : IJ) : ‖coeff t‖ = coeff t := Real.norm_of_nonneg (hcoeff t)
  have hsum : (∑ t : IJ, coeff t) = (2 : ℝ) ^ (a + b) := by
    rw [hsplit coeff]
    exact mixedLeibniz_coefficient_sum a b
  have hpow : (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ s :=
    pow_le_pow_right₀ (by norm_num) hab
  calc
    δ m q ^ a * ‖J.D k x v‖ ≤
        δ m q ^ a * ∑ t, coeff t * ‖(JT t).D k x v‖ := by
      apply mul_le_mul_of_nonneg_left _ hδa
      rw [hd]
      simpa only [norm_mul, hnormCoeff] using
        norm_sum_le (Finset.univ : Finset IJ) (fun t : IJ => coeff t * (JT t).D k x v)
    _ = ∑ t, coeff t * (δ m q ^ a * ‖(JT t).D k x v‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ t, coeff t * (Cp * Cf * Cg * W) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hterm t) (hcoeff t))
    _ = (2 : ℝ) ^ (a + b) * (Cp * Cf * Cg * W) := by rw [← Finset.sum_mul, hsum]
    _ ≤ C * W := by
      have hh := mul_le_mul_of_nonneg_right hpow
        (mul_nonneg (mul_nonneg (mul_nonneg hCp (zero_le_one.trans hCf))
          (zero_le_one.trans hCg)) hW)
      simpa only [C, mul_assoc] using hh
    _ ≤ (1 + C) * E m q ^ (Af + Ag) * parameterHeightWeight (H m q) k *
        R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      have hh := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left zero_le_one : C ≤ 1 + C) hW
      simpa only [W, mul_assoc] using hh



/-- Negation does not change any weighted jet bound. -/
theorem EndpointMixedPowerBounds.neg
    (hf : EndpointMixedPowerBounds p center base loss U Ω δ H E f)
    (F : ∀ m, MixedJetRegularity U (Ω m) (f m)) :
    EndpointMixedPowerBounds p center base loss U Ω δ H E (fun m x q => -(f m x q)) := by
  intro K s
  obtain ⟨C, A, hC, hA, hb⟩ := hf K s
  refine ⟨C, A, hC, hA, ?_⟩
  intro m k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  let Jf := (F m).parameter a b q hq
  let L : ℝ →L[ℝ] ℝ := (-1 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  let Jneg : SmoothDirections U (fun y => mixedDerivative a b (fun t => -(f m y t)) q) :=
    (smoothDirections_postcompCLM Jf L).congr (fun y _ => by
      simpa only [Function.comp_apply, L, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, neg_one_mul] using
        (mixedDerivative_const_mul (-1) (f m y) a b q).symm)
  have heq := HasProjectiveJetsOn.unique J.open_domain
    J.hasProjectiveJetsOn Jneg.hasProjectiveJetsOn k x hx
  have hd : J.D k x v = -(Jf.D k x v) := by
    have hh := congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq
    simpa only [Jneg, SmoothDirections.congr, smoothDirections_postcompCLM_D_apply, L, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, neg_one_mul] using hh
  rw [hd, norm_neg]
  exact hb m k hk a b hab q hq Jf x hx hlow v hv R hR hhigh hvhigh

/-- The weighted estimate concerns the actual field, independently of
the particular genuine tower chosen for its jets. -/
theorem EndpointMixedPowerBounds.congr
    (hf : EndpointMixedPowerBounds p center base loss U Ω δ H E f)
    (F : ∀ m, MixedJetRegularity U (Ω m) (f m))
    (G : ∀ m, MixedJetRegularity U (Ω m) (g m))
    (hΩ : ∀ m, IsOpen (Ω m))
    (heq : ∀ m x, x ∈ U → EqOn (f m x) (g m x) (Ω m)) :
    EndpointMixedPowerBounds p center base loss U Ω δ H E g := by
  intro K s
  obtain ⟨C, A, hC, hA, hb⟩ := hf K s
  refine ⟨C, A, hC, hA, ?_⟩
  intro m k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  let Jf := J.congr (fun y hy =>
    (mixedDerivative_eq_of_eqOn (hΩ m) ((F m).spatial y hy) ((G m).spatial y hy)
      (heq m y hy) a b hq).symm)
  exact hb m k hk a b hab q hq Jf x hx hlow v hv R hR hhigh hvhigh

end ContinuousFlexibility.Analysis
