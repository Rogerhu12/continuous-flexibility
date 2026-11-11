import ContinuousFlexibility.Analysis.PolynomialJetOperations
import ContinuousFlexibility.Analysis.PolynomialJetPowers

/-!
# Fixed-power mixed jets of a fiberwise inverse

Differentiating the actual right-inverse identity gives the triangular
inverse derivative. Induction on the total derivative order then uses
only lower inverse jets. No bound for the value of either circle lift
is needed. All constants are uniform in the component index.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

theorem triangular_inverse_derivative_algebra
    (A B : (ℝ × ℝ) →L[ℝ] ℝ) (hb : A (0, 1) ≠ 0)
    (hcomp : A.comp ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod B) =
      ContinuousLinearMap.snd ℝ ℝ ℝ) :
    B = (A (-1, 0) * (A (0, 1))⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (A (0, 1))⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L v) hcomp
  have hpair : (v.1, B v) = v.1 • ((1, 0) : ℝ × ℝ) + B v • ((0, 1) : ℝ × ℝ) := by
    simp only [Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  have hscalar : v.1 * A (1, 0) + B v * A (0, 1) = v.2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', hpair,
      map_add, map_smul, smul_eq_mul] using h
  have hneg : A (-1, 0) = -A (1, 0) := by
    have heq : ((-1, 0) : ℝ × ℝ) = -((1, 0) : ℝ × ℝ) := by ext <;> simp
    rw [heq, map_neg]
  have hsol : B v = (v.2 - v.1 * A (1, 0)) / A (0, 1) :=
    (eq_div_iff hb).mpr (by linarith only [hscalar])
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [hsol, hneg]
  field_simp [hb]
  <;> ring

/-- A triangular derivative equation has polynomially bounded positive
jets whenever its right-hand side has such bounds. The recurrence never
uses the value of the unknown circle lift. -/
theorem norm_iteratedFDeriv_of_fiber_derivative_polynomial_bound
    {ι : Type*} (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (U : ι → Set (ℝ × ℝ)) (hU : ∀ i, IsOpen (U i))
    (g : ι → (ℝ × ℝ) → ℝ)
    (R : ι → (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (hR : ∀ i, ContDiffOn ℝ ∞ (R i) (U i))
    (hmap : ∀ i, MapsTo (fun p => (p.1, g i p)) (U i) (U i))
    (hderiv : ∀ i p, p ∈ U i → fderiv ℝ (g i) p = R i (p.1, g i p))
    (hRbound : ∀ n : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
      ‖iteratedFDeriv ℝ n (R i) p‖ ≤ A * W i ^ P)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
      ‖iteratedFDeriv ℝ n (g i) p‖ ≤ A * W i ^ P := by
  induction n using Nat.strong_induction_on generalizing hn with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hinner (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
          ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
          ‖iteratedFDeriv ℝ k (fun q => (q.1, g i q)) p‖ ≤ A * W i ^ P :=
        norm_iteratedFDeriv_coordinate_graph_polynomial_bound W hW U hU g hg k hk
          (ih k (by omega) hk)
      have houter (k : ℕ) (_hk : k ≤ n) :
          ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
          ‖iteratedFDeriv ℝ k (R i) (p.1, g i p)‖ ≤ A * W i ^ P := by
        obtain ⟨A, P, hA, hP, hb⟩ := hRbound k
        exact ⟨A, P, hA, hP, fun i p hp => hb i _ (hmap i hp)⟩
      obtain ⟨A, P, hA, hP, hb⟩ := norm_iteratedFDeriv_comp_polynomial_bound
        W hW U U hU hU (fun i p => (p.1, g i p)) R
        (fun i => contDiffOn_fst.prodMk (hg i)) hR hmap n houter hinner
      refine ⟨A, P, hA, hP, fun i p hp => ?_⟩
      have heq : fderiv ℝ (g i) =ᶠ[𝓝 p] fun q => R i (q.1, g i q) := by
        filter_upwards [(hU i).mem_nhds hp] with q hq
        exact hderiv i q hq
      rw [← norm_iteratedFDeriv_fderiv, (heq.iteratedFDeriv ℝ n).eq_of_nhds]
      exact hb i p hp

/-- The right-inverse identity itself supplies the derivative equation.
The scalar angular lower bound is the only denominator bound used. -/
theorem norm_iteratedFDeriv_fiber_inverse_polynomial_bound
    {ι : Type*} (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (U : ι → Set (ℝ × ℝ)) (hU : ∀ i, IsOpen (U i))
    (F g : ι → (ℝ × ℝ) → ℝ)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (U i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (hmap : ∀ i, MapsTo (fun p => (p.1, g i p)) (U i) (U i))
    (hright : ∀ i p, p ∈ U i → F i (p.1, g i p) = p.2)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ i p, p ∈ U i → c ≤ fderiv ℝ (F i) p (0, 1))
    (hFbound : ∀ n : ℕ, 1 ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i p, p ∈ U i → ‖iteratedFDeriv ℝ n (F i) p‖ ≤ A * W i ^ P)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
      ‖iteratedFDeriv ℝ n (g i) p‖ ≤ A * W i ^ P := by
  let u (i : ι) (p : ℝ × ℝ) : ℝ := fderiv ℝ (F i) p (-1, 0)
  let v (i : ι) (p : ℝ × ℝ) : ℝ := fderiv ℝ (F i) p (0, 1)
  have hu (i : ι) : ContDiffOn ℝ ∞ (u i) (U i) :=
    ((hF i).fderiv_of_isOpen (hU i) (by simp)).clm_apply contDiffOn_const
  have hv (i : ι) : ContDiffOn ℝ ∞ (v i) (U i) :=
    ((hF i).fderiv_of_isOpen (hU i) (by simp)).clm_apply contDiffOn_const
  have hvpos (i : ι) (p : ℝ × ℝ) (hp : p ∈ U i) : 0 < v i p :=
    hc.trans_le (hlower i p hp)
  have hub (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
      ‖iteratedFDeriv ℝ k (u i) p‖ ≤ A * W i ^ P :=
    norm_iteratedFDeriv_fderiv_apply_polynomial_bound W U hU F hF (-1, 0) k
      (hFbound (k + 1) (by omega))
  have hvb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
      ‖iteratedFDeriv ℝ k (v i) p‖ ≤ A * W i ^ P :=
    norm_iteratedFDeriv_fderiv_apply_polynomial_bound W U hU F hF (0, 1) k
      (hFbound (k + 1) (by omega))
  let b (i : ι) (p : ℝ × ℝ) : ℝ := (v i p)⁻¹
  have hb (i : ι) : ContDiffOn ℝ ∞ (b i) (U i) :=
    (hv i).inv (fun p hp => (hvpos i p hp).ne')
  have hbb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
      ‖iteratedFDeriv ℝ k (b i) p‖ ≤ A * W i ^ P := by
    apply norm_iteratedFDeriv_inv_polynomial_bound W hW U hU v hv hc
      (show (0 : ℝ) ≤ 0 from le_rfl) _ hvb k
    intro i p hp
    simpa only [neg_zero, Real.rpow_zero, mul_one] using hlower i p hp
  let a (i : ι) (p : ℝ × ℝ) : ℝ := u i p * b i p
  have ha (i : ι) : ContDiffOn ℝ ∞ (a i) (U i) := (hu i).mul (hb i)
  have hab (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
      ‖iteratedFDeriv ℝ k (a i) p‖ ≤ A * W i ^ P :=
    norm_iteratedFDeriv_mul_polynomial_bound W hW U hU u b hu hb k
      (fun j _ => hub j) (fun j _ => hbb j)
  let L₁ : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let L₂ : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let R (i : ι) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ := a i p • L₁ + b i p • L₂
  have hR (i : ι) : ContDiffOn ℝ ∞ (R i) (U i) :=
    ((ha i).smul_const L₁).add ((hb i).smul_const L₂)
  have hRb (k : ℕ) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ U i →
      ‖iteratedFDeriv ℝ k (R i) p‖ ≤ A * W i ^ P := by
    apply norm_iteratedFDeriv_add_polynomial_bound W hW U hU
      (fun i p => a i p • L₁) (fun i p => b i p • L₂)
      (fun i => (ha i).smul_const L₁) (fun i => (hb i).smul_const L₂) k
    · simpa only [ContinuousLinearMap.toSpanSingleton_apply] using
        norm_iteratedFDeriv_clm_left_polynomial_bound W U hU a ha
          (ContinuousLinearMap.toSpanSingleton ℝ L₁) k (hab k)
    · simpa only [ContinuousLinearMap.toSpanSingleton_apply] using
        norm_iteratedFDeriv_clm_left_polynomial_bound W U hU b hb
          (ContinuousLinearMap.toSpanSingleton ℝ L₂) k (hbb k)
  apply norm_iteratedFDeriv_of_fiber_derivative_polynomial_bound W hW U hU g R
    hg hR hmap _ hRb n hn
  intro i p hp
  have hFd := ((hF i).contDiffAt ((hU i).mem_nhds (hmap i hp))).differentiableAt (by simp)
  have hgd := ((hg i).contDiffAt ((hU i).mem_nhds hp)).differentiableAt (by simp)
  have hchain : HasFDerivAt (fun q : ℝ × ℝ => F i (q.1, g i q))
      ((fderiv ℝ (F i) (p.1, g i p)).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ (g i) p))) p := by
    simpa only [Function.comp_def] using
      hFd.hasFDerivAt.comp p (hasFDerivAt_fst.prodMk hgd.hasFDerivAt)
  have heq : (fun q : ℝ × ℝ => q.2) =ᶠ[𝓝 p] fun q => F i (q.1, g i q) := by
    filter_upwards [(hU i).mem_nhds hp] with q hq
    exact (hright i q hq).symm
  have hcomp := (hchain.congr_of_eventuallyEq heq).unique hasFDerivAt_snd
  exact triangular_inverse_derivative_algebra (fderiv ℝ (F i) (p.1, g i p))
    (fderiv ℝ (g i) p) (hvpos i _ (hmap i hp)).ne' hcomp

end ContinuousFlexibility.Analysis
