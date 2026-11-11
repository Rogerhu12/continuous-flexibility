import ContinuousFlexibility.Analysis.CanonicalJetProductClosure
import ContinuousFlexibility.Analysis.FlowJetPolynomial
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# A common fixed loss for finite flow-jet majorants

The polynomial records the derivative weight of each original field
factor. Interpolation is applied once to the expanded monomials. All
finite material factors are then absorbed before the state and the
material envelope are chosen. Empty products and constant terms are
included, so the loss is independent of both order and factor count.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem flow_list_sum_get (ks : List ℕ) :
    (∑ i : Fin ks.length, ks.get i) = ks.sum := by
  rw [← List.sum_ofFn, List.ofFn_get]

private theorem flow_list_prod_get (ks : List ℕ) (X : ℕ → ℝ) :
    (∏ i : Fin ks.length, X (ks.get i)) = (ks.map X).prod := by
  rw [← List.prod_ofFn]
  have h : List.ofFn (fun i : Fin ks.length => X (ks.get i)) = ks.map X := by
    rw [← List.map_ofFn, List.ofFn_get]
  rw [h]

private theorem flow_list_material_product
    (ks : List ℕ) (A X : ℕ → ℝ) {W : ℝ} (hW : 0 < W) :
    (ks.map (fun k => A k * W ^ (A k) * X k)).prod =
      (ks.map A).prod * W ^ (ks.map A).sum * (ks.map X).prod := by
  induction ks with
  | nil => simp only [List.map_nil, List.prod_nil, List.sum_nil, Real.rpow_zero, mul_one]
  | cons k ks ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih,
      Real.rpow_add hW]
    ring

/-- The finite polynomial majorant of actual flow jets has the same
single high-seminorm form at every order, with one common low order and
one common loss. Its constants precede both the state and the envelope. -/
theorem flowJetPolynomial_le_material_one_high
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (offset : ℕ) :
    ∃ base loss : ℕ, ∀ s : ℕ, ∀ P : FlowJetPolynomial,
      FlowJetPolynomialDegreeLE P s →
      ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∃ B : ℝ, 0 < B ∧ ∀ z : E, p base z ≤ 1 →
        ∀ W : ℝ, 1 ≤ W →
          flowJetPolynomialEval P
            (fun k => A k * W ^ (A k) * (1 + p (k + offset) z)) ≤
            B * W ^ B * (1 + p (s + loss) z) := by
  classical
  obtain ⟨base, loss, hprod⟩ := coordinate_jet_product_le_one_high_of_low hp hI offset
  have hlist (ks : List ℕ) (s : ℕ) (hs : ks.sum ≤ s) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E, p base z ≤ 1 →
        (ks.map (fun k => 1 + p (k + offset) z)).prod ≤
          C * (1 + p (s + loss) z) := by
    cases ks with
    | nil =>
      refine ⟨1, zero_le_one, fun z _ => ?_⟩
      simpa only [List.map_nil, List.prod_nil, one_mul] using
        (le_add_of_nonneg_right (apply_nonneg (p (s + loss)) z) :
          (1 : ℝ) ≤ 1 + p (s + loss) z)
    | cons k ks =>
      letI : Nonempty (Fin (k :: ks).length) := ⟨⟨0, by simp⟩⟩
      obtain ⟨C, hC, hbound⟩ := hprod (List.get (k :: ks)) s
        (by simpa only [flow_list_sum_get] using hs)
      refine ⟨C, hC, fun z hz => ?_⟩
      simpa only [flow_list_prod_get] using hbound z hz
  refine ⟨base, loss, ?_⟩
  intro s P hP A hA
  have hA0 (k : ℕ) : 0 ≤ A k := zero_le_one.trans (hA k)
  have hmajorant : ∀ Q : FlowJetPolynomial, FlowJetPolynomialDegreeLE Q s →
      ∃ C e : ℝ, 0 ≤ C ∧ ∀ z : E, p base z ≤ 1 →
        ∀ W : ℝ, 1 ≤ W →
          flowJetPolynomialEval Q
            (fun k => A k * W ^ (A k) * (1 + p (k + offset) z)) ≤
            C * W ^ e * (1 + p (s + loss) z) := by
    intro Q
    induction Q with
    | nil =>
      intro _
      refine ⟨0, 0, le_rfl, fun z _ W _ => ?_⟩
      simp only [flowJetPolynomialEval_nil, zero_mul, le_refl]
    | cons m Q ih =>
      intro hQ
      have hm := hQ m List.mem_cons_self
      obtain ⟨C₀, hC₀, hb₀⟩ := hlist m.2 s hm.2
      obtain ⟨C₁, e₁, hC₁, hb₁⟩ :=
        ih (fun n hn => hQ n (List.mem_cons_of_mem m hn))
      let c : ℝ := m.1 * (m.2.map A).prod * C₀
      let e : ℝ := (m.2.map A).sum
      have hprodA : 0 ≤ (m.2.map A).prod := by
        apply List.prod_nonneg
        intro x hx
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
        exact hA0 k
      have hc : 0 ≤ c := mul_nonneg (mul_nonneg hm.1 hprodA) hC₀
      refine ⟨c + C₁, max e e₁, add_nonneg hc hC₁, ?_⟩
      intro z hz W hW
      have hW0 : 0 < W := zero_lt_one.trans_le hW
      have hH : 0 ≤ 1 + p (s + loss) z :=
        add_nonneg zero_le_one (apply_nonneg _ _)
      have hmBound :
          m.1 * (m.2.map (fun k =>
            A k * W ^ (A k) * (1 + p (k + offset) z))).prod ≤
          c * W ^ e * (1 + p (s + loss) z) := by
        rw [flow_list_material_product _ _ _ hW0]
        calc
          _ ≤ m.1 * ((m.2.map A).prod * W ^ e *
              (C₀ * (1 + p (s + loss) z))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hb₀ z hz)
                (mul_nonneg hprodA (Real.rpow_nonneg hW0.le _))) hm.1
          _ = c * W ^ e * (1 + p (s + loss) z) := by dsimp only [c]; ring
      have hmono₀ : c * W ^ e ≤ c * W ^ (max e e₁) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hW (le_max_left _ _)) hc
      have hmono₁ : C₁ * W ^ e₁ ≤ C₁ * W ^ (max e e₁) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hW (le_max_right _ _)) hC₁
      calc
        _ ≤ c * W ^ e * (1 + p (s + loss) z) +
            C₁ * W ^ e₁ * (1 + p (s + loss) z) :=
          (flowJetPolynomialEval_cons _ _ _).trans_le
            (add_le_add hmBound (hb₁ z hz W hW))
        _ ≤ c * W ^ (max e e₁) * (1 + p (s + loss) z) +
            C₁ * W ^ (max e e₁) * (1 + p (s + loss) z) :=
          add_le_add (mul_le_mul_of_nonneg_right hmono₀ hH)
            (mul_le_mul_of_nonneg_right hmono₁ hH)
        _ = (c + C₁) * W ^ (max e e₁) * (1 + p (s + loss) z) := by ring
  obtain ⟨C, e, _, hbound⟩ := hmajorant P hP
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack C e
  refine ⟨B, hB, fun z hz W hW => ?_⟩
  exact (hbound z hz W hW).trans
    (mul_le_mul_of_nonneg_right (hpack W hW)
      (add_nonneg zero_le_one (apply_nonneg _ _)))

end ContinuousFlexibility.Analysis
