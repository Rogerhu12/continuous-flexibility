import ContinuousFlexibility.Analysis.N06NuCoordinateJets
import ContinuousFlexibility.Analysis.N06Neighborhood
import ContinuousFlexibility.Analysis.NeighborhoodProfileBounds

/-!
# Fixed-seminorm bounds for differences of actual nu-coordinate jets

The finite coordinate packet is affine in the real state and q. Its fixed
angular jets therefore have a uniform linear difference bound in the
original state grading, with order j+4. No smallness of a source-space
element or an independently prescribed jet is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def N06StateHeightFiniteJetDifferenceBound (D : ReferenceData) (S : PhysicalSpacesData)
    (n : ℕ) (C : ℝ) : Prop :=
  ∀ a b, a + b ≤ n → ∀ (x y : AnnularState S) (p : PolarPoint),
    p ∈ annularOpen D →
      |mixedDerivative a b (stateU S x) p - mixedDerivative a b (stateU S y) p| ≤
        C * stateGrading S (n + 2) (x - y)

theorem n06_stateU_mixedDerivative_finite_difference_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ N06StateHeightFiniteJetDifferenceBound D S n C := by
  classical
  let I := Fin (n + 1) × Fin (n + 1)
  have hchoices (i : I) :=
    n06_stateU_mixedDerivative_difference_bound hD hT hS i.1.val i.2.val
  choose c hc hbound using hchoices
  let C : ℝ := ∑ i : I, c i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => hc i
  refine ⟨C, hC, ?_⟩
  intro a b hab x y p hp
  let i : I := (⟨a, by omega⟩, ⟨b, by omega⟩)
  have hi : c i ≤ C := Finset.single_le_sum (fun k _ => hc k) (Finset.mem_univ i)
  calc
    _ ≤ c i * stateGrading S (a + b + 2) (x - y) := hbound i x y p hp
    _ ≤ c i * stateGrading S (n + 2) (x - y) :=
      mul_le_mul_of_nonneg_left (solve_stateGrading_monotone S (by omega) (x - y)) (hc i)
    _ ≤ _ := mul_le_mul_of_nonneg_right hi (apply_nonneg _ _)

def n06NuCoordinateAngularJet (D : ReferenceData) (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (r θ : ℝ) (j : ℕ) : N06NuJetCoordinates :=
  ![if j = 0 then r else 0,
    if j = 0 then D.w r else 0,
    if j = 0 then deriv D.w r else 0,
    if j = 0 then D.chi r else 0,
    if j = 0 then deriv D.chi r else 0,
    mixedDerivative 1 j (stateU S z.1) (r, θ),
    mixedDerivative 2 j (stateU S z.1) (r, θ),
    (1 / r) * mixedDerivative 0 (j + 1) (stateU S z.1) (r, θ),
    (1 / r) * mixedDerivative 1 (j + 1) (stateU S z.1) (r, θ) -
      (1 / r ^ 2) * mixedDerivative 0 (j + 1) (stateU S z.1) (r, θ),
    (1 / r) * mixedDerivative 0 (j + 2) (stateU S z.1) (r, θ),
    if j = 0 then z.2 else 0,
    if j = 0 then z.1.2.1 else 0]

theorem n06_actualNuJetCoordinates_angularJet_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) {r : ℝ} (hr : r ≠ 0) (j : ℕ) (θ : ℝ) :
    iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S z (r, t)) θ =
      n06NuCoordinateAngularJet D S z r θ j := by
  have h := n06_nuHeight_angularJet_formulas (neighborhood_stateU_contDiff hT hS z.1) hr j θ
  ext i
  rw [n06_actualNuJetCoordinates_angularJet_apply hT hS z hr]
  fin_cases i <;>
    simp only [n06ActualNuJetCoordinates, n06NuCoordinateAngularJet,
      Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    first | exact iteratedDeriv_const | exact h.1 | exact h.2.1 |
      exact h.2.2.1 | exact h.2.2.2.1 | exact h.2.2.2.2

private theorem n06_scaled_difference_le {c c₀ L P u v : ℝ}
    (hc : 0 ≤ c) (hc₀ : c ≤ c₀) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (h : |u - v| ≤ L * P) : |c * u - c * v| ≤ (c₀ * L) * P := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  exact ((mul_le_mul_of_nonneg_left h hc).trans
    (mul_le_mul_of_nonneg_right hc₀ (mul_nonneg hL hP))).trans_eq (mul_assoc _ _ _).symm

private theorem n06_two_term_difference_le {u v u' v' A B P : ℝ}
    (hu : |u - u'| ≤ A * P) (hv : |v - v'| ≤ B * P) :
    |(u - v) - (u' - v')| ≤ (A + B) * P := by
  have he : (u - v) - (u' - v') = (u - u') - (v - v') := by ring
  have htri : |(u - u') - (v - v')| ≤ |u - u'| + |v - v'| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (u - u') (v - v')
  exact (congrArg abs he).trans_le
    (htri.trans ((add_le_add hu hv).trans_eq (add_mul A B P).symm))

private theorem n06_norm_coordinate_array_sub_le
    (j : ℕ) (f : Fin 5 → ℝ) (u v : Fin 7 → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (h : ∀ i, |u i - v i| ≤ R) :
    ‖(![if j = 0 then f 0 else 0, if j = 0 then f 1 else 0,
        if j = 0 then f 2 else 0, if j = 0 then f 3 else 0,
        if j = 0 then f 4 else 0, u 0, u 1, u 2, u 3, u 4,
        if j = 0 then u 5 else 0, if j = 0 then u 6 else 0] : N06NuJetCoordinates) -
      ![if j = 0 then f 0 else 0, if j = 0 then f 1 else 0,
        if j = 0 then f 2 else 0, if j = 0 then f 3 else 0,
        if j = 0 then f 4 else 0, v 0, v 1, v 2, v 3, v 4,
        if j = 0 then v 5 else 0, if j = 0 then v 6 else 0]‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i <;>
    simp only [Pi.sub_apply, Matrix.cons_val_zero', Matrix.cons_val_succ', Real.norm_eq_abs]
  all_goals first
  | simpa only [sub_self, abs_zero] using hR
  | exact h 0
  | exact h 1
  | exact h 2
  | exact h 3
  | exact h 4
  | split_ifs <;> first
    | exact h 5
    | exact h 6
    | simpa only [sub_self, abs_zero] using hR

def N06NuCoordinateJetDifferenceBound (D : ReferenceData) (S : PhysicalSpacesData)
    (j : ℕ) (C : ℝ) : Prop :=
  ∀ (z w : AnnularState S × ℝ) r, r ∈ radialCore D → ∀ θ,
    ‖iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S z (r, t)) θ -
      iteratedDeriv j (fun t => n06ActualNuJetCoordinates D S w (r, t)) θ‖ ≤
        C * (stateGrading S (j + 4) (z.1 - w.1) + |z.2 - w.2|)

/-- One fixed original seminorm bounds the difference of the complete
actual finite coordinate packet, at every physical angle and radius. -/
theorem n06_actualNuJetCoordinates_angular_difference_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (j : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ N06NuCoordinateJetDifferenceBound D S j C := by
  obtain ⟨L, hL, hjet⟩ := n06_stateU_mixedDerivative_finite_difference_bound
    (D := D) (T := T) (S := S) hD hT hS (j + 2)
  have ha : 0 < D.a := hD.choose_spec.1.1
  let A : ℝ := (1 / D.a) * L
  let B : ℝ := (1 / D.a ^ 2) * L
  let C : ℝ := 1 + L + 2 * A + B
  have hA : 0 ≤ A := mul_nonneg (one_div_nonneg.mpr ha.le) hL
  have hB : 0 ≤ B := mul_nonneg (one_div_nonneg.mpr (sq_nonneg _)) hL
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hLC : L ≤ C := by dsimp only [C]; linarith
  have hAC : A ≤ C := by dsimp only [C]; linarith
  have hABC : A + B ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro z w r hr θ
  let P := stateGrading S (j + 4) (z.1 - w.1)
  let R := P + |z.2 - w.2|
  have hP : 0 ≤ P := apply_nonneg _ _
  have hR : 0 ≤ R := add_nonneg hP (abs_nonneg _)
  have hPR : P ≤ R := le_add_of_nonneg_right (abs_nonneg _)
  have hqR : |z.2 - w.2| ≤ R := le_add_of_nonneg_left hP
  have hpromote {c t : ℝ} (hc : 0 ≤ c) (hcC : c ≤ C) (ht : |t| ≤ c * P) :
      |t| ≤ C * R :=
    ht.trans ((mul_le_mul_of_nonneg_left hPR hc).trans
      (mul_le_mul_of_nonneg_right hcC hR))
  have hCR : R ≤ C * R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hR
  have hrpos : 0 < r := ha.trans hr.1
  have hri : (1 / r) ≤ 1 / D.a := one_div_le_one_div_of_le ha hr.1.le
  have hsq : D.a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha.le hr.1.le 2
  have hri₂ : (1 / r ^ 2) ≤ 1 / D.a ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos ha) hsq
  have hh (a b : ℕ) (hab : a + b ≤ j + 2) :
      |mixedDerivative a b (stateU S z.1) (r, θ) -
        mixedDerivative a b (stateU S w.1) (r, θ)| ≤ L * P := by
    simpa only [P, Nat.add_assoc] using hjet a b hab z.1 w.1 (r, θ) ⟨hr, mem_univ _⟩
  have h₁ := hpromote hL hLC (hh 1 j (by omega))
  have h₂ := hpromote hL hLC (hh 2 j (by omega))
  have h₃ := hpromote hA hAC
    (n06_scaled_difference_le (one_div_nonneg.mpr hrpos.le) hri hL hP (hh 0 (j + 1) (by omega)))
  have h₅ := hpromote hA hAC
    (n06_scaled_difference_le (one_div_nonneg.mpr hrpos.le) hri hL hP (hh 0 (j + 2) (by omega)))
  have h₄ : |((1 / r) * mixedDerivative 1 (j + 1) (stateU S z.1) (r, θ) -
        (1 / r ^ 2) * mixedDerivative 0 (j + 1) (stateU S z.1) (r, θ)) -
      ((1 / r) * mixedDerivative 1 (j + 1) (stateU S w.1) (r, θ) -
        (1 / r ^ 2) * mixedDerivative 0 (j + 1) (stateU S w.1) (r, θ))| ≤ C * R := by
    have hmain := n06_scaled_difference_le (one_div_nonneg.mpr hrpos.le) hri hL hP
      (hh 1 (j + 1) (by omega))
    have hlow := n06_scaled_difference_le (one_div_nonneg.mpr (sq_nonneg r)) hri₂ hL hP
      (hh 0 (j + 1) (by omega))
    exact hpromote (add_nonneg hA hB) hABC (n06_two_term_difference_le hmain hlow)
  have hν : |z.1.2.1 - w.1.2.1| ≤ C * R :=
    ((neighborhoodStateGrading_controls_le S (j + 4) (z.1 - w.1)).1.trans hPR).trans hCR
  let packet (y : AnnularState S × ℝ) : Fin 7 → ℝ :=
    ![mixedDerivative 1 j (stateU S y.1) (r, θ),
      mixedDerivative 2 j (stateU S y.1) (r, θ),
      (1 / r) * mixedDerivative 0 (j + 1) (stateU S y.1) (r, θ),
      (1 / r) * mixedDerivative 1 (j + 1) (stateU S y.1) (r, θ) -
        (1 / r ^ 2) * mixedDerivative 0 (j + 1) (stateU S y.1) (r, θ),
      (1 / r) * mixedDerivative 0 (j + 2) (stateU S y.1) (r, θ), y.2, y.1.2.1]
  have hpacket : ∀ i : Fin 7, |packet z i - packet w i| ≤ C * R := by
    intro i
    fin_cases i <;>
      first | exact h₁ | exact h₂ | exact h₃ | exact h₄ | exact h₅ |
        exact hqR.trans hCR | exact hν
  have hnorm : ‖n06NuCoordinateAngularJet D S z r θ j -
      n06NuCoordinateAngularJet D S w r θ j‖ ≤ C * R :=
    n06_norm_coordinate_array_sub_le j ![r, D.w r, deriv D.w r, D.chi r, deriv D.chi r]
      (packet z) (packet w) (mul_nonneg (zero_le_one.trans hC) hR) hpacket
  exact (congrArg₂ (fun a b : N06NuJetCoordinates => ‖a - b‖)
    (n06_actualNuJetCoordinates_angularJet_eq hT hS z hrpos.ne' j θ)
    (n06_actualNuJetCoordinates_angularJet_eq hT hS w hrpos.ne' j θ)).trans_le hnorm

end ContinuousFlexibility.Statements
