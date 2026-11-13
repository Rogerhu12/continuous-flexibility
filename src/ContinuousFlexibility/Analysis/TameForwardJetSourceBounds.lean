import ContinuousFlexibility.Analysis.TameInverseExpressions
import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Abstract ordered forward jets and source normalization

The parameter recurrence and the source-linear normalization use abstract
topological vector spaces. Concrete circle realizations are instantiated
only after these proofs, so their construction is not unfolded repeatedly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

section OrderedJets

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]
  {U : Set X} {L : X → Y →L[ℝ] Z}

/-- Any kernel with the actual zeroth value and directional recurrence
agrees with the given ordered tower. -/
theorem inverseForwardJet_eq_of_recurrence
    (hU : IsOpen U)
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (K : (n : ℕ) → X → (Fin n → X) → Y → Z)
    (hzero : ∀ x ∈ U, ∀ y, L x y = K 0 x Fin.elim0 y)
    (hstep : ∀ n x, x ∈ U → ∀ (v : Fin n → X) y h,
      HasProjectiveLineDerivAt (fun z => K n z v y)
        (K (n + 1) x (Fin.cons h v) y) x h) :
    ∀ n x, x ∈ U → ∀ (v : Fin n → X) y,
      inverseForwardJet J n x v y = K n x v y := by
  intro n
  induction n with
  | zero =>
    intro x hx v y
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    subst v
    exact (inverseForwardJet_zero J hx y).trans (hzero x hx y)
  | succ n ih =>
    intro x hx v y
    have hf := hasProjectiveLineDerivAt_inverseForwardJet
      J hx n (Fin.tail v) y (v 0)
    have hg : (fun z => K n z (Fin.tail v) y) =ᶠ[𝓝 x]
        (fun z => inverseForwardJet J n z (Fin.tail v) y) := by
      filter_upwards [hU.mem_nhds hx] with z hz
      exact (ih z hz (Fin.tail v) y).symm
    have heq := (hf.congr_germ hg).unique
      (hstep n x hx (Fin.tail v) y (v 0))
    simpa only [Fin.cons_self_tail] using heq

end OrderedJets

section SourceBounds

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Normalize only the linear source variable. -/
theorem linearMap_oneHigh_of_unitSourceBound
    (A : E →L[ℝ] F) (q : Seminorm ℝ F) (low high : Seminorm ℝ E)
    {C a : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ u, low u < 1 → q (A u) ≤ C * (a + high u)) :
    ∀ y, q (A y) ≤ C * (a * low y + high y) := by
  let B : E [×1]→L[ℝ] F :=
    ContinuousMultilinearMap.ofSubsingleton ℝ E F (0 : Fin 1) A
  have hB (w : Fin 1 → E) : B w = A (w 0) := by
    simp only [B, ContinuousMultilinearMap.ofSubsingleton_apply_apply]
  have hunit (w : Fin 1 → E) (hw : ∀ i, low (w i) < 1) :
      q (B w) ≤ C * (a + ∑ i, high (w i)) := by
    rw [hB]
    simpa only [Fin.sum_univ_one] using hlocal (w 0) (hw 0)
  intro y
  have hb := multilinear_bound_of_unitBall B q low high hC hunit
    (fun _ : Fin 1 => y)
  rw [hB] at hb
  have he : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  simpa only [multilinearTameSize, Fin.prod_univ_one, Fin.sum_univ_one,
    he, Finset.prod_empty, mul_one] using hb

/-- A translated source with no seminorm loss preserves one fixed low
base while the old parameter increments remain in a fixed low ball. -/
theorem linearMap_oneHigh_of_shiftedSourceKernel
    (A : E →L[ℝ] F) (q : Seminorm ℝ F) (low high : Seminorm ℝ E)
    {n : ℕ} (x : E) (v : Fin n → E) (τ : E → E)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hv : ∀ i, low (v i) ≤ R)
    (hτlow : ∀ u, low (τ u) ≤ low u)
    (hτhigh : ∀ u, high (τ u) ≤ high u)
    (hkernel : ∀ u, q (A u) ≤ C *
      multilinearTameSize low high (n + 1) (1 + high x) (Fin.cons (τ u) v)) :
    ∀ y, q (A y) ≤ C * R ^ (n + 1) *
      ((1 + high x + ∑ i, high (v i)) * low y + high y) := by
  classical
  let P : ℝ := R ^ (n + 1)
  let a : ℝ := 1 + high x + ∑ i, high (v i)
  have hP : 0 ≤ P := pow_nonneg (zero_le_one.trans hR) _
  apply linearMap_oneHigh_of_unitSourceBound A q low high (mul_nonneg hC hP)
  intro u hu
  let w : Fin (n + 1) → E := Fin.cons (τ u) v
  have hw (i : Fin (n + 1)) : low (w i) ≤ R := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hτlow u).trans (hu.le.trans hR)
    · exact hv j
  have hp (I : Finset (Fin (n + 1))) : (∏ i ∈ I, low (w i)) ≤ P := by
    have hcard : I.card ≤ n + 1 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ I)
    calc
      _ ≤ ∏ _i ∈ I, R := Finset.prod_le_prod₀
        (fun i _ => apply_nonneg _ _) (fun i _ => hw i)
      _ = R ^ I.card := by simp only [Finset.prod_const]
      _ ≤ P := pow_le_pow_right₀ hR hcard
  have hsum : (∑ i, high (w i)) ≤ high u + ∑ i, high (v i) := by
    simpa only [w, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
      add_le_add (hτhigh u) (le_refl (∑ i, high (v i)))
  have hmajor : multilinearTameSize low high (n + 1) (1 + high x) w ≤
      P * (a + high u) := by
    unfold multilinearTameSize
    calc
      _ ≤ (1 + high x) * P + ∑ i, high (w i) * P :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hp Finset.univ)
            (add_nonneg zero_le_one (apply_nonneg _ _)))
          (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
            (hp (Finset.univ.erase i)) (apply_nonneg _ _)))
      _ = P * (1 + high x + ∑ i, high (w i)) := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ P * (1 + high x + (high u + ∑ i, high (v i))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hP
      _ = P * (a + high u) := by dsimp only [a]; ring
  exact (hkernel u).trans
    ((mul_le_mul_of_nonneg_left hmajor hC).trans_eq (mul_assoc C P _).symm)

end SourceBounds

end ContinuousFlexibility.Analysis
