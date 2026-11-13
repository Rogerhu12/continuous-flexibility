import ContinuousFlexibility.Analysis.TameInverseBounds
import ContinuousFlexibility.Analysis.TameJetLocalBounds
import ContinuousFlexibility.Analysis.SpacesInterpolationProducts

/-!
# A fixed low base for the existing inverse expressions

Only the original inputs enter the interpolation products.  A low-order
value of an intermediate expression is charged to the high-order budget;
it never becomes a new low-neighborhood hypothesis.  The final theorem
estimates the already constructed inverse tower.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

private theorem inverseInputProfile_product
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hI : HasInterpolation p) :
    ∃ base loss : ℕ, ∀ (a b : ℕ) (R : ℝ), 0 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} [Fintype ι] (x : ι → E),
        (∑ i, p base (x i)) ≤ R →
        (1 + ∑ i, p a (x i)) * (1 + ∑ i, p b (x i)) ≤
          C * (1 + ∑ i, p (a + b + loss) (x i)) := by
  classical
  obtain ⟨base, loss, hb⟩ := spaces_interpolation_pair_bound p (fun x _ _ h => hp h x) hI
  refine ⟨base, loss, fun a b R hR => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb a b (a + b) le_rfl
  have hxy (x y : E) :
      p a x * p b y ≤ C *
        (p (a + b + loss) x * p base y + p base x * p (a + b + loss) y) :=
    (mul_le_mul (hp (by omega) x) (hp (by omega) y)
      (apply_nonneg _ _) (apply_nonneg _ _)).trans (hc x y)
  refine ⟨3 + 2 * C * R, by positivity, ?_⟩
  intro ι _ x hx
  let H : ℝ := ∑ i, p (a + b + loss) (x i)
  let L : ℝ := ∑ i, p base (x i)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have ha : (∑ i, p a (x i)) ≤ H :=
    Finset.sum_le_sum (fun i _ => hp (by omega) (x i))
  have hbb : (∑ i, p b (x i)) ≤ H :=
    Finset.sum_le_sum (fun i _ => hp (by omega) (x i))
  have hcross : (∑ i, p a (x i)) * (∑ i, p b (x i)) ≤ 2 * C * R * H := by
    calc
      _ = ∑ i, ∑ j, p a (x i) * p b (x j) := by
        exact Fintype.sum_mul_sum _ _
      _ ≤ ∑ i, ∑ j, C *
          (p (a + b + loss) (x i) * p base (x j) +
            p base (x i) * p (a + b + loss) (x j)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hxy (x i) (x j)))
      _ = C * (H * L + L * H) := by
        dsimp only [L, H]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ = 2 * C * L * H := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx (mul_nonneg (by norm_num) hC)) hH
  dsimp only [H] at ha hbb hH hcross ⊢
  nlinarith [mul_nonneg hC hR]

private theorem inverseProfile_linear_step
    {I : Type*} (P f g : ℕ → I → ℝ)
    (hP : ∀ s i, 0 ≤ P s i) (hmono : ∀ i, Monotone (fun s => P s i))
    (base opLoss productLoss loss : ℕ)
    (hprod : ∀ a b, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i, P a i * P b i ≤ C * P (a + b + productLoss) i)
    (hf : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i, f s i ≤ C * P (s + loss) i)
    (hstep : ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i, g s i ≤ C * (P (s + opLoss) i * f base i + f (s + opLoss) i)) :
    ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i, g s i ≤ C * P (s + (opLoss + base + loss + productLoss)) i := by
  intro s
  obtain ⟨A, hA, ha⟩ := hf base
  obtain ⟨B, hB, hb⟩ := hf (s + opLoss)
  obtain ⟨D, hD, hd⟩ := hprod (s + opLoss) (base + loss)
  obtain ⟨C, hC, hc⟩ := hstep s
  refine ⟨C * (A * D + B), by positivity, fun i => ?_⟩
  have hfirst : P (s + opLoss) i * f base i ≤
      A * D * P (s + (opLoss + base + loss + productLoss)) i := by
    calc
      _ ≤ P (s + opLoss) i * (A * P (base + loss) i) :=
        mul_le_mul_of_nonneg_left (ha i) (hP _ _)
      _ = A * (P (s + opLoss) i * P (base + loss) i) := by ring
      _ ≤ A * (D * P ((s + opLoss) + (base + loss) + productLoss) i) :=
        mul_le_mul_of_nonneg_left (hd i) hA
      _ = _ := by simp only [Nat.add_assoc, mul_assoc]
  have hsecond := (hb i).trans (mul_le_mul_of_nonneg_left
    (hmono i (by omega : s + opLoss + loss ≤
      s + (opLoss + base + loss + productLoss))) hB)
  exact (hc i).trans ((mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC).trans_eq
    (by ring))

section Expressions

variable {E A : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
  {U : Set E} {L : E → E →L[ℝ] E}
  (q : ℕ → Seminorm ℝ E) (hq : Monotone q)
  (J : SmoothDirections (U ×ˢ univ) (fun z : E × E => L z.1 z.2))
  (V : E → E →L[ℝ] E)
  (operatorBase inverseLoss forwardLoss : ℕ)
  (hV : ∀ R : ℝ, 1 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ U, q operatorBase x ≤ R → ∀ y,
      q s (V x y) ≤ C * ((1 + q (s + inverseLoss) x) * q operatorBase y +
        q (s + inverseLoss) y))
  (hF : ∀ n (R : ℝ), 1 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ U, q operatorBase x ≤ R → ∀ v : Fin n → E,
      (∀ i, q operatorBase (v i) ≤ R) → ∀ y,
      q s (inverseForwardJet J n x v y) ≤ C *
        ((1 + q (s + (n + forwardLoss)) x + ∑ i, q (s + (n + forwardLoss)) (v i)) *
          q operatorBase y + q (s + (n + forwardLoss)) y))

include hq hV hF in
private theorem inverseExpression_fixedBase_growth
    (a : ℕ → Seminorm ℝ A) (ha : Monotone a)
    (base productLoss : ℕ) (hbase : operatorBase ≤ base)
    (hproduct : ∀ R : ℝ, 1 ≤ R → ∀ b c, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : (E × E) × A, pairGrading (pairGrading q q) a base z ≤ R →
        (1 + pairGrading (pairGrading q q) a b z) *
          (1 + pairGrading (pairGrading q q) a c z) ≤
        C * (1 + pairGrading (pairGrading q q) a (b + c + productLoss) z))
    (e : TameInverseExpression E E E A) (he : e.IsZeroLoss q q q a) :
    ∃ loss : ℕ, ∀ R : ℝ, 1 ≤ R → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : (E × E) × A, z.1.1 ∈ U →
        pairGrading (pairGrading q q) a base z ≤ R →
        pairGrading q q s (e.eval J V z.1 z.2) ≤
          C * (1 + pairGrading (pairGrading q q) a (s + loss) z) := by
  let d := pairGrading (pairGrading q q) a
  have hd : Monotone d := tamePairGrading_monotone (tamePairGrading_monotone hq hq) ha
  have hx (s) (z : (E × E) × A) : q s z.1.1 ≤ d s z := by
    simp only [d, pairGrading_apply]
    linarith [apply_nonneg (q s) z.1.2, apply_nonneg (a s) z.2]
  have hu (s) (z : (E × E) × A) : q s z.1.2 ≤ d s z := by
    simp only [d, pairGrading_apply]
    linarith [apply_nonneg (q s) z.1.1, apply_nonneg (a s) z.2]
  have hau (s) (z : (E × E) × A) : a s z.2 ≤ d s z := by
    simp only [d, pairGrading_apply]
    linarith [apply_nonneg (q s) z.1.1, apply_nonneg (q s) z.1.2]
  have hfst (s) (y : E × E) : q s y.1 ≤ pairGrading q q s y := by
    rw [pairGrading_apply]; exact le_add_of_nonneg_right (apply_nonneg _ _)
  have hsnd (s) (y : E × E) : q s y.2 ≤ pairGrading q q s y := by
    rw [pairGrading_apply]; exact le_add_of_nonneg_left (apply_nonneg _ _)
  induction e with
  | zero =>
      exact ⟨0, fun R hR s => ⟨0, le_rfl, fun z _ _ => by simp [TameInverseExpression.eval]⟩⟩
  | source =>
      refine ⟨0, fun R hR s => ⟨1, zero_le_one, fun z _ _ => ?_⟩⟩
      simpa only [TameInverseExpression.eval, d, pairGrading_apply, map_zero, zero_add,
        one_mul, Nat.add_zero] using (hu s z).trans (le_add_of_nonneg_left zero_le_one)
  | linearSource c =>
      refine ⟨0, fun R hR s => ?_⟩
      obtain ⟨C, hc⟩ := he s (Nat.zero_le s)
      refine ⟨C, C.coe_nonneg, fun z _ _ => ?_⟩
      exact (hc z.2).trans (mul_le_mul_of_nonneg_left
        ((hau s z).trans (le_add_of_nonneg_left zero_le_one)) C.coe_nonneg)
  | add e f ie iff =>
      obtain ⟨le, he'⟩ := ie he.1
      obtain ⟨lf, hf'⟩ := iff he.2
      refine ⟨max le lf, fun R hR s => ?_⟩
      obtain ⟨Ce, hCe, hce⟩ := he' R hR s
      obtain ⟨Cf, hCf, hcf⟩ := hf' R hR s
      refine ⟨Ce + Cf, add_nonneg hCe hCf, fun z hz hlow => ?_⟩
      have h₁ := (hce z hz hlow).trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hd (by omega : s + le ≤ s + max le lf) z)) hCe)
      have h₂ := (hcf z hz hlow).trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hd (by omega : s + lf ≤ s + max le lf) z)) hCf)
      exact (map_add_le_add (pairGrading q q s) _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))
  | neg e ie =>
      obtain ⟨loss, hb⟩ := ie he
      refine ⟨loss, fun R hR s => ?_⟩
      obtain ⟨C, hC, hc⟩ := hb R hR s
      refine ⟨C, hC, ?_⟩
      intro z hz hl
      simpa only [TameInverseExpression.eval, map_neg_eq_map] using hc z hz hl
  | inverse e ie =>
      obtain ⟨loss, hb⟩ := ie he
      refine ⟨inverseLoss + operatorBase + loss + productLoss, fun R hR => ?_⟩
      let I := {z : (E × E) × A // z.1.1 ∈ U ∧ d base z ≤ R}
      let P : ℕ → I → ℝ := fun s i => 1 + d s i.val
      have hstep (s : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i : I,
          pairGrading q q s ((TameInverseExpression.inverse e).eval J V i.val.1 i.val.2) ≤
            C * (P (s + inverseLoss) i *
              pairGrading q q operatorBase (e.eval J V i.val.1 i.val.2) +
                pairGrading q q (s + inverseLoss) (e.eval J V i.val.1 i.val.2)) := by
        obtain ⟨C, hC, hc⟩ := hV R hR s
        refine ⟨C, hC, fun i => ?_⟩
        have h := hc i.val.1.1 i.property.1
          ((hx _ i.val).trans ((hd hbase i.val).trans i.property.2))
          (e.eval J V i.val.1 i.val.2).2
        simpa only [TameInverseExpression.eval, pairGrading_apply, map_zero, add_zero] using
          h.trans (mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul (add_le_add le_rfl (hx _ i.val)) (hsnd _ _)
              (apply_nonneg _ _) (add_nonneg zero_le_one (apply_nonneg _ _)))
            (hsnd _ _)) hC)
      have hg := inverseProfile_linear_step P
        (fun s i => pairGrading q q s (e.eval J V i.val.1 i.val.2))
        (fun s i => pairGrading q q s ((TameInverseExpression.inverse e).eval J V i.val.1 i.val.2))
        (fun _ _ => add_nonneg zero_le_one (apply_nonneg _ _))
        (fun i _ _ h => add_le_add le_rfl (hd h i.val))
        operatorBase inverseLoss productLoss loss
        (fun b c => by
          obtain ⟨C, hC, hc⟩ := hproduct R hR b c
          exact ⟨C, hC, fun i => hc i.val i.property.2⟩)
        (fun s => by
          obtain ⟨C, hC, hc⟩ := hb R hR s
          exact ⟨C, hC, fun i => hc i.val i.property.1 i.property.2⟩) hstep
      intro s
      obtain ⟨C, hC, hc⟩ := hg s
      exact ⟨C, hC, fun z hz hl => hc ⟨z, hz, hl⟩⟩
  | forward n v e ie =>
      obtain ⟨loss, hb⟩ := ie he.2
      refine ⟨(n + forwardLoss) + operatorBase + loss + productLoss, fun R hR => ?_⟩
      choose cLow hcLow using fun i => he.1 i operatorBase (Nat.zero_le _)
      let R' : ℝ := (1 + ∑ i, (cLow i : ℝ)) * R
      have hRR : R ≤ R' := le_mul_of_one_le_left (zero_le_one.trans hR)
        (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (cLow i).coe_nonneg)))
      have hR' : 1 ≤ R' := hR.trans hRR
      let I := {z : (E × E) × A // z.1.1 ∈ U ∧ d base z ≤ R}
      let P : ℕ → I → ℝ := fun s i => 1 + d s i.val
      have hstep (s : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i : I,
          pairGrading q q s ((TameInverseExpression.forward n v e).eval J V i.val.1 i.val.2) ≤
            C * (P (s + (n + forwardLoss)) i *
              pairGrading q q operatorBase (e.eval J V i.val.1 i.val.2) +
                pairGrading q q (s + (n + forwardLoss)) (e.eval J V i.val.1 i.val.2)) := by
        choose cHigh hcHigh using fun i => he.1 i (s + (n + forwardLoss)) (Nat.zero_le _)
        let K : ℝ := 1 + ∑ i, (cHigh i : ℝ)
        have hK : 1 ≤ K := le_add_of_nonneg_right
          (Finset.sum_nonneg (fun i _ => (cHigh i).coe_nonneg))
        obtain ⟨C, hC, hc⟩ := hF n R' hR' s
        refine ⟨C * K, mul_nonneg hC (zero_le_one.trans hK), fun i => ?_⟩
        have hv (j : Fin n) : q operatorBase (v j i.val.2) ≤ R' := by
          have hAj : (cLow j : ℝ) ≤ 1 + ∑ i, (cLow i : ℝ) :=
            (Finset.single_le_sum (fun i _ => (cLow i).coe_nonneg) (Finset.mem_univ j)).trans
              (le_add_of_nonneg_left zero_le_one)
          exact (hcLow j i.val.2).trans ((mul_le_mul
            hAj ((hau _ i.val).trans ((hd hbase i.val).trans i.property.2))
            (apply_nonneg _ _) (by positivity)).trans_eq (by rfl))
        have hh := hc i.val.1.1 i.property.1
          (((hx _ i.val).trans ((hd hbase i.val).trans i.property.2)).trans hRR)
          (fun j => v j i.val.2) hv (e.eval J V i.val.1 i.val.2).1
        have hdirs : (∑ j, q (s + (n + forwardLoss)) (v j i.val.2)) ≤
          (∑ j, (cHigh j : ℝ)) * d (s + (n + forwardLoss)) i.val := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum (fun j _ => (hcHigh j i.val.2).trans
            (mul_le_mul_of_nonneg_left (hau _ i.val) (cHigh j).coe_nonneg))
        have hcoef : 1 + q (s + (n + forwardLoss)) i.val.1.1 +
            (∑ j, q (s + (n + forwardLoss)) (v j i.val.2)) ≤
          K * P (s + (n + forwardLoss)) i := by
          dsimp only [K, P]
          nlinarith [hx (s + (n + forwardLoss)) i.val,
            Finset.sum_nonneg (s := Finset.univ)
              (fun (j : Fin n) _ => (cHigh j).coe_nonneg)]
        have harg := add_le_add
          (mul_le_mul hcoef (hfst operatorBase (e.eval J V i.val.1 i.val.2)) (apply_nonneg _ _)
            (mul_nonneg (zero_le_one.trans hK) (add_nonneg zero_le_one (apply_nonneg _ _))))
          ((hfst (s + (n + forwardLoss)) (e.eval J V i.val.1 i.val.2)).trans
            (le_mul_of_one_le_left (apply_nonneg _ _) hK))
        simpa only [TameInverseExpression.eval, pairGrading_apply, map_zero, zero_add] using
          hh.trans ((mul_le_mul_of_nonneg_left harg hC).trans_eq (by ring))
      have hg := inverseProfile_linear_step P
        (fun s i => pairGrading q q s (e.eval J V i.val.1 i.val.2))
        (fun s i => pairGrading q q s ((TameInverseExpression.forward n v e).eval J V i.val.1 i.val.2))
        (fun _ _ => add_nonneg zero_le_one (apply_nonneg _ _))
        (fun i _ _ h => add_le_add le_rfl (hd h i.val))
        operatorBase (n + forwardLoss) productLoss loss
        (fun b c => by
          obtain ⟨C, hC, hc⟩ := hproduct R hR b c
          exact ⟨C, hC, fun i => hc i.val i.property.2⟩)
        (fun s => by
          obtain ⟨C, hC, hc⟩ := hb R hR s
          exact ⟨C, hC, fun i => hc i.val i.property.1 i.property.2⟩) hstep
      intro s
      obtain ⟨C, hC, hc⟩ := hg s
      exact ⟨C, hC, fun z hz hl => hc ⟨z, hz, hl⟩⟩

include hq hV hF in
/-- A single low base controls every order of the same inverse tower.
The two inputs are value estimates for the inverse operator and for the
actual ordered forward jets, not estimates for the desired inverse jets. -/
theorem inverseFamilySmoothDirections_fixedBase_oneHigh
    (hI : HasInterpolation (pairGrading q q))
    (hU : IsOpen U)
    (hleft : ∀ x ∈ U, ∀ y, V x (L x y) = y)
    (hright : ∀ x ∈ U, ∀ y, L x (V x y) = y)
    (hcont : ContinuousOn (fun z : E × E => V z.1 z.2) (U ×ˢ univ)) :
    ∃ base : ℕ, ∀ n : ℕ, ∃ loss : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ U ×ˢ univ, pairGrading q q base x ≤ R →
          ∀ v : Fin n → E × E,
            q s ((inverseFamilySmoothDirections J hU V hleft hright hcont).D n x v) ≤
              C * tameJetSize (pairGrading q q) n s loss base x v := by
  let p := pairGrading q q
  have hp : Monotone p := tamePairGrading_monotone hq hq
  obtain ⟨b, productLoss, hproduct⟩ := inverseInputProfile_product p hp hI
  let base : ℕ := max operatorBase b
  refine ⟨base, fun n => ?_⟩
  let a := tupleGrading (fun _ : Fin n => p)
  let d := jetGrading p n
  have ha : Monotone a := tupleGrading_monotone _ (fun _ => hp)
  have hd : Monotone d := jetGrading_monotone hp n
  have hprod : ∀ R : ℝ, 1 ≤ R → ∀ i j, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : (E × E) × (Fin n → E × E), d base z ≤ R →
        (1 + d i z) * (1 + d j z) ≤ C * (1 + d (i + j + productLoss) z) := by
    intro R hR i j
    obtain ⟨C, hC, hc⟩ := hproduct i j R (zero_le_one.trans hR)
    refine ⟨C, hC, fun z hz => ?_⟩
    have hl : (∑ k, p b ((Fin.cons z.1 z.2 : Fin (n + 1) → E × E) k)) ≤ R := by
      simpa only [d, jetGrading_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
        (hd (le_max_right operatorBase b) z).trans hz
    simpa only [d, jetGrading_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
      hc (Fin.cons z.1 z.2) hl
  obtain ⟨loss, hgrowth⟩ := inverseExpression_fixedBase_growth q hq J V
    operatorBase inverseLoss forwardLoss hV hF a ha base productLoss
    (le_max_left operatorBase b) hprod
    (inverseExpressionJet (X := E) (Y := E) (Z := E) n)
    (inverseExpressionJet_zeroLoss q q q n)
  refine ⟨loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hgrowth (R + n)
    (hR.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))) s
  refine ⟨C, hC, fun x hx hlow v => ?_⟩
  have hlocal (w : Fin n → E × E) (hw : ∀ i, p base (w i) < 1) :
      q s ((inverseFamilySmoothDirections J hU V hleft hright hcont).D n x w) ≤
        C * ((1 + p (s + loss) x) + ∑ i, p (s + loss) (w i)) := by
    have hsum : (∑ i, p base (w i)) ≤ (n : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hw i).le)
        _ = _ := by simp
    have hbox : d base (x, w) ≤ R + n := by
      simpa only [d, jetGrading_apply] using add_le_add hlow hsum
    rw [inverseFamilySmoothDirections_apply J hU V hleft hright hcont n hx.1]
    have hprojection : q s (inverseExpressionJetValue J V n x w).1 ≤
        pairGrading q q s (inverseExpressionJetValue J V n x w) := by
      rw [pairGrading_apply]
      exact le_add_of_nonneg_right (apply_nonneg _ _)
    have hbound := hc (x, w) hx.1 hbox
    exact hprojection.trans (by
      simpa only [inverseExpressionJetValue, pairGrading_apply, tupleGrading_apply,
        p, a, add_assoc] using hbound)
  exact multilinear_bound_of_unitBall
    ((inverseFamilySmoothDirections J hU V hleft hright hcont).D n x)
    (q s) (p base) (p (s + loss)) hC hlocal v

end Expressions

end ContinuousFlexibility.Analysis
