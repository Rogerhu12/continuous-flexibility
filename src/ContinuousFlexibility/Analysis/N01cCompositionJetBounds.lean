module

public import ContinuousFlexibility.Analysis.N01cCoefficientJetCalculus
public import ContinuousFlexibility.Analysis.N01cOneHighProducts
public import ContinuousFlexibility.Analysis.N01cOuterDenominatorJets

/-!
# Quantitative ordered-partition bounds for actual parameter jets

The first estimates retain the actual inner jets in the ordered-partition
formula for composition. The normalization theorem then starts from finite
sums of raw seminorm products. Each individual product carries its genuine
total spatial order. The entire continuous multilinear map is normalized
only after these products have been bounded on the low-seminorm unit ball.

The evaluation point and the grading increment are independent. Thus the
one-high expression can be centered at the fixed reference state. One base
and one loss work for every parameter order, spatial order and finite raw
expansion. Constants may depend on those finite orders and expansions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

section OrderedPartitionNorms

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The norm estimate for one actual ordered-partition composition term.
Only the intermediate and target spaces need norms. -/
theorem norm_projectiveCompositionTerm_le
    (u : X → Y) (J : ProjectiveJetFamily X Y) (g : Y → Z)
    {k : ℕ} (c : OrderedFinpartition k) (x : X) (v : Fin k → X) :
    ‖projectiveCompositionTerm u J (fun j => iteratedFDeriv ℝ j g) c x v‖ ≤
      ‖iteratedFDeriv ℝ c.length g (u x)‖ *
        ∏ i : Fin c.length, ‖J (c.partSize i) x (v ∘ c.emb i)‖ := by
  rw [projectiveCompositionTerm_apply]
  exact ContinuousMultilinearMap.le_opNorm _ _

/-- A bound for the actual composed tower by the actual inner tower.
No estimate for a formal or unverified derivative family is substituted. -/
theorem smoothDirections_contDiff_comp_D_norm_le
    {U : Set X} {V : Set Y} {u : X → Y} {g : Y → Z}
    (J : SmoothDirections U u) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo u U V) (k : ℕ) (x : X) (v : Fin k → X) :
    ‖(smoothDirections_contDiff_comp J hV hg hmap).D k x v‖ ≤
      ∑ c : OrderedFinpartition k,
        ‖iteratedFDeriv ℝ c.length g (u x)‖ *
          ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ := by
  rw [smoothDirections_contDiff_comp_D_apply]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun c _ => ContinuousMultilinearMap.le_opNorm _ _))

/-- A uniform outer-jet bound factors out of the actual partition sum. -/
theorem smoothDirections_contDiff_comp_D_norm_le_of_outer_bound
    {U : Set X} {V : Set Y} {u : X → Y} {g : Y → Z}
    (J : SmoothDirections U u) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo u U V) (k : ℕ) (x : X) (B : ℝ)
    (hB : ∀ j : ℕ, j ≤ k → ‖iteratedFDeriv ℝ j g (u x)‖ ≤ B)
    (v : Fin k → X) :
    ‖(smoothDirections_contDiff_comp J hV hg hmap).D k x v‖ ≤
      B * ∑ c : OrderedFinpartition k,
        ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ := by
  calc
    _ ≤ ∑ c : OrderedFinpartition k,
        ‖iteratedFDeriv ℝ c.length g (u x)‖ *
          ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ :=
      smoothDirections_contDiff_comp_D_norm_le J hV hg hmap k x v
    _ ≤ ∑ c : OrderedFinpartition k,
        B * ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_right
        (hB c.length c.length_le) (Finset.prod_nonneg (fun i _ => norm_nonneg _)))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The compact outer-jet theorem supplies one coefficient for every
evaluation point mapped into the same compact subset of the outer domain. -/
theorem smoothDirections_contDiff_comp_D_norm_bound_of_compact
    {U : Set X} {V : Set Y} {u : X → Y} {g : Y → Z}
    (J : SmoothDirections U u) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo u U V) {K : Set Y} (hK : IsCompact K) (hKV : K ⊆ V)
    (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : X, u x ∈ K → ∀ v : Fin k → X,
      ‖(smoothDirections_contDiff_comp J hV hg hmap).D k x v‖ ≤
        B * ∑ c : OrderedFinpartition k,
          ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ := by
  obtain ⟨B, hB, hb⟩ := compact_iteratedFDeriv_bound hK
    (fun y hy => hg.contDiffAt (hV.mem_nhds (hKV hy))) k
  refine ⟨B, hB, fun x hx v => ?_⟩
  exact smoothDirections_contDiff_comp_D_norm_le_of_outer_bound
    J hV hg hmap k x B (fun j hj => hb j hj (u x) hx) v

end OrderedPartitionNorms

section RawSumNormalization

variable {X Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Finite sums of raw products can be normalized without decomposing
their target multilinear map. Each summand has its own factors and slots;
its assigned spatial orders must add up to at most the output order. -/
theorem exists_oneHighMultilinearSumProductBounds
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    (hinterp : HasInterpolation p) (offset : ℕ) :
    ∃ base loss : ℕ,
      ∀ k s : ℕ, ∀ (ι : Type) [Fintype ι], ∀ factors : ι → ℕ,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ a : ∀ t, Fin (factors t) → ℕ,
        (∀ t, ∑ i, a t i ≤ s) →
        ∀ select : ∀ t, Fin (factors t) → Fin (k + 1),
        ∀ y : X, p base y ≤ 1 →
        ∀ A : X [×k]→L[ℝ] Z, ∀ K : ι → ℝ, (∀ t, 0 ≤ K t) →
        (∀ v : Fin k → X, ‖A v‖ ≤
          ∑ t, K t * ∏ i, p (a t i + offset) ((Fin.cons y v : Fin (k + 1) → X) (select t i))) →
        ∀ v : Fin k → X, ‖A v‖ ≤
          C * (∑ t, K t) * oneHighVariationWeight p base (s + loss) y v := by
  classical
  obtain ⟨base, loss, hproduct⟩ := exists_oneHighProductBounds p hp hinterp offset
  refine ⟨base, loss, ?_⟩
  intro k s ι inst factors
  choose c hc hcb using (fun t : ι => hproduct (factors t) s)
  let d : ι → ℝ := fun t => c t * ((factors t : ℝ) + 1)
  have hd (t : ι) : 0 ≤ d t :=
    mul_nonneg (hc t) (by positivity)
  let C : ℝ := ∑ t, d t
  have hC : 0 ≤ C := Finset.sum_nonneg (fun t _ => hd t)
  have hdC (t : ι) : d t ≤ C :=
    Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ t)
  refine ⟨C, hC, ?_⟩
  intro a ha select y hy A K hK hraw
  have hKsum : 0 ≤ ∑ t, K t := Finset.sum_nonneg (fun t _ => hK t)
  have hnormalized :
      ∀ v : Fin k → X, (normSeminorm ℝ Z) (A v) ≤
        C * (∑ t, K t) *
          multilinearTameSize (p base) (p (s + loss)) k
            (1 + p (s + loss) y) v := by
    apply multilinear_bound_of_unitBall A (normSeminorm ℝ Z)
      (p base) (p (s + loss)) (mul_nonneg hC hKsum)
    intro v hv
    let R : ℝ := p (s + loss) y + ∑ j, p (s + loss) (v j)
    have hy0 : 0 ≤ p (s + loss) y := apply_nonneg _ _
    have hv0 : 0 ≤ ∑ j, p (s + loss) (v j) :=
      Finset.sum_nonneg (fun j _ => apply_nonneg _ _)
    have hR : 0 ≤ R := add_nonneg hy0 hv0
    have hfactor (t : ι) :
        ∏ i, p (a t i + offset) ((Fin.cons y v : Fin (k + 1) → X) (select t i)) ≤
          C * ((1 + p (s + loss) y) + ∑ j, p (s + loss) (v j)) := by
      let w : Fin (factors t) → X := fun i => (Fin.cons y v : Fin (k + 1) → X) (select t i)
      have hw (i : Fin (factors t)) : p base (w i) ≤ 1 :=
        Fin.cases
          (motive := fun j : Fin (k + 1) =>
            p base ((Fin.cons y v : Fin (k + 1) → X) j) ≤ 1)
          hy (fun j => (hv j).le) (select t i)
      have hslot (i : Fin (factors t)) : p (s + loss) (w i) ≤ R := by
        have hyR : p (s + loss) y ≤ R := le_add_of_nonneg_right hv0
        have hvR (j : Fin k) : p (s + loss) (v j) ≤ R :=
          (Finset.single_le_sum (fun j _ => apply_nonneg (p (s + loss)) (v j))
            (Finset.mem_univ j)).trans (le_add_of_nonneg_left hy0)
        exact Fin.cases
          (motive := fun j : Fin (k + 1) =>
            p (s + loss) ((Fin.cons y v : Fin (k + 1) → X) j) ≤ R)
          hyR hvR (select t i)
      have hsumw : ∑ i, p (s + loss) (w i) ≤ (factors t : ℝ) * R := by
        calc
          _ ≤ ∑ _i : Fin (factors t), R :=
            Finset.sum_le_sum (fun i _ => hslot i)
          _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have haffine : 1 + ∑ i, p (s + loss) (w i) ≤
          ((factors t : ℝ) + 1) * (1 + R) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (factors t)]
      calc
        _ ≤ c t * (1 + ∑ i, p (s + loss) (w i)) := hcb t (a t) (ha t) w hw
        _ ≤ c t * (((factors t : ℝ) + 1) * (1 + R)) :=
          mul_le_mul_of_nonneg_left haffine (hc t)
        _ = d t * (1 + R) := by dsimp only [d]; ring
        _ ≤ C * (1 + R) :=
          mul_le_mul_of_nonneg_right (hdC t) (by linarith)
        _ = _ := by dsimp only [R]; ring
    have hb :
        ‖A v‖ ≤ C * (∑ t, K t) *
          ((1 + p (s + loss) y) + ∑ j, p (s + loss) (v j)) := by
      calc
        _ ≤ ∑ t, K t * ∏ i, p (a t i + offset) ((Fin.cons y v : Fin (k + 1) → X) (select t i)) :=
          hraw v
        _ ≤ ∑ t, K t *
            (C * ((1 + p (s + loss) y) + ∑ j, p (s + loss) (v j))) :=
          Finset.sum_le_sum (fun t _ =>
            mul_le_mul_of_nonneg_left (hfactor t) (hK t))
        _ = _ := by rw [← Finset.sum_mul]; ring
    simpa only [coe_normSeminorm] using hb
  intro v
  simpa only [coe_normSeminorm, multilinearTameSize, oneHighVariationWeight] using
    hnormalized v

end RawSumNormalization

section CompositionNormalization

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Ordered-partition composition with genuine distributed spatial orders.

The input is a finite raw expansion of each product of actual inner jets.
Every raw summand has total spatial order at most s. The conclusion has
one high factor, even if a partition has many blocks or its raw expansion
has many terms. The base and loss are fixed before all these choices.
The point x is the evaluation point; y is the increment used in the
seminorm ball and in the final one-high expression. -/
theorem exists_oneHighCompositionSumBounds
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p)
    (hinterp : HasInterpolation p) (offset : ℕ) :
    ∃ base loss : ℕ,
      ∀ k s : ℕ, ∀ terms : OrderedFinpartition k → ℕ,
      ∀ factors : ∀ c, Fin (terms c) → ℕ,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ {U : Set X} {V : Set Y} {u : X → Y} {g : Y → Z},
        ∀ J : SmoothDirections U u, ∀ hV : IsOpen V,
        ∀ hg : ContDiffOn ℝ ∞ g V, ∀ hmap : MapsTo u U V,
        ∀ a : ∀ c t, Fin (factors c t) → ℕ,
        (∀ c t, ∑ i, a c t i ≤ s) →
        ∀ select : ∀ c t, Fin (factors c t) → Fin (k + 1),
        ∀ x y : X, p base y ≤ 1 →
        ∀ B : OrderedFinpartition k → ℝ,
        ∀ K : ∀ c, Fin (terms c) → ℝ,
        (∀ c, 0 ≤ B c) → (∀ c t, 0 ≤ K c t) →
        (∀ c, ‖iteratedFDeriv ℝ c.length g (u x)‖ ≤ B c) →
        (∀ c (v : Fin k → X),
          (∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖) ≤
            ∑ t, K c t *
              ∏ i, p (a c t i + offset) ((Fin.cons y v : Fin (k + 1) → X) (select c t i))) →
        ∀ v : Fin k → X,
          ‖(smoothDirections_contDiff_comp J hV hg hmap).D k x v‖ ≤
            C * (∑ c, B c * ∑ t, K c t) *
              oneHighVariationWeight p base (s + loss) y v := by
  classical
  obtain ⟨base, loss, hnormalize⟩ :=
    exists_oneHighMultilinearSumProductBounds (Z := Z) p hp hinterp offset
  refine ⟨base, loss, ?_⟩
  intro k s terms factors
  let I : Type := Σ c : OrderedFinpartition k, Fin (terms c)
  obtain ⟨C, hC, hCb⟩ := hnormalize k s I (fun j => factors j.1 j.2)
  refine ⟨C, hC, ?_⟩
  intro U V u g J hV hg hmap a ha select x y hy B K hB hK houter hraw
  let A : X [×k]→L[ℝ] Z := (smoothDirections_contDiff_comp J hV hg hmap).D k x
  have hrawall (v : Fin k → X) :
      ‖A v‖ ≤ ∑ j : I, (B j.1 * K j.1 j.2) *
        ∏ i, p (a j.1 j.2 i + offset) ((Fin.cons y v : Fin (k + 1) → X) (select j.1 j.2 i)) := by
    calc
      _ ≤ ∑ c : OrderedFinpartition k,
          ‖iteratedFDeriv ℝ c.length g (u x)‖ *
            ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ :=
        smoothDirections_contDiff_comp_D_norm_le J hV hg hmap k x v
      _ ≤ ∑ c : OrderedFinpartition k,
          B c * (∑ t, K c t *
            ∏ i, p (a c t i + offset) ((Fin.cons y v : Fin (k + 1) → X) (select c t i))) :=
        Finset.sum_le_sum (fun c _ => mul_le_mul (houter c) (hraw c v)
          (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (hB c))
      _ = _ := by
        simp only [I, Fintype.sum_sigma, Finset.mul_sum, mul_assoc]
  have hb := hCb (fun j : I => a j.1 j.2)
    (fun j : I => ha j.1 j.2) (fun j : I => select j.1 j.2)
    y hy A (fun j : I => B j.1 * K j.1 j.2)
    (fun j : I => mul_nonneg (hB j.1) (hK j.1 j.2)) hrawall
  intro v
  simpa only [A, I, Fintype.sum_sigma, Finset.mul_sum] using hb v

end CompositionNormalization

end ContinuousFlexibility.Analysis
