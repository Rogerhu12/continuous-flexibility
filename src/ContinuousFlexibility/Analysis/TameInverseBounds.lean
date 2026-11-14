module

public import ContinuousFlexibility.Analysis.TameInverseJets
public import ContinuousFlexibility.Analysis.TameLocalLinear

/-!
# Local tame bounds for the inverse expressions

Finite formulas are estimated as ordinary locally tame maps on the product
of the state and the old increments.  Multilinear normalization is applied
only after the complete directional tower has been constructed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators NNReal
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section LinearEstimates

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

theorem inverseTame_tupleTail (p : ℕ → Seminorm ℝ E) (n : ℕ) :
    IsTameLinear (tupleGrading (fun _ : Fin (n + 1) => p))
      (tupleGrading (fun _ : Fin n => p)) (inverseAuxTail E n).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  simp only [Nat.add_zero, NNReal.coe_one, one_mul, ContinuousLinearMap.coe_coe,
    inverseAuxTail_apply, tupleGrading_apply]
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (apply_nonneg _ _)

end LinearEstimates

section LinearInverseGrowth

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

/-- The homogeneous linear-family estimate implies ordinary local tame
growth in the joint parameter/source variables. -/
theorem locallyTameOn_inverse_of_linearFamilyTame
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hr : WithSeminorms r) {U : Set X} {V : X → Z →ₗ[ℝ] Y}
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))
    (hT : LinearFamilyTame p q r U V) :
    LocallyTameOn (pairGrading p r) q (U ×ˢ univ) (fun z : X × Z => V z.1 z.2) := by
  refine ⟨hV, ?_⟩
  intro z0 hz0
  obtain ⟨loss, base, hbound⟩ := hT
  let R : ℝ := r base z0.2 + 1
  let W : Set (X × Z) := (U ×ˢ univ) ∩ {z | r base z.2 < R}
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hW : W ∈ 𝓝[U ×ˢ univ] z0 := by
    refine inter_mem self_mem_nhdsWithin ?_
    apply mem_nhdsWithin_of_mem_nhds
    have hc : Continuous (fun z : X × Z => r base z.2) := by
      simpa only [Function.comp_def] using
        (hr.continuous_seminorm base).comp
          (continuous_snd : Continuous (fun z : X × Z => z.2))
    exact hc.continuousAt
      (Iio_mem_nhds (by dsimp [R]; linarith))
  refine ⟨loss, base, W, hW, ?_⟩
  intro s hs
  obtain ⟨C, hC, hb⟩ := hbound s hs
  refine ⟨C * (1 + R), mul_nonneg hC (by positivity), ?_⟩
  intro z hz
  have hbz := hb z.1 hz.1.1 z.2
  have hlow : r base z.2 ≤ R := hz.2.le
  have hpx : 0 ≤ p (s + loss) z.1 := apply_nonneg _ _
  have hry : 0 ≤ r (s + loss) z.2 := apply_nonneg _ _
  have hmul : (1 + p (s + loss) z.1) * r base z.2 ≤
      (1 + p (s + loss) z.1) * R :=
    mul_le_mul_of_nonneg_left hlow (by positivity)
  rw [pairGrading_apply]
  calc
    _ ≤ C * (r (s + loss) z.2 + (1 + p (s + loss) z.1) * r base z.2) := hbz
    _ ≤ C * (r (s + loss) z.2 + (1 + p (s + loss) z.1) * R) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hmul) hC
    _ ≤ C * ((1 + R) * (1 + (p (s + loss) z.1 + r (s + loss) z.2))) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hR hry]) hC
    _ = C * (1 + R) * (1 + (p (s + loss) z.1 + r (s + loss) z.2)) := by ring

end LinearInverseGrowth

section ExpressionLinearData

variable {X Y Z A A' : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
  [TopologicalSpace A'] [AddCommGroup A'] [Module ℝ A']

/-- All auxiliary linear maps in an expression have degree zero.  The
inverse and forward jet operations have their own fixed losses. -/
def TameInverseExpression.IsZeroLoss
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y) (r : ℕ → Seminorm ℝ Z)
    (a : ℕ → Seminorm ℝ A) : TameInverseExpression X Y Z A → Prop
  | .zero => True
  | .source => True
  | .linearSource c => IsTameLinear a (pairGrading q r) c.toLinearMap 0 0
  | .add e f => e.IsZeroLoss p q r a ∧ f.IsZeroLoss p q r a
  | .neg e => e.IsZeroLoss p q r a
  | .inverse e => e.IsZeroLoss p q r a
  | .forward _ v e => (∀ i, IsTameLinear a p (v i).toLinearMap 0 0) ∧ e.IsZeroLoss p q r a

theorem TameInverseExpression.IsZeroLoss.reparam
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {a : ℕ → Seminorm ℝ A} {a' : ℕ → Seminorm ℝ A'}
    {e : TameInverseExpression X Y Z A} (he : e.IsZeroLoss p q r a)
    (g : A' →L[ℝ] A) (hg : IsTameLinear a' a g.toLinearMap 0 0) :
    (e.reparam g).IsZeroLoss p q r a' := by
  induction e with
  | zero => trivial
  | source => trivial
  | linearSource c => exact inverseTame_comp_zero he hg
  | add e f ie iff => exact ⟨ie he.1, iff he.2⟩
  | neg e ie => exact ie he
  | inverse e ie => exact ie he
  | forward n v e ie =>
      exact ⟨fun i => inverseTame_comp_zero (he.1 i) hg, ie he.2⟩

theorem TameInverseExpression.IsZeroLoss.diff
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {a : ℕ → Seminorm ℝ A} {a' : ℕ → Seminorm ℝ A'}
    {e : TameInverseExpression X Y Z A} (he : e.IsZeroLoss p q r a)
    (g : A' →L[ℝ] A) (hg : IsTameLinear a' a g.toLinearMap 0 0)
    (h : A' →L[ℝ] X × Z) (hh : IsTameLinear a' (pairGrading p r) h.toLinearMap 0 0) :
    (e.diff g h).IsZeroLoss p q r a' := by
  have hfst := inverseTame_comp_zero (inverseTame_fst p r) hh
  have hsnd := inverseTame_comp_zero (inverseTame_snd p r) hh
  induction e with
  | zero => trivial
  | source => exact inverseTame_comp_zero (inverseTame_inr q r) hsnd
  | linearSource c => trivial
  | add e f ie iff => exact ⟨ie he.1, iff he.2⟩
  | neg e ie => exact ie he
  | inverse e ie =>
      exact ⟨ie he, ⟨fun _ => hfst, he.reparam g hg⟩⟩
  | forward n v e ie =>
      have hv : ∀ i, IsTameLinear a' p ((v i).comp g).toLinearMap 0 0 :=
        fun i => inverseTame_comp_zero (he.1 i) hg
      refine ⟨⟨?_, he.2.reparam g hg⟩, hv, ie he.2⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hfst
      · exact hv j

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]

theorem inverseExpressionJet_zeroLoss
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y) (r : ℕ → Seminorm ℝ Z) :
    ∀ n, (inverseExpressionJet (X := X) (Y := Y) (Z := Z) n).IsZeroLoss p q r
      (tupleGrading (fun _ : Fin n => pairGrading p r)) := by
  intro n
  induction n with
  | zero => trivial
  | succ n ih =>
      exact ih.diff (inverseAuxTail (X × Z) n) (inverseTame_tupleTail (pairGrading p r) n)
        (ContinuousLinearMap.proj 0) (inverseTame_tupleProjection (pairGrading p r) 0)

end ExpressionLinearData

section ExpressionGrowth

variable {X Y Z A : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
variable {U : Set X} {L : X → Y →L[ℝ] Z}

/-- Every inverse expression has local tame growth provided the forward
jets and the inverse itself have value estimates. -/
theorem TameInverseExpression.locallyTameOn_eval
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {a : ℕ → Seminorm ℝ A}
    (hp : Monotone p) (hq : Monotone q) (hr : Monotone r) (ha : Monotone a)
    (e : TameInverseExpression X Y Z A) (he : e.IsZeroLoss p q r a)
    (J : SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y)
    (hV : LocallyTameOn (pairGrading p r) q (U ×ˢ univ) (fun z : X × Z => V z.1 z.2))
    (hJ : ∀ k, LocallyTameOn
      (pairGrading (pairGrading p q) (tupleGrading (fun _ : Fin k => pairGrading p q)))
      r ((U ×ˢ univ) ×ˢ univ) (fun z => J.D k z.1 z.2)) :
    LocallyTameOn (pairGrading (pairGrading p r) a) (pairGrading q r)
      ((U ×ˢ univ) ×ˢ univ) (fun z => e.eval J V z.1 z.2) := by
  let d := pairGrading (pairGrading p r) a
  let S : Set ((X × Z) × A) := (U ×ˢ univ) ×ˢ univ
  have hd : Monotone d := tamePairGrading_monotone (tamePairGrading_monotone hp hr) ha
  have hstate : LocallyTameOn d (pairGrading p r) S (fun z => z.1) :=
    locallyTameOn_of_isTameLinear (ContinuousLinearMap.fst ℝ (X × Z) A)
      (inverseTame_fst (pairGrading p r) a) S
  have hx : LocallyTameOn d p S (fun z => z.1.1) := inverseLocallyTame_fst hstate
  have hy : LocallyTameOn d r S (fun z => z.1.2) := inverseLocallyTame_snd hstate
  have haux : LocallyTameOn d a S (fun z => z.2) :=
    locallyTameOn_of_isTameLinear (ContinuousLinearMap.snd ℝ (X × Z) A)
      (inverseTame_snd (pairGrading p r) a) S
  induction e with
  | zero => exact locallyTameOn_const d (pairGrading q r) S 0
  | source => exact (locallyTameOn_const d q S (0 : Y)).prodMk hd hy
  | linearSource c =>
      exact (locallyTameOn_of_isTameLinear c he univ).comp haux (fun _ _ => mem_univ _)
  | add e f ie iff => exact (ie he.1).add hd (iff he.2)
  | neg e ie => exact (ie he).neg
  | inverse e ie =>
      have hs := inverseLocallyTame_snd (ie he)
      have harg := hx.prodMk hd hs
      have hi := hV.comp harg (fun z hz => ⟨hz.1.1, mem_univ _⟩)
      exact hi.prodMk hd (locallyTameOn_const d r S (0 : Z))
  | forward n v e ie =>
      have heval := inverseLocallyTame_fst (ie he.2)
      have hdirs (i : Fin n) : LocallyTameOn d p S (fun z => v i z.2) :=
        (locallyTameOn_of_isTameLinear (v i) (he.1 i) univ).comp haux
          (fun _ _ => mem_univ _)
      have hinput (i : Fin (n + 1)) : LocallyTameOn d (pairGrading p q) S
          (fun z => Fin.snoc (α := fun _ : Fin (n + 1) => X × Y)
            (fun j => (v j z.2, (0 : Y)))
            ((0 : X), (e.eval J V z.1 z.2).1) i) := by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using
            (locallyTameOn_const d p S (0 : X)).prodMk hd heval
        · simpa only [Fin.snoc_castSucc] using
            (hdirs j).prodMk hd (locallyTameOn_const d q S (0 : Y))
      have hargs := (hx.prodMk hd (locallyTameOn_const d q S (0 : Y))).prodMk hd
        (LocallyTameOn.pi hd hinput)
      have hj := (hJ (n + 1)).comp hargs
        (fun z hz => ⟨⟨hz.1.1, mem_univ _⟩, mem_univ _⟩)
      exact (locallyTameOn_const d q S (0 : Y)).prodMk hd hj

end ExpressionGrowth

end ContinuousFlexibility.Analysis
