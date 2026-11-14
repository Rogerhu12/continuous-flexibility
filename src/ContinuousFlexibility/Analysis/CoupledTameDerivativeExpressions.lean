module

public import ContinuousFlexibility.Analysis.TameInverseExpressions
public import ContinuousFlexibility.Analysis.TameJetLocalBounds
public import ContinuousFlexibility.Analysis.TameLocalLinear

/-!
# Ordered expressions for the derivative evaluation

The derivative of `f` is evaluated jointly in its base point and its input.
An ordered jet keeps the input in its last slot.  Differentiation either
prepends a base increment or replaces that last input by its increment.
These two operations give finite expressions at every order without
assuming symmetry of higher directional derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section OrderedJets

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
variable {U : Set E} {f : E → F}

/-- The last slot is the input of the derivative evaluation. -/
def coupledOrderedJet (J : SmoothDirections U f)
    (n : ℕ) (x : E) (v : Fin n → E) (y : E) : F :=
  J.D (n + 1) x (Fin.snoc v y)

def coupledOrderedJetLast (J : SmoothDirections U f)
    (n : ℕ) (x : E) (v : Fin n → E) : E →L[ℝ] F :=
  (J.D (n + 1) x).toContinuousLinearMap (Fin.snoc v 0) (Fin.last n)

@[simp] theorem coupledOrderedJetLast_apply (J : SmoothDirections U f)
    (n : ℕ) (x : E) (v : Fin n → E) (y : E) :
    coupledOrderedJetLast J n x v y = coupledOrderedJet J n x v y := by
  simp only [coupledOrderedJetLast, ContinuousMultilinearMap.toContinuousLinearMap_apply,
    Fin.update_snoc_last, coupledOrderedJet]

def coupledOrderedJetHead (J : SmoothDirections U f)
    (n : ℕ) (x : E) (v : Fin n → E) (y : E) : E →L[ℝ] F :=
  (J.D (n + 2) x).toContinuousLinearMap (Fin.cons 0 (Fin.snoc v y)) 0

@[simp] theorem coupledOrderedJetHead_apply (J : SmoothDirections U f)
    (n : ℕ) (x : E) (v : Fin n → E) (y h : E) :
    coupledOrderedJetHead J n x v y h =
      coupledOrderedJet J (n + 1) x (Fin.cons h v) y := by
  rw [coupledOrderedJetHead, ContinuousMultilinearMap.toContinuousLinearMap_apply,
    Fin.update_cons_zero, coupledOrderedJet, Fin.cons_snoc_eq_snoc_cons]

theorem hasProjectiveLineDerivAt_coupledOrderedJet (J : SmoothDirections U f)
    {x : E} (hx : x ∈ U) (n : ℕ) (v : Fin n → E) (y h : E) :
    HasProjectiveLineDerivAt (fun z => coupledOrderedJet J n z v y)
      (coupledOrderedJet J (n + 1) x (Fin.cons h v) y) x h := by
  simpa only [coupledOrderedJet, Fin.cons_snoc_eq_snoc_cons] using
    J.derivative (n + 1) x hx (Fin.snoc v y) h

theorem continuousOn_coupledOrderedJet (J : SmoothDirections U f) (n : ℕ) :
    ContinuousOn
      (fun z : E × ((Fin n → E) × E) => coupledOrderedJet J n z.1 z.2.1 z.2.2)
      (U ×ˢ univ) := by
  have hinput : Continuous
      (fun z : E × ((Fin n → E) × E) =>
        Fin.snoc (α := fun _ : Fin (n + 1) => E) z.2.1 z.2.2) := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using continuous_snd.snd
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (continuous_apply j).comp continuous_snd.fst
  exact (J.continuous (n + 1)).comp
    (continuous_fst.prodMk hinput).continuousOn
    (fun z hz => ⟨hz.1, mem_univ _⟩)

/-- Varying the final input uses the ordinary variable-linear product
rule for actual difference quotients in the given topologies. -/
theorem coupledOrderedJet_curve_rule (J : SmoothDirections U f)
    {x : E} (hx : x ∈ U) (h : E) (n : ℕ) (v : Fin n → E)
    {c : ℝ → E} {dc : E} (hc : HasProjectiveCurveDerivAt c dc 0) :
    HasProjectiveCurveDerivAt
      (fun t : ℝ => coupledOrderedJet J n (x + t • h) v (c t))
      (coupledOrderedJet J (n + 1) x (Fin.cons h v) (c 0) +
        coupledOrderedJet J n x v dc) 0 := by
  have heval : ∀ y, ContinuousAt
      (fun p : ℝ × E => coupledOrderedJet J n (x + p.1 • h) v p.2) (0, y) := by
    intro y
    have hj := ((continuousOn_coupledOrderedJet J n) (x, (v, y))
      ⟨hx, mem_univ _⟩).continuousAt
        ((J.open_domain.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)
    have hm : Continuous (fun p : ℝ × E => (x + p.1 • h, (v, p.2))) :=
      (continuous_const.add (continuous_fst.smul continuous_const)).prodMk
        (continuous_const.prodMk continuous_snd)
    simpa only [Function.comp_def] using
      hj.comp_of_eq (hm.continuousAt (x := (0, y)))
        (by simp only [zero_smul, add_zero])
  have hd := hasProjectiveLineDerivAt_coupledOrderedJet J hx n v (c 0) h
  have hrule := inverseCurveDeriv_variableLinear
    (fun t => (coupledOrderedJetLast J n (x + t • h) v).toLinearMap)
    (c := c) (dc := dc) (t := 0)
    (dB := coupledOrderedJet J (n + 1) x (Fin.cons h v) (c 0))
    (by simpa only [ContinuousLinearMap.coe_coe, coupledOrderedJetLast_apply] using heval)
    hc
    (by simpa only [ContinuousLinearMap.coe_coe, coupledOrderedJetLast_apply,
      HasProjectiveLineDerivAt] using hd)
  simpa only [ContinuousLinearMap.coe_coe, coupledOrderedJetLast_apply,
    zero_smul, add_zero] using hrule

end OrderedJets

section Expressions

variable (E A : Type*)
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]

/-- Increments are auxiliary linear coordinates.  The last jet input is
either the current input or another auxiliary coordinate. -/
inductive CoupledDerivativeExpression where
  | current (n : ℕ) (v : Fin n → A →L[ℝ] E)
  | fixed (n : ℕ) (v : Fin n → A →L[ℝ] E) (u : A →L[ℝ] E)
  | add (e g : CoupledDerivativeExpression)

variable {E A} {F : Type*}
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
variable {U : Set E} {f : E → F}

def CoupledDerivativeExpression.eval (J : SmoothDirections U f) :
    CoupledDerivativeExpression E A → (E × E) → A → F
  | .current n v, z, a => coupledOrderedJet J n z.1 (fun i => v i a) z.2
  | .fixed n v u, z, a => coupledOrderedJet J n z.1 (fun i => v i a) (u a)
  | .add e g, z, a => e.eval J z a + g.eval J z a

variable {A' : Type*} [TopologicalSpace A'] [AddCommGroup A'] [Module ℝ A']

def CoupledDerivativeExpression.diff (e : CoupledDerivativeExpression E A)
    (g : A' →L[ℝ] A) (h : A' →L[ℝ] E × E) : CoupledDerivativeExpression E A' :=
  match e with
  | .current n v =>
      .add (.current (n + 1)
        (Fin.cons ((ContinuousLinearMap.fst ℝ E E).comp h) (fun i => (v i).comp g)))
        (.fixed n (fun i => (v i).comp g) ((ContinuousLinearMap.snd ℝ E E).comp h))
  | .fixed n v u => .fixed (n + 1)
      (Fin.cons ((ContinuousLinearMap.fst ℝ E E).comp h) (fun i => (v i).comp g))
      (u.comp g)
  | .add e e' => .add (e.diff g h) (e'.diff g h)

def CoupledDerivativeExpression.differential (J : SmoothDirections U f) :
    CoupledDerivativeExpression E A → (E × E) → A → (E × E) →L[ℝ] F
  | .current n v, z, a =>
      (coupledOrderedJetHead J n z.1 (fun i => v i a) z.2).comp
        (ContinuousLinearMap.fst ℝ E E) +
      (coupledOrderedJetLast J n z.1 (fun i => v i a)).comp
        (ContinuousLinearMap.snd ℝ E E)
  | .fixed n v u, z, a =>
      (coupledOrderedJetHead J n z.1 (fun i => v i a) (u a)).comp
        (ContinuousLinearMap.fst ℝ E E)
  | .add e g, z, a => e.differential J z a + g.differential J z a

theorem CoupledDerivativeExpression.eval_diff (e : CoupledDerivativeExpression E A)
    (J : SmoothDirections U f) (g : A' →L[ℝ] A) (h : A' →L[ℝ] E × E)
    (z : E × E) (a : A') :
    (e.diff g h).eval J z a = e.differential J z (g a) (h a) := by
  have hdirs (n : ℕ) (v : Fin n → A →L[ℝ] E) :
      (fun i : Fin (n + 1) =>
        Fin.cons (α := fun _ : Fin (n + 1) => A' →L[ℝ] E)
          ((ContinuousLinearMap.fst ℝ E E).comp h)
          (fun j => (v j).comp g) i a) =
        Fin.cons (α := fun _ : Fin (n + 1) => E)
          (h a).1 (fun j => v j (g a)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp only [Fin.cons_zero, Fin.cons_succ, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst']
  induction e with
  | current n v =>
      simp only [diff, eval, differential, add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        coupledOrderedJetHead_apply, coupledOrderedJetLast_apply, hdirs]
  | fixed n v u =>
      simp only [diff, eval, differential, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', coupledOrderedJetHead_apply, hdirs]
  | add e e' he he' => simp only [diff, eval, differential, add_apply, he, he']

theorem CoupledDerivativeExpression.continuousOn_eval (e : CoupledDerivativeExpression E A)
    (J : SmoothDirections U f) :
    ContinuousOn (fun z : (E × E) × A => e.eval J z.1 z.2)
      ((U ×ˢ univ) ×ˢ univ) := by
  induction e with
  | current n v =>
      have hv : Continuous (fun z : (E × E) × A => fun i => v i z.2) :=
        continuous_pi fun i => (v i).continuous.comp continuous_snd
      exact (continuousOn_coupledOrderedJet J n).comp
        (continuous_fst.fst.prodMk (hv.prodMk continuous_fst.snd)).continuousOn
        (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  | fixed n v u =>
      have hv : Continuous (fun z : (E × E) × A => fun i => v i z.2) :=
        continuous_pi fun i => (v i).continuous.comp continuous_snd
      exact (continuousOn_coupledOrderedJet J n).comp
        (continuous_fst.fst.prodMk (hv.prodMk (u.continuous.comp continuous_snd))).continuousOn
        (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  | add e g he hg => exact he.add hg

theorem CoupledDerivativeExpression.hasLineDerivAt_eval (e : CoupledDerivativeExpression E A)
    (J : SmoothDirections U f) {z : E × E} (hz : z.1 ∈ U) (a : A) (h : E × E) :
    HasProjectiveLineDerivAt (fun w => e.eval J w a)
      (e.differential J z a h) z h := by
  induction e with
  | current n v =>
      have hc : HasProjectiveCurveDerivAt (fun t : ℝ => z.2 + t • h.2) h.2 0 := by
        simpa only [HasProjectiveLineDerivAt, ContinuousLinearMap.id_apply] using
          hasProjectiveLineDerivAt_clm (ContinuousLinearMap.id ℝ E) z.2 h.2
      have hj := coupledOrderedJet_curve_rule J hz h.1 n (fun i => v i a) hc
      simpa only [HasProjectiveLineDerivAt, eval, differential, add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', coupledOrderedJetHead_apply,
        coupledOrderedJetLast_apply, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, zero_smul, add_zero] using hj
  | fixed n v u =>
      have hj := hasProjectiveLineDerivAt_coupledOrderedJet J hz n (fun i => v i a) (u a) h.1
      simpa only [HasProjectiveLineDerivAt, eval, differential,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        coupledOrderedJetHead_apply, Prod.fst_add, Prod.smul_fst] using hj
  | add e g he hg => exact he.add hg

end Expressions

section ExpressionBounds

variable {E A A' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
  [TopologicalSpace A'] [AddCommGroup A'] [Module ℝ A']

def CoupledDerivativeExpression.IsZeroLoss (p : ℕ → Seminorm ℝ E)
    (a : ℕ → Seminorm ℝ A) : CoupledDerivativeExpression E A → Prop
  | .current _ v => ∀ i, IsTameLinear a p (v i).toLinearMap 0 0
  | .fixed _ v u => (∀ i, IsTameLinear a p (v i).toLinearMap 0 0) ∧
      IsTameLinear a p u.toLinearMap 0 0
  | .add e g => e.IsZeroLoss p a ∧ g.IsZeroLoss p a

theorem CoupledDerivativeExpression.IsZeroLoss.diff
    {p : ℕ → Seminorm ℝ E} {a : ℕ → Seminorm ℝ A} {a' : ℕ → Seminorm ℝ A'}
    {e : CoupledDerivativeExpression E A} (he : e.IsZeroLoss p a)
    (g : A' →L[ℝ] A) (hg : IsTameLinear a' a g.toLinearMap 0 0)
    (h : A' →L[ℝ] E × E) (hh : IsTameLinear a' (pairGrading p p) h.toLinearMap 0 0) :
    (e.diff g h).IsZeroLoss p a' := by
  have hfst := inverseTame_comp_zero (inverseTame_fst p p) hh
  have hsnd := inverseTame_comp_zero (inverseTame_snd p p) hh
  have hcons (n : ℕ) (v : Fin n → A →L[ℝ] E)
      (hv : ∀ i, IsTameLinear a p (v i).toLinearMap 0 0) :
      ∀ i, IsTameLinear a' p
        ((Fin.cons (α := fun _ : Fin (n + 1) => A' →L[ℝ] E)
          ((ContinuousLinearMap.fst ℝ E E).comp h)
          (fun j => (v j).comp g)) i).toLinearMap 0 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hfst
    · exact inverseTame_comp_zero (hv j) hg
  induction e with
  | current n v =>
      exact ⟨hcons n v he, (fun i => inverseTame_comp_zero (he i) hg), hsnd⟩
  | fixed n v u => exact ⟨hcons n v he.1, inverseTame_comp_zero he.2 hg⟩
  | add e g ie ig => exact ⟨ie he.1, ig he.2⟩

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
variable {U : Set E} {f : E → F}

/-- Existing local bounds on the original jets control every expression.
Only coordinate maps and finite sums are used here. -/
theorem CoupledDerivativeExpression.locallyTameOn_eval
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {a : ℕ → Seminorm ℝ A}
    (hp : Monotone p) (ha : Monotone a)
    (e : CoupledDerivativeExpression E A) (he : e.IsZeroLoss p a)
    (J : SmoothDirections U f)
    (hJ : ∀ k, LocallyTameOn (jetGrading p k) q (U ×ˢ univ)
      (fun z => J.D k z.1 z.2)) :
    LocallyTameOn (pairGrading (pairGrading p p) a) q
      ((U ×ˢ univ) ×ˢ univ) (fun z => e.eval J z.1 z.2) := by
  let d := pairGrading (pairGrading p p) a
  let S : Set ((E × E) × A) := (U ×ˢ univ) ×ˢ univ
  have hd : Monotone d := tamePairGrading_monotone (tamePairGrading_monotone hp hp) ha
  have hstate : LocallyTameOn d (pairGrading p p) S (fun z => z.1) :=
    locallyTameOn_of_isTameLinear (ContinuousLinearMap.fst ℝ (E × E) A)
      (inverseTame_fst (pairGrading p p) a) S
  have hx : LocallyTameOn d p S (fun z => z.1.1) := inverseLocallyTame_fst hstate
  have hy : LocallyTameOn d p S (fun z => z.1.2) := inverseLocallyTame_snd hstate
  have haux : LocallyTameOn d a S (fun z => z.2) :=
    locallyTameOn_of_isTameLinear (ContinuousLinearMap.snd ℝ (E × E) A)
      (inverseTame_snd (pairGrading p p) a) S
  have hcoordinate (u : A →L[ℝ] E) (hu : IsTameLinear a p u.toLinearMap 0 0) :
      LocallyTameOn d p S (fun z => u z.2) :=
    (locallyTameOn_of_isTameLinear u hu univ).comp haux (fun _ _ => mem_univ _)
  have hordered (n : ℕ) (v : Fin n → A →L[ℝ] E)
      (hv : ∀ i, IsTameLinear a p (v i).toLinearMap 0 0)
      (u : (E × E) × A → E) (hu : LocallyTameOn d p S u) :
      LocallyTameOn d q S
        (fun z => coupledOrderedJet J n z.1.1 (fun i => v i z.2) (u z)) := by
    have hinput (i : Fin (n + 1)) : LocallyTameOn d p S
        (fun z => Fin.snoc (α := fun _ : Fin (n + 1) => E)
          (fun j => v j z.2) (u z) i) := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hu
      · simpa only [Fin.snoc_castSucc] using hcoordinate (v j) (hv j)
    exact (hJ (n + 1)).comp (hx.prodMk hd (LocallyTameOn.pi hd hinput))
      (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  induction e with
  | current n v => exact hordered n v he _ hy
  | fixed n v u => exact hordered n v he.1 _ (hcoordinate u he.2)
  | add e g ie ig => exact (ie he.1).add hd (ig he.2)

end ExpressionBounds

end ContinuousFlexibility.Analysis
