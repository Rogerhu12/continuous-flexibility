module

public import ContinuousFlexibility.Analysis.TameInverseFamily

/-!
# Expressions for all derivatives of an inverse family

Only two nonlinear operations are needed: applying the continuous inverse
and evaluating a parameter derivative of the forward family.  Finite
expressions in these operations are closed under differentiation.  The
codomain is `Y × Z`, which allows both operations to belong to one expression
type without dependent output casts.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section ForwardJets

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]
variable {U : Set X} {L : X → Y →L[ℝ] Z}

/-- The ordered parameter jets of the forward family.  The source increment
is the last slot, so the tower's derivative recurrence prepends every new
parameter increment without requiring Schwarz symmetry. -/
def inverseForwardJet
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (n : ℕ) (x : X) (v : Fin n → X) (y : Y) : Z :=
  J.D (n + 1) (x, 0) (Fin.snoc (fun i => (v i, 0)) (0, y))

/-- At order zero, differentiation in the source recovers the original
linear family. -/
theorem inverseForwardJet_zero
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    {x : X} (hx : x ∈ U) (y : Y) :
    inverseForwardJet J 0 x Fin.elim0 y = L x y := by
  have h := J.derivative 0 (x, 0) ⟨hx, mem_univ _⟩ Fin.elim0 (0, y)
  have hcurve : (fun t : ℝ => J.D 0 ((x, 0) + t • ((0, y) : X × Y)) Fin.elim0) =
      (fun t : ℝ => t • L x y) := by
    funext t
    have he : (x, 0) + t • ((0, y) : X × Y) = (x, t • y) := by
      change (x + t • (0 : X), (0 : Y) + t • y) = _
      simp only [smul_zero, add_zero, zero_add]
    rw [he]
    simpa only [map_smul] using J.zero (x, t • y) ⟨hx, mem_univ _⟩
  unfold HasProjectiveLineDerivAt at h
  rw [hcurve] at h
  have hlinear : HasProjectiveCurveDerivAt (fun t : ℝ => t • L x y) (L x y) 0 := by
    simpa only [HasProjectiveLineDerivAt, ContinuousLinearMap.id_apply, zero_add] using
      hasProjectiveLineDerivAt_clm (ContinuousLinearMap.id ℝ Z) 0 (L x y)
  convert h.unique hlinear using 1
  unfold inverseForwardJet
  congr 1
  funext i
  fin_cases i
  rfl

/-- The partial source map of every parameter jet is genuinely continuous
linear in the source. -/
def inverseForwardJetLinear
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (n : ℕ) (x : X) (v : Fin n → X) : Y →L[ℝ] Z :=
  ((J.D (n + 1) (x, 0)).toContinuousLinearMap
    (Fin.snoc (fun i => (v i, 0)) (0 : X × Y)) (Fin.last n)).comp
      (ContinuousLinearMap.inr ℝ X Y)

@[simp] theorem inverseForwardJetLinear_apply
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (n : ℕ) (x : X) (v : Fin n → X) (y : Y) :
    inverseForwardJetLinear J n x v y = inverseForwardJet J n x v y := by
  simp only [inverseForwardJetLinear, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, ContinuousLinearMap.inr_apply,
    Fin.update_snoc_last, inverseForwardJet]

/-- Fixing the old increments gives a continuous linear map in the new
parameter increment. -/
def inverseForwardJetHead
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (n : ℕ) (x : X) (v : Fin n → X) (y : Y) : X →L[ℝ] Z :=
  ((J.D (n + 2) (x, 0)).toContinuousLinearMap
    (Fin.cons (0 : X × Y) (Fin.snoc (fun i => (v i, 0)) (0, y))) 0).comp
      (ContinuousLinearMap.inl ℝ X Y)

@[simp] theorem inverseForwardJetHead_apply
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (n : ℕ) (x : X) (v : Fin n → X) (y : Y) (h : X) :
    inverseForwardJetHead J n x v y h =
      inverseForwardJet J (n + 1) x (Fin.cons h v) y := by
  rw [inverseForwardJetHead, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, ContinuousLinearMap.inl_apply,
    Fin.update_cons_zero]
  unfold inverseForwardJet
  congr 1
  rw [Fin.cons_snoc_eq_snoc_cons]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Every parameter derivative is the next ordered jet. -/
theorem hasProjectiveLineDerivAt_inverseForwardJet
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    {x : X} (hx : x ∈ U) (n : ℕ) (v : Fin n → X) (y : Y) (h : X) :
    HasProjectiveLineDerivAt (fun z => inverseForwardJet J n z v y)
      (inverseForwardJet J (n + 1) x (Fin.cons h v) y) x h := by
  have hd := J.derivative (n + 1) (x, 0) ⟨hx, mem_univ _⟩
    (Fin.snoc (fun i => (v i, 0)) (0, y)) (h, 0)
  have hi : Fin.cons (h, (0 : Y)) (Fin.snoc (fun i => (v i, 0)) (0, y)) =
      Fin.snoc (α := fun _ : Fin (n + 2) => X × Y)
        (fun i => (Fin.cons (α := fun _ : Fin (n + 1) => X) h v i, (0 : Y)))
        ((0 : X), y) := by
    rw [Fin.cons_snoc_eq_snoc_cons]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simpa only [HasProjectiveLineDerivAt, inverseForwardJet,
    Prod.smul_mk, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
    smul_zero, add_zero, zero_add, hi] using hd

/-- Joint continuity of the ordered forward jets. -/
theorem continuousOn_inverseForwardJet
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (n : ℕ) :
    ContinuousOn
      (fun z : X × ((Fin n → X) × Y) => inverseForwardJet J n z.1 z.2.1 z.2.2)
      (U ×ˢ univ) := by
  have hinput : Continuous
      (fun z : X × ((Fin n → X) × Y) =>
        Fin.snoc (α := fun _ : Fin (n + 1) => X × Y)
          (fun i => (z.2.1 i, (0 : Y))) ((0 : X), z.2.2)) := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using continuous_const.prodMk continuous_snd.snd
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (((continuous_apply j).comp continuous_snd.fst).prodMk continuous_const)
  exact (J.continuous (n + 1)).comp
    (((continuous_fst.prodMk continuous_const).prodMk hinput).continuousOn)
    (fun z hz => ⟨⟨hz.1, mem_univ _⟩, mem_univ _⟩)

end ForwardJets

section Expressions

variable (X Y Z A : Type*)
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]

/-- Finite formulas built from the inverse and the ordered forward jets.
The auxiliary parameter stores previously introduced increments. -/
inductive TameInverseExpression where
  | zero
  | source
  | linearSource (c : A →L[ℝ] Y × Z)
  | add (e f : TameInverseExpression)
  | neg (e : TameInverseExpression)
  | inverse (e : TameInverseExpression)
  | forward (n : ℕ) (v : Fin n → A →L[ℝ] X) (e : TameInverseExpression)

variable {X Y Z A}
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]
variable {U : Set X} {L : X → Y →L[ℝ] Z}

def TameInverseExpression.eval
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y) : TameInverseExpression X Y Z A → (X × Z) → A → Y × Z
  | .zero, _, _ => 0
  | .source, z, _ => (0, z.2)
  | .linearSource c, _, a => c a
  | .add e f, z, a => e.eval J V z a + f.eval J V z a
  | .neg e, z, a => -e.eval J V z a
  | .inverse e, z, a => (V z.1 (e.eval J V z a).2, 0)
  | .forward n v e, z, a =>
      (0, inverseForwardJet J n z.1 (fun i => v i a) (e.eval J V z a).1)

variable {A' : Type*} [TopologicalSpace A'] [AddCommGroup A'] [Module ℝ A']

def TameInverseExpression.reparam (e : TameInverseExpression X Y Z A)
    (g : A' →L[ℝ] A) : TameInverseExpression X Y Z A' :=
  match e with
  | .zero => .zero
  | .source => .source
  | .linearSource c => .linearSource (c.comp g)
  | .add e f => .add (e.reparam g) (f.reparam g)
  | .neg e => .neg (e.reparam g)
  | .inverse e => .inverse (e.reparam g)
  | .forward n v e => .forward n (fun i => (v i).comp g) (e.reparam g)

@[simp] theorem TameInverseExpression.eval_reparam
    (e : TameInverseExpression X Y Z A)
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y) (g : A' →L[ℝ] A) (z : X × Z) (a : A') :
    (e.reparam g).eval J V z a = e.eval J V z (g a) := by
  induction e with
  | zero => rfl
  | source => rfl
  | linearSource c => simp only [reparam, eval, ContinuousLinearMap.comp_apply]
  | add e f he hf => simp only [reparam, eval, he, hf]
  | neg e he => simp only [reparam, eval, he]
  | inverse e he => simp only [reparam, eval, he]
  | forward n v e he => simp only [reparam, eval, ContinuousLinearMap.comp_apply, he]

/-- Formal differentiation in the base.  Old auxiliary increments are
pulled back by `g`; the new joint parameter/source increment is `h`. -/
def TameInverseExpression.diff (e : TameInverseExpression X Y Z A)
    (g : A' →L[ℝ] A) (h : A' →L[ℝ] X × Z) : TameInverseExpression X Y Z A' :=
  match e with
  | .zero => .zero
  | .source => .linearSource
      ((ContinuousLinearMap.inr ℝ Y Z).comp ((ContinuousLinearMap.snd ℝ X Z).comp h))
  | .linearSource _ => .zero
  | .add e f => .add (e.diff g h) (f.diff g h)
  | .neg e => .neg (e.diff g h)
  | .inverse e => .add (.inverse (e.diff g h))
      (.neg (.inverse (.forward 1 (fun _ => (ContinuousLinearMap.fst ℝ X Z).comp h)
        (.inverse (e.reparam g)))))
  | .forward n v e =>
      .add (.forward (n + 1)
        (Fin.cons ((ContinuousLinearMap.fst ℝ X Z).comp h) (fun i => (v i).comp g))
        (e.reparam g))
        (.forward n (fun i => (v i).comp g) (e.diff g h))

/-- The same formal differential, packaged as an actual continuous linear
map in the new increment. -/
def TameInverseExpression.differential
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y) : TameInverseExpression X Y Z A → (X × Z) → A →
      (X × Z) →L[ℝ] Y × Z
  | .zero, _, _ => 0
  | .source, _, _ => (ContinuousLinearMap.inr ℝ Y Z).comp (ContinuousLinearMap.snd ℝ X Z)
  | .linearSource _, _, _ => 0
  | .add e f, z, a => e.differential J V z a + f.differential J V z a
  | .neg e, z, a => -e.differential J V z a
  | .inverse e, z, a =>
      (ContinuousLinearMap.inl ℝ Y Z).comp ((V z.1).comp
        ((ContinuousLinearMap.snd ℝ Y Z).comp (e.differential J V z a) -
          (inverseForwardJetHead J 0 z.1 Fin.elim0 (V z.1 (e.eval J V z a).2)).comp
            (ContinuousLinearMap.fst ℝ X Z)))
  | .forward n v e, z, a =>
      (ContinuousLinearMap.inr ℝ Y Z).comp
        ((inverseForwardJetHead J n z.1 (fun i => v i a) (e.eval J V z a).1).comp
            (ContinuousLinearMap.fst ℝ X Z) +
          (inverseForwardJetLinear J n z.1 (fun i => v i a)).comp
            ((ContinuousLinearMap.fst ℝ Y Z).comp (e.differential J V z a)))

/-- Formal differentiation agrees with the continuous linear differential
at every base point; this identity is algebraic. -/
theorem TameInverseExpression.eval_diff
    (e : TameInverseExpression X Y Z A)
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y) (g : A' →L[ℝ] A) (h : A' →L[ℝ] X × Z)
    (z : X × Z) (a : A') :
    (e.diff g h).eval J V z a = e.differential J V z (g a) (h a) := by
  induction e with
  | zero => simp only [diff, eval, differential, zero_apply]
  | source => simp only [diff, eval, differential, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply]
  | linearSource c => simp only [diff, eval, differential, zero_apply]
  | add e f he hf => simp only [diff, eval, differential, add_apply, he, hf]
  | neg e he => simp only [diff, eval, differential, neg_apply, he]
  | inverse e he =>
      have hdir : (fun _ : Fin 1 => (h a).1) = Fin.cons (h a).1 Fin.elim0 := by
        funext i
        fin_cases i
        rfl
      simp only [diff, eval, differential, eval_reparam, he,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        sub_apply, inverseForwardJetHead_apply, map_sub,
        ← sub_eq_add_neg, Prod.mk_sub_mk, sub_self, hdir]
  | forward n v e he =>
      have hdirs :
          (fun i : Fin (n + 1) =>
            Fin.cons (α := fun _ : Fin (n + 1) => A' →L[ℝ] X)
              ((ContinuousLinearMap.fst ℝ X Z).comp h)
              (fun j => (v j).comp g) i a) =
            Fin.cons (α := fun _ : Fin (n + 1) => X)
              (h a).1 (fun j => v j (g a)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp only [Fin.cons_zero, Fin.cons_succ, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.coe_fst']
      simp only [diff, eval, differential, eval_reparam, he,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        add_apply, inverseForwardJetHead_apply,
        inverseForwardJetLinear_apply, Prod.mk_add_mk, zero_add, hdirs]

/-- Continuity of every expression is joint in the base and all old
increments. -/
theorem TameInverseExpression.continuousOn_eval
    (e : TameInverseExpression X Y Z A)
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ)) :
    ContinuousOn (fun p : (X × Z) × A => e.eval J V p.1 p.2)
      ((U ×ˢ univ) ×ˢ univ) := by
  induction e with
  | zero => exact continuousOn_const
  | source => exact (continuous_const.prodMk continuous_fst.snd).continuousOn
  | linearSource c => exact (c.continuous.comp continuous_snd).continuousOn
  | add e f he hf => exact he.add hf
  | neg e he => exact he.neg
  | inverse e he =>
      exact (hV.comp (continuous_fst.fst.continuousOn.prodMk he.snd)
        (fun p hp => ⟨hp.1.1, mem_univ _⟩)).prodMk continuousOn_const
  | forward n v e he =>
      have hv : Continuous (fun p : (X × Z) × A => (fun i => v i p.2)) :=
        continuous_pi fun i => (v i).continuous.comp continuous_snd
      exact continuousOn_const.prodMk
        ((continuousOn_inverseForwardJet J n).comp
          (continuous_fst.fst.continuousOn.prodMk (hv.continuousOn.prodMk he.fst))
          (fun p hp => ⟨hp.1.1, mem_univ _⟩))

end Expressions

section CurveRules

variable {P Q : Type*}
  [TopologicalSpace P] [AddCommGroup P] [Module ℝ P]
  [TopologicalSpace Q] [AddCommGroup Q] [Module ℝ Q]

/-- Curve derivatives commute with finite Cartesian products. -/
theorem inverseCurveDeriv_prod
    {f : ℝ → P} {g : ℝ → Q} {df : P} {dg : Q} {t : ℝ}
    (hf : HasProjectiveCurveDerivAt f df t) (hg : HasProjectiveCurveDerivAt g dg t) :
    HasProjectiveCurveDerivAt (fun s => (f s, g s)) (df, dg) t := by
  exact Filter.Tendsto.prodMk_nhds hf hg

variable [IsTopologicalAddGroup Q]

/-- The variable-linear-map curve rule in a topological vector space,
proved by one exact difference-quotient identity. -/
theorem inverseCurveDeriv_variableLinear
    (B : ℝ → P →ₗ[ℝ] Q) {c : ℝ → P} {dc : P} {dB : Q} {t : ℝ}
    (hB : ∀ w, ContinuousAt (fun p : ℝ × P => B p.1 p.2) (t, w))
    (hc : HasProjectiveCurveDerivAt c dc t)
    (hdB : HasProjectiveCurveDerivAt (fun s => B s (c t)) dB t) :
    HasProjectiveCurveDerivAt (fun s => B s (c s)) (dB + B t dc) t := by
  have hshift : Tendsto (fun h : ℝ => t + h) (𝓝[≠] (0 : ℝ)) (𝓝 t) := by
    simpa only [add_zero, id_eq] using (tendsto_const_nhds (x := t)).add
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  have ht := (hB dc).tendsto.comp (hshift.prodMk_nhds hc)
  unfold HasProjectiveCurveDerivAt at hdB ⊢
  apply (hdB.add ht).congr'
  exact Eventually.of_forall (fun h => by
    change h⁻¹ • (B (t + h) (c t) - B t (c t)) +
        B (t + h) (h⁻¹ • (c (t + h) - c t)) =
      h⁻¹ • (B (t + h) (c (t + h)) - B t (c t))
    rw [map_smul, map_sub, ← smul_add]
    congr 1
    abel)

end CurveRules

section ExpressionDerivatives

variable {X Y Z A : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
variable {U : Set X} {L : X → Y →L[ℝ] Z}

/-- A forward jet, with its source varying along a differentiable curve. -/
theorem inverseForwardJet_curve_rule
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (hU : IsOpen U) {x : X} (hx : x ∈ U) (h : X)
    (n : ℕ) (v : Fin n → X) {c : ℝ → Y} {dc : Y}
    (hc : HasProjectiveCurveDerivAt c dc 0) :
    HasProjectiveCurveDerivAt
      (fun t : ℝ => inverseForwardJet J n (x + t • h) v (c t))
      (inverseForwardJet J (n + 1) x (Fin.cons h v) (c 0) +
        inverseForwardJet J n x v dc) 0 := by
  have heval : ∀ y, ContinuousAt
      (fun p : ℝ × Y => inverseForwardJet J n (x + p.1 • h) v p.2) (0, y) := by
    intro y
    have hj := ((continuousOn_inverseForwardJet J n) (x, (v, y))
      ⟨hx, mem_univ _⟩).continuousAt
        ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)
    have hm : Continuous
        (fun p : ℝ × Y => (x + p.1 • h, (v, p.2))) :=
      (continuous_const.add (continuous_fst.smul continuous_const)).prodMk
        (continuous_const.prodMk continuous_snd)
    simpa only [Function.comp_def] using
      hj.comp_of_eq (hm.continuousAt (x := (0, y)))
        (by simp only [zero_smul, add_zero])
  have hcoefficient := hasProjectiveLineDerivAt_inverseForwardJet J hx n v (c 0) h
  have hrule := inverseCurveDeriv_variableLinear
    (fun t => (inverseForwardJetLinear J n (x + t • h) v).toLinearMap)
    (c := c) (dc := dc) (t := 0)
    (dB := inverseForwardJet J (n + 1) x (Fin.cons h v) (c 0))
    (by simpa only [ContinuousLinearMap.coe_coe, inverseForwardJetLinear_apply] using heval)
    hc
    (by simpa only [ContinuousLinearMap.coe_coe, inverseForwardJetLinear_apply,
      HasProjectiveLineDerivAt] using hcoefficient)
  simpa only [ContinuousLinearMap.coe_coe, inverseForwardJetLinear_apply,
    zero_smul, add_zero] using hrule

/-- The recursive expression differential is the actual directional
derivative.  This supplies all orders by iteration, with joint continuity
already proved separately. -/
theorem TameInverseExpression.hasLineDerivAt_eval
    (e : TameInverseExpression X Y Z A)
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (hU : IsOpen U) (V : X → Z →L[ℝ] Y)
    (hleft : ∀ x ∈ U, ∀ u, V x (L x u) = u)
    (hright : ∀ x ∈ U, ∀ y, L x (V x y) = y)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))
    {z : X × Z} (hz : z.1 ∈ U) (a : A) (h : X × Z) :
    HasProjectiveLineDerivAt (fun w => e.eval J V w a)
      (e.differential J V z a h) z h := by
  induction e with
  | zero => exact hasProjectiveLineDerivAt_const 0 z h
  | source =>
      exact hasProjectiveLineDerivAt_clm
        ((ContinuousLinearMap.inr ℝ Y Z).comp (ContinuousLinearMap.snd ℝ X Z)) z h
  | linearSource c => exact hasProjectiveLineDerivAt_const (c a) z h
  | add e f he hf => exact he.add hf
  | neg e he =>
      simpa only [neg_one_smul, eval, differential, neg_apply] using
        he.const_smul (-1)
  | inverse e he =>
      let y : ℝ → Z := fun t => (e.eval J V (z + t • h) a).2
      have hy : HasProjectiveCurveDerivAt y (e.differential J V z a h).2 0 :=
        he.clm_comp (ContinuousLinearMap.snd ℝ Y Z)
      let u : Y := V z.1 (e.eval J V z a).2
      have hfwd := hasProjectiveLineDerivAt_inverseForwardJet J hz 0 Fin.elim0 u h.1
      have hgerm : (fun x => L x u) =ᶠ[𝓝 z.1]
          (fun x => inverseForwardJet J 0 x Fin.elim0 u) := by
        filter_upwards [hU.mem_nhds hz] with x hx
        exact (inverseForwardJet_zero J hx u).symm
      have hL : HasProjectiveCurveDerivAt
          (fun t : ℝ => L (z.1 + t • h.1) u)
          (inverseForwardJet J 1 z.1 (Fin.cons h.1 Fin.elim0) u) 0 :=
        hfwd.congr_germ hgerm
      have hinv := hasProjectiveCurveDerivAt_inverseFamily hU
        (fun x => (L x).toLinearMap) (fun x => (V x).toLinearMap)
        hleft hright hV
        (x := fun t : ℝ => z.1 + t • h.1) (y := y) (t := 0)
        (dy := (e.differential J V z a h).2)
        (dL := inverseForwardJet J 1 z.1 (Fin.cons h.1 Fin.elim0) u)
        ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt)
        (by simpa only [zero_smul, add_zero] using hz)
        hy
        (by simpa only [y, u, zero_smul, add_zero,
          ContinuousLinearMap.coe_coe] using hL)
      have hprod := inverseCurveDeriv_prod hinv (hasProjectiveCurveDerivAt_const (0 : Z) 0)
      simpa only [HasProjectiveLineDerivAt, eval, differential,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        sub_apply, ContinuousLinearMap.coe_coe,
        inverseForwardJetHead_apply, zero_smul, add_zero,
        Prod.smul_mk, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_add, Prod.snd_add, y, u] using hprod
  | forward n v e he =>
      have hc : HasProjectiveCurveDerivAt
          (fun t : ℝ => (e.eval J V (z + t • h) a).1)
          (e.differential J V z a h).1 0 :=
        he.clm_comp (ContinuousLinearMap.fst ℝ Y Z)
      have hj := inverseForwardJet_curve_rule J hU hz h.1 n (fun i => v i a) hc
      have hprod := inverseCurveDeriv_prod (hasProjectiveCurveDerivAt_const (0 : Y) 0) hj
      simpa only [HasProjectiveLineDerivAt, eval, differential,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        add_apply, inverseForwardJetHead_apply,
        inverseForwardJetLinear_apply, zero_smul, add_zero,
        Prod.smul_mk, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_add, Prod.snd_add] using hprod

end ExpressionDerivatives

end ContinuousFlexibility.Analysis
