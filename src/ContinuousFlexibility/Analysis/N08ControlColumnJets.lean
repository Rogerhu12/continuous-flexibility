import ContinuousFlexibility.Analysis.N08ControlColumnExtraction
import ContinuousFlexibility.Analysis.TameInverseJets

/-!
# The genuine joint tower of a control column

Ordered parameter jets keep the control vector in the last slot. A finite
expression differentiates either the coefficient or the one varying
control vector. The resulting recursion gives every joint derivative,
without a norm on the state space or a symmetry assumption on higher jets.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

namespace N08ControlColumnCalculus

section OrderedJets

variable {X B Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace B] [AddCommGroup B] [Module ℝ B]
  [IsTopologicalAddGroup B] [ContinuousSMul ℝ B]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  {U : Set (X × B)} {F : X × B → Y}

def slice (U : Set (X × B)) : Set X := {x | (x, (0 : B)) ∈ U}

theorem isOpen_slice (J : SmoothDirections U F) : IsOpen (slice U) :=
  J.open_domain.preimage (continuous_id.prodMk continuous_const)

def orderedJet (J : SmoothDirections U F) (n : ℕ) (x : X)
    (v : Fin n → X) (b : B) : Y :=
  J.D (n + 1) (x, 0) (Fin.snoc (fun i => (v i, 0)) (0, b))

theorem orderedJet_zero (J : SmoothDirections U F) (x : X) (b : B) :
    orderedJet J 0 x Fin.elim0 b = n08ControlColumn J x b := by
  rw [n08ControlColumn_apply]
  unfold orderedJet
  congr 1
  funext i
  fin_cases i
  simp only [Fin.snoc_zero, Fin.cons_zero]

def orderedLinear (J : SmoothDirections U F) (n : ℕ) (x : X)
    (v : Fin n → X) : B →L[ℝ] Y :=
  ((J.D (n + 1) (x, 0)).toContinuousLinearMap
    (Fin.snoc (fun i => (v i, 0)) (0 : X × B)) (Fin.last n)).comp
      (ContinuousLinearMap.inr ℝ X B)

theorem orderedLinear_apply (J : SmoothDirections U F) (n : ℕ) (x : X)
    (v : Fin n → X) (b : B) : orderedLinear J n x v b = orderedJet J n x v b := by
  simp only [orderedLinear, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, ContinuousLinearMap.inr_apply,
    Fin.update_snoc_last, orderedJet]

def orderedHead (J : SmoothDirections U F) (n : ℕ) (x : X)
    (v : Fin n → X) (b : B) : X →L[ℝ] Y :=
  ((J.D (n + 2) (x, 0)).toContinuousLinearMap
    (Fin.cons (0 : X × B) (Fin.snoc (fun i => (v i, 0)) (0, b))) 0).comp
      (ContinuousLinearMap.inl ℝ X B)

theorem orderedHead_apply (J : SmoothDirections U F) (n : ℕ) (x : X)
    (v : Fin n → X) (b : B) (h : X) :
    orderedHead J n x v b h = orderedJet J (n + 1) x (Fin.cons h v) b := by
  rw [orderedHead, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, ContinuousLinearMap.inl_apply,
    Fin.update_cons_zero]
  unfold orderedJet
  congr 1
  rw [Fin.cons_snoc_eq_snoc_cons]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem orderedJet_hasLineDerivAt (J : SmoothDirections U F)
    {x : X} (hx : x ∈ slice U) (n : ℕ) (v : Fin n → X) (b : B) (h : X) :
    HasProjectiveLineDerivAt (fun y => orderedJet J n y v b)
      (orderedJet J (n + 1) x (Fin.cons h v) b) x h := by
  have hd := J.derivative (n + 1) (x, 0) hx
    (Fin.snoc (fun i => (v i, 0)) (0, b)) (h, 0)
  have hi : Fin.cons (h, (0 : B)) (Fin.snoc (fun i => (v i, 0)) (0, b)) =
      Fin.snoc (α := fun _ : Fin (n + 2) => X × B)
        (fun i => (Fin.cons (α := fun _ : Fin (n + 1) => X) h v i, (0 : B)))
        ((0 : X), b) := by
    rw [Fin.cons_snoc_eq_snoc_cons]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simpa only [HasProjectiveLineDerivAt, orderedJet, Prod.smul_mk, Prod.mk_add_mk,
    Prod.fst_add, Prod.snd_add, smul_zero, add_zero, zero_add, hi] using hd

theorem orderedJet_continuousOn (J : SmoothDirections U F) (n : ℕ) :
    ContinuousOn (fun z : X × ((Fin n → X) × B) =>
      orderedJet J n z.1 z.2.1 z.2.2) (slice U ×ˢ univ) := by
  have hi : Continuous (fun z : X × ((Fin n → X) × B) =>
      Fin.snoc (α := fun _ : Fin (n + 1) => X × B)
        (fun i => (z.2.1 i, (0 : B))) ((0 : X), z.2.2)) := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using continuous_const.prodMk continuous_snd.snd
    · simpa only [Fin.snoc_castSucc] using
        (((continuous_apply j).comp continuous_snd.fst).prodMk continuous_const)
  exact (J.continuous (n + 1)).comp
    (((continuous_fst.prodMk continuous_const).prodMk hi).continuousOn)
    (fun z hz => ⟨hz.1, mem_univ _⟩)

theorem orderedJet_curve_rule (J : SmoothDirections U F)
    {x : X} (hx : x ∈ slice U) (h : X) (n : ℕ) (v : Fin n → X)
    {c : ℝ → B} {dc : B} (hc : HasProjectiveCurveDerivAt c dc 0) :
    HasProjectiveCurveDerivAt (fun t : ℝ => orderedJet J n (x + t • h) v (c t))
      (orderedJet J (n + 1) x (Fin.cons h v) (c 0) + orderedJet J n x v dc) 0 := by
  have heval : ∀ b, ContinuousAt
      (fun p : ℝ × B => orderedJet J n (x + p.1 • h) v p.2) (0, b) := by
    intro b
    have hj := ((orderedJet_continuousOn J n) (x, (v, b))
      ⟨hx, mem_univ _⟩).continuousAt
        (((isOpen_slice J).prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)
    have hm : Continuous (fun p : ℝ × B => (x + p.1 • h, (v, p.2))) :=
      (continuous_const.add (continuous_fst.smul continuous_const)).prodMk
        (continuous_const.prodMk continuous_snd)
    simpa only [Function.comp_def] using
      hj.comp_of_eq (hm.continuousAt (x := (0, b)))
        (by simp only [zero_smul, add_zero])
  have hcoef := orderedJet_hasLineDerivAt J hx n v (c 0) h
  have h := inverseCurveDeriv_variableLinear
    (fun t => (orderedLinear J n (x + t • h) v).toLinearMap)
    (c := c) (dc := dc) (t := 0)
    (dB := orderedJet J (n + 1) x (Fin.cons h v) (c 0))
    (by simpa only [ContinuousLinearMap.coe_coe, orderedLinear_apply] using heval)
    hc (by simpa only [ContinuousLinearMap.coe_coe, orderedLinear_apply,
      HasProjectiveLineDerivAt] using hcoef)
  simpa only [ContinuousLinearMap.coe_coe, orderedLinear_apply,
    zero_smul, add_zero] using h

end OrderedJets

section Expressions

variable (X B A : Type*)
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace B] [AddCommGroup B] [Module ℝ B]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]

/-- A sum of ordered jets with either the current control or a fixed
linear function of the old directions in its last slot. -/
inductive Expression where
  | jet (n : ℕ) (v : Fin n → A →L[ℝ] X) (b : A →L[ℝ] B)
  | fiber (n : ℕ) (v : Fin n → A →L[ℝ] X)
  | add (e f : Expression)

variable {X B A}
variable {Y A' : Type*}
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [IsTopologicalAddGroup B] [ContinuousSMul ℝ B]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [TopologicalSpace A'] [AddCommGroup A'] [Module ℝ A']
  {U : Set (X × B)} {F : X × B → Y}

def Expression.eval (J : SmoothDirections U F) : Expression X B A → (X × B) → A → Y
  | .jet n v b, z, a => orderedJet J n z.1 (fun i => v i a) (b a)
  | .fiber n v, z, a => orderedJet J n z.1 (fun i => v i a) z.2
  | .add e f, z, a => e.eval J z a + f.eval J z a

def Expression.reparam (g : A' →L[ℝ] A) : Expression X B A → Expression X B A'
  | .jet n v b => .jet n (fun i => (v i).comp g) (b.comp g)
  | .fiber n v => .fiber n (fun i => (v i).comp g)
  | .add e f => .add (e.reparam g) (f.reparam g)

def Expression.diff (g : A' →L[ℝ] A) (h : A' →L[ℝ] X × B) :
    Expression X B A → Expression X B A'
  | .jet n v b => .jet (n + 1)
      (Fin.cons ((ContinuousLinearMap.fst ℝ X B).comp h) (fun i => (v i).comp g))
      (b.comp g)
  | .fiber n v => .add
      (.fiber (n + 1)
        (Fin.cons ((ContinuousLinearMap.fst ℝ X B).comp h) (fun i => (v i).comp g)))
      (.jet n (fun i => (v i).comp g) ((ContinuousLinearMap.snd ℝ X B).comp h))
  | .add e f => .add (e.diff g h) (f.diff g h)

def Expression.differential (J : SmoothDirections U F) :
    Expression X B A → (X × B) → A → (X × B) →L[ℝ] Y
  | .jet n v b, z, a =>
      (orderedHead J n z.1 (fun i => v i a) (b a)).comp (ContinuousLinearMap.fst ℝ X B)
  | .fiber n v, z, a =>
      (orderedHead J n z.1 (fun i => v i a) z.2).comp (ContinuousLinearMap.fst ℝ X B) +
      (orderedLinear J n z.1 (fun i => v i a)).comp (ContinuousLinearMap.snd ℝ X B)
  | .add e f, z, a => e.differential J z a + f.differential J z a

theorem Expression.eval_diff (e : Expression X B A) (J : SmoothDirections U F)
    (g : A' →L[ℝ] A) (h : A' →L[ℝ] X × B) (z : X × B) (a : A') :
    (e.diff g h).eval J z a = e.differential J z (g a) (h a) := by
  have hcons {n : ℕ} (v : Fin n → A →L[ℝ] X) :
      (fun i => Fin.cons ((ContinuousLinearMap.fst ℝ X B).comp h)
        (fun j => (v j).comp g) i a) =
      Fin.cons (h a).1 (fun i => v i (g a)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp only [Fin.cons_zero, Fin.cons_succ, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst']
  induction e with
  | jet n v b =>
      simp only [diff, eval, differential, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', orderedHead_apply, hcons]
  | fiber n v =>
      simp only [diff, eval, differential, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.add_apply, orderedHead_apply, orderedLinear_apply, hcons]
  | add e f he hf =>
      simp only [diff, eval, differential, ContinuousLinearMap.add_apply, he, hf]

theorem Expression.continuousOn_eval (e : Expression X B A) (J : SmoothDirections U F) :
    ContinuousOn (fun z : (X × B) × A => e.eval J z.1 z.2)
      ((slice U ×ˢ univ) ×ˢ univ) := by
  induction e with
  | jet n v b =>
      exact (orderedJet_continuousOn J n).comp
        (continuous_fst.fst.prodMk
          ((continuous_pi fun i => (v i).continuous.comp continuous_snd).prodMk
            (b.continuous.comp continuous_snd))).continuousOn
        (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  | fiber n v =>
      exact (orderedJet_continuousOn J n).comp
        (continuous_fst.fst.prodMk
          ((continuous_pi fun i => (v i).continuous.comp continuous_snd).prodMk
            continuous_fst.snd)).continuousOn
        (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  | add e f he hf => exact he.add hf

theorem Expression.hasLineDerivAt_eval (e : Expression X B A) (J : SmoothDirections U F)
    {z : X × B} (hz : z.1 ∈ slice U) (a : A) (h : X × B) :
    HasProjectiveLineDerivAt (fun w => e.eval J w a)
      (e.differential J z a h) z h := by
  induction e with
  | jet n v b =>
      simpa only [eval, differential, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', orderedHead_apply] using
        HasProjectiveLineDerivAt.comp_linear (LinearMap.fst ℝ X B)
          (x := z) (v := h)
          (orderedJet_hasLineDerivAt J hz n (fun i => v i a) (b a) h.1)
  | fiber n v =>
      have hc : HasProjectiveCurveDerivAt (fun t : ℝ => z.2 + t • h.2) h.2 0 := by
        simpa only [HasProjectiveLineDerivAt, ContinuousLinearMap.id_apply] using
          hasProjectiveLineDerivAt_clm (ContinuousLinearMap.id ℝ B) z.2 h.2
      have hd := orderedJet_curve_rule J hz h.1 n (fun i => v i a) hc
      simpa only [HasProjectiveLineDerivAt, eval, differential,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.add_apply,
        orderedHead_apply, orderedLinear_apply, zero_smul, add_zero,
        Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] using hd
  | add e f he hf => exact he.add hf

end Expressions

section Tower

variable {X B Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace B] [AddCommGroup B] [Module ℝ B]
  [IsTopologicalAddGroup B] [ContinuousSMul ℝ B]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  {U : Set (X × B)} {F : X × B → Y}

def columnExpression : (n : ℕ) → Expression X B (Fin n → X × B)
  | 0 => .fiber 0 Fin.elim0
  | n + 1 => (columnExpression n).diff (inverseAuxTail (X × B) n)
      (ContinuousLinearMap.proj 0)

def columnJetValue (J : SmoothDirections U F) (n : ℕ) (z : X × B)
    (v : Fin n → X × B) : Y := (columnExpression n).eval J z v

theorem columnJetValue_zero (J : SmoothDirections U F) (z : X × B)
    (v : Fin 0 → X × B) : columnJetValue J 0 z v = n08ControlColumn J z.1 z.2 := by
  have he : (fun i : Fin 0 => (Fin.elim0 i : (Fin 0 → X × B) →L[ℝ] X) v) =
      Fin.elim0 := by funext i; exact i.elim0
  simpa only [columnJetValue, columnExpression, Expression.eval, he] using
    orderedJet_zero J z.1 z.2

theorem columnJetValue_succ (J : SmoothDirections U F) (n : ℕ) (z : X × B)
    (v : Fin (n + 1) → X × B) :
    columnJetValue J (n + 1) z v =
      (columnExpression n).differential J z (Fin.tail v) (v 0) := by
  simpa only [columnJetValue, columnExpression, inverseAuxTail_apply,
    ContinuousLinearMap.proj_apply] using
    (columnExpression n).eval_diff J (inverseAuxTail (X × B) n)
      (ContinuousLinearMap.proj 0) z v

theorem columnJetValue_hasLineDerivAt (J : SmoothDirections U F)
    (n : ℕ) {z : X × B} (hz : z.1 ∈ slice U) (v : Fin n → X × B) (h : X × B) :
    HasProjectiveLineDerivAt (fun w => columnJetValue J n w v)
      (columnJetValue J (n + 1) z (Fin.cons h v)) z h := by
  have hd := (columnExpression n).hasLineDerivAt_eval J hz v h
  rw [columnJetValue_succ, Fin.tail_cons, Fin.cons_zero]
  exact hd

theorem columnJetValue_update_add (J : SmoothDirections U F) :
    ∀ n z, z.1 ∈ slice U → ∀ (v : Fin n → X × B) (i : Fin n) (a b : X × B),
      columnJetValue J n z (Function.update v i (a + b)) =
        columnJetValue J n z (Function.update v i a) +
          columnJetValue J n z (Function.update v i b) := by
  intro n
  induction n with
  | zero => intro z hz v i; exact Fin.elim0 i
  | succ n ih =>
      intro z hz v i a b
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [columnJetValue_succ, Fin.tail_update_zero, Function.update_self]
        exact map_add _ a b
      · let w : Fin n → X × B := Fin.tail v
        let h : X × B := v 0
        have hsum := (columnJetValue_hasLineDerivAt J n hz (Function.update w j a) h).add
          (columnJetValue_hasLineDerivAt J n hz (Function.update w j b) h)
        have hall := columnJetValue_hasLineDerivAt J n hz (Function.update w j (a + b)) h
        have hgerm :
            (fun x => columnJetValue J n x (Function.update w j a) +
              columnJetValue J n x (Function.update w j b)) =ᶠ[𝓝 z]
            (fun x => columnJetValue J n x (Function.update w j (a + b))) := by
          filter_upwards [((isOpen_slice J).prod isOpen_univ).mem_nhds
            ⟨hz, mem_univ z.2⟩] with x hx
          exact (ih x hx.1 w j a b).symm
        have heq := (hall.congr_germ hgerm).unique hsum
        simpa only [w, h, Fin.cons_update, Fin.cons_self_tail] using heq

theorem columnJetValue_update_smul (J : SmoothDirections U F) :
    ∀ n z, z.1 ∈ slice U → ∀ (v : Fin n → X × B) (i : Fin n) (c : ℝ) (a : X × B),
      columnJetValue J n z (Function.update v i (c • a)) =
        c • columnJetValue J n z (Function.update v i a) := by
  intro n
  induction n with
  | zero => intro z hz v i; exact Fin.elim0 i
  | succ n ih =>
      intro z hz v i c a
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [columnJetValue_succ, Fin.tail_update_zero, Function.update_self]
        exact map_smul _ c a
      · let w : Fin n → X × B := Fin.tail v
        let h : X × B := v 0
        have hsmul := (columnJetValue_hasLineDerivAt J n hz (Function.update w j a) h).const_smul c
        have hall := columnJetValue_hasLineDerivAt J n hz (Function.update w j (c • a)) h
        have hgerm :
            (fun x => c • columnJetValue J n x (Function.update w j a)) =ᶠ[𝓝 z]
            (fun x => columnJetValue J n x (Function.update w j (c • a))) := by
          filter_upwards [((isOpen_slice J).prod isOpen_univ).mem_nhds
            ⟨hz, mem_univ z.2⟩] with x hx
          exact (ih x hx.1 w j c a).symm
        have heq := (hall.congr_germ hgerm).unique hsmul
        simpa only [w, h, Fin.cons_update, Fin.cons_self_tail] using heq

def columnJetMultilinear (J : SmoothDirections U F) (n : ℕ)
    (z : X × B) (hz : z.1 ∈ slice U) : (X × B) [×n]→L[ℝ] Y where
  toMultilinearMap := MultilinearMap.mk' (columnJetValue J n z)
    (columnJetValue_update_add J n z hz) (columnJetValue_update_smul J n z hz)
  cont := by
    have hc := (columnExpression n).continuousOn_eval J
    have hm : Continuous (fun v : Fin n → X × B => (z, v)) :=
      continuous_const.prodMk continuous_id
    have hcont : Continuous (fun v : Fin n → X × B => columnJetValue J n z v) := by
      simpa only [Function.comp_def, columnJetValue] using
        continuousOn_univ.mp (hc.comp hm.continuousOn
          (fun v _ => ⟨⟨hz, mem_univ z.2⟩, mem_univ v⟩))
    apply hcont.congr
    intro v
    simp only [MultilinearMap.toFun_eq_coe, MultilinearMap.mk'_apply]

theorem columnJetMultilinear_apply (J : SmoothDirections U F) (n : ℕ)
    (z : X × B) (hz : z.1 ∈ slice U) (v : Fin n → X × B) :
    columnJetMultilinear J n z hz v = columnJetValue J n z v := by
  rw [← ContinuousMultilinearMap.coe_coe]
  simp only [columnJetMultilinear, MultilinearMap.mk'_apply]

def columnJets (J : SmoothDirections U F) : ProjectiveJetFamily (X × B) Y := by
  classical
  exact fun n z => if hz : z.1 ∈ slice U then columnJetMultilinear J n z hz else 0

theorem columnJets_apply (J : SmoothDirections U F) (n : ℕ)
    {z : X × B} (hz : z.1 ∈ slice U) (v : Fin n → X × B) :
    columnJets J n z v = columnJetValue J n z v := by
  simp only [columnJets, dite_eq_left hz, columnJetMultilinear_apply]

theorem columnJets_actual (J : SmoothDirections U F) :
    HasProjectiveJetsOn (fun z : X × B => n08ControlColumn J z.1 z.2)
      (columnJets J) (slice U ×ˢ univ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [columnJets_apply J 0 hz.1, columnJetValue_zero]
  · intro n
    apply ((columnExpression n).continuousOn_eval J).congr
    intro p hp
    exact columnJets_apply J n hp.1.1 p.2
  · intro n z hz h v
    have hd := columnJetValue_hasLineDerivAt J n hz.1 v h
    have hgerm : (fun x => columnJets J n x v) =ᶠ[𝓝 z]
        (fun x => columnJetValue J n x v) := by
      filter_upwards [((isOpen_slice J).prod isOpen_univ).mem_nhds hz] with x hx
      exact columnJets_apply J n hx.1 v
    simpa only [columnJets_apply J (n + 1) hz.1] using hd.congr_germ hgerm

end Tower

end N08ControlColumnCalculus

section TowerInterface

variable {X B Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace B] [AddCommGroup B] [Module ℝ B]
  [IsTopologicalAddGroup B] [ContinuousSMul ℝ B]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  {U : Set (X × B)} {F : X × B → Y}

/-- The actual control column has one joint tower on the full zero-control
slice times every control vector. -/
def n08ControlColumn_smoothDirections (J : SmoothDirections U F) :
    SmoothDirections (N08ControlColumnCalculus.slice U ×ˢ univ)
      (fun z : X × B => n08ControlColumn J z.1 z.2) :=
  smoothDirectionsOfJets ((N08ControlColumnCalculus.isOpen_slice J).prod isOpen_univ)
    (N08ControlColumnCalculus.columnJets J) (N08ControlColumnCalculus.columnJets_actual J)

theorem n08ControlColumn_smoothDirections_apply (J : SmoothDirections U F) (n : ℕ)
    {z : X × B} (hz : z.1 ∈ N08ControlColumnCalculus.slice U) (v : Fin n → X × B) :
    (n08ControlColumn_smoothDirections J).D n z v =
      N08ControlColumnCalculus.columnJetValue J n z v :=
  N08ControlColumnCalculus.columnJets_apply J n hz v

end TowerInterface

end ContinuousFlexibility.Statements
