import ContinuousFlexibility.Analysis.CoupledTameDerivativeExpressions
import ContinuousFlexibility.Analysis.TameInverseBounds
import ContinuousFlexibility.Analysis.TamePairTopology

/-!
# The joint derivative of a smooth tame map

Ordered expressions construct all genuine directional derivatives of
`(x,v) ↦ Df(x)[v]`.  Their joint local tame bounds are then normalized to
the same homogeneous one-high-factor bounds as in `SmoothTameOn`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
variable {U : Set E} {f : E → F}

/-- The finite expression for each derivative of the joint evaluation. -/
def coupledDerivativeExpressionJet :
    (n : ℕ) → CoupledDerivativeExpression E (Fin n → E × E)
  | 0 => .current 0 Fin.elim0
  | n + 1 => (coupledDerivativeExpressionJet n).diff (inverseAuxTail (E × E) n)
      (ContinuousLinearMap.proj 0)

def coupledDerivativeJetValue (J : SmoothDirections U f)
    (n : ℕ) (z : E × E) (v : Fin n → E × E) : F :=
  (coupledDerivativeExpressionJet n).eval J z v

@[simp] theorem coupledDerivativeJetValue_zero (J : SmoothDirections U f)
    (z : E × E) (v : Fin 0 → E × E) :
    coupledDerivativeJetValue J 0 z v = J.D 1 z.1 (fun _ => z.2) := by
  unfold coupledDerivativeJetValue coupledDerivativeExpressionJet
    CoupledDerivativeExpression.eval coupledOrderedJet
  congr 1

theorem coupledDerivativeJetValue_succ (J : SmoothDirections U f)
    (n : ℕ) (z : E × E) (v : Fin (n + 1) → E × E) :
    coupledDerivativeJetValue J (n + 1) z v =
      (coupledDerivativeExpressionJet n).differential J z (Fin.tail v) (v 0) := by
  simpa only [coupledDerivativeJetValue, coupledDerivativeExpressionJet,
    inverseAuxTail_apply, ContinuousLinearMap.proj_apply] using
      (coupledDerivativeExpressionJet (E := E) n).eval_diff J
        (inverseAuxTail (E × E) n) (ContinuousLinearMap.proj 0) z v

theorem hasProjectiveLineDerivAt_coupledDerivativeJet (J : SmoothDirections U f)
    (n : ℕ) {z : E × E} (hz : z.1 ∈ U) (v : Fin n → E × E) (h : E × E) :
    HasProjectiveLineDerivAt (fun w => coupledDerivativeJetValue J n w v)
      (coupledDerivativeJetValue J (n + 1) z (Fin.cons h v)) z h := by
  have hd := (coupledDerivativeExpressionJet n).hasLineDerivAt_eval J hz v h
  rw [coupledDerivativeJetValue_succ, Fin.tail_cons, Fin.cons_zero]
  simpa only [coupledDerivativeJetValue] using hd

/-- Linearity in old slots follows by differentiating the corresponding
identity.  Linearity in the new slot is already bundled in `differential`. -/
theorem coupledDerivativeJetValue_update_add (J : SmoothDirections U f) :
    ∀ n z, z.1 ∈ U → ∀ (v : Fin n → E × E) (i : Fin n) (a b : E × E),
      coupledDerivativeJetValue J n z (Function.update v i (a + b)) =
        coupledDerivativeJetValue J n z (Function.update v i a) +
          coupledDerivativeJetValue J n z (Function.update v i b) := by
  intro n
  induction n with
  | zero => intro z hz v i; exact Fin.elim0 i
  | succ n ih =>
      intro z hz v i a b
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [coupledDerivativeJetValue_succ, Fin.tail_update_zero, Function.update_self]
        exact map_add _ a b
      · let w : Fin n → E × E := Fin.tail v
        let h : E × E := v 0
        have hsum :=
          (hasProjectiveLineDerivAt_coupledDerivativeJet J n hz (Function.update w j a) h).add
          (hasProjectiveLineDerivAt_coupledDerivativeJet J n hz (Function.update w j b) h)
        have hall := hasProjectiveLineDerivAt_coupledDerivativeJet J n hz
          (Function.update w j (a + b)) h
        have hgerm :
            (fun x => coupledDerivativeJetValue J n x (Function.update w j a) +
              coupledDerivativeJetValue J n x (Function.update w j b)) =ᶠ[𝓝 z]
            (fun x => coupledDerivativeJetValue J n x (Function.update w j (a + b))) := by
          filter_upwards [(J.open_domain.prod isOpen_univ).mem_nhds
            ⟨hz, mem_univ z.2⟩] with x hx
          exact (ih x hx.1 w j a b).symm
        have heq := (hall.congr_germ hgerm).unique hsum
        simpa only [w, h, Fin.cons_update, Fin.cons_self_tail] using heq

theorem coupledDerivativeJetValue_update_smul (J : SmoothDirections U f) :
    ∀ n z, z.1 ∈ U → ∀ (v : Fin n → E × E) (i : Fin n) (c : ℝ) (a : E × E),
      coupledDerivativeJetValue J n z (Function.update v i (c • a)) =
        c • coupledDerivativeJetValue J n z (Function.update v i a) := by
  intro n
  induction n with
  | zero => intro z hz v i; exact Fin.elim0 i
  | succ n ih =>
      intro z hz v i c a
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [coupledDerivativeJetValue_succ, Fin.tail_update_zero, Function.update_self]
        exact map_smul _ c a
      · let w : Fin n → E × E := Fin.tail v
        let h : E × E := v 0
        have hsmul :=
          (hasProjectiveLineDerivAt_coupledDerivativeJet J n hz
            (Function.update w j a) h).const_smul c
        have hall := hasProjectiveLineDerivAt_coupledDerivativeJet J n hz
          (Function.update w j (c • a)) h
        have hgerm :
            (fun x => c • coupledDerivativeJetValue J n x (Function.update w j a)) =ᶠ[𝓝 z]
            (fun x => coupledDerivativeJetValue J n x (Function.update w j (c • a))) := by
          filter_upwards [(J.open_domain.prod isOpen_univ).mem_nhds
            ⟨hz, mem_univ z.2⟩] with x hx
          exact (ih x hx.1 w j c a).symm
        have heq := (hall.congr_germ hgerm).unique hsmul
        simpa only [w, h, Fin.cons_update, Fin.cons_self_tail] using heq

/-- Bundle the actual formulas as continuous multilinear maps. -/
def coupledDerivativeJetMultilinear (J : SmoothDirections U f)
    (n : ℕ) (z : E × E) (hz : z.1 ∈ U) : (E × E) [×n]→L[ℝ] F where
  toMultilinearMap := MultilinearMap.mk' (coupledDerivativeJetValue J n z)
    (coupledDerivativeJetValue_update_add J n z hz)
    (coupledDerivativeJetValue_update_smul J n z hz)
  cont := by
    have hc := (coupledDerivativeExpressionJet n).continuousOn_eval J
    have hm : Continuous (fun v : Fin n → E × E => (z, v)) :=
      continuous_const.prodMk continuous_id
    have hcont : Continuous (fun v : Fin n → E × E => coupledDerivativeJetValue J n z v) := by
      simpa only [Function.comp_def, coupledDerivativeJetValue] using
        continuousOn_univ.mp (hc.comp hm.continuousOn
          (fun v _ => ⟨⟨hz, mem_univ z.2⟩, mem_univ v⟩))
    apply hcont.congr
    intro v
    simp only [MultilinearMap.toFun_eq_coe, MultilinearMap.mk'_apply]

@[simp] theorem coupledDerivativeJetMultilinear_apply (J : SmoothDirections U f)
    (n : ℕ) (z : E × E) (hz : z.1 ∈ U) (v : Fin n → E × E) :
    coupledDerivativeJetMultilinear J n z hz v = coupledDerivativeJetValue J n z v := by
  rw [← ContinuousMultilinearMap.coe_coe]
  simp only [coupledDerivativeJetMultilinear, MultilinearMap.mk'_apply]

def coupledDerivativeJets (J : SmoothDirections U f) : ProjectiveJetFamily (E × E) F := by
  classical
  exact fun n z => if hz : z.1 ∈ U then coupledDerivativeJetMultilinear J n z hz else 0

@[simp] theorem coupledDerivativeJets_apply (J : SmoothDirections U f)
    (n : ℕ) {z : E × E} (hz : z.1 ∈ U) (v : Fin n → E × E) :
    coupledDerivativeJets J n z v = coupledDerivativeJetValue J n z v := by
  simp only [coupledDerivativeJets, dite_eq_left hz, coupledDerivativeJetMultilinear_apply]

theorem hasProjectiveJetsOn_derivativeEvaluation (J : SmoothDirections U f) :
    HasProjectiveJetsOn (fun z : E × E => J.D 1 z.1 (fun _ => z.2))
      (coupledDerivativeJets J) (U ×ˢ univ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [coupledDerivativeJets_apply J 0 hz.1, coupledDerivativeJetValue_zero]
  · intro n
    apply ((coupledDerivativeExpressionJet n).continuousOn_eval J).congr
    intro p hp
    exact coupledDerivativeJets_apply J n hp.1.1 p.2
  · intro n z hz h v
    have hactual := hasProjectiveLineDerivAt_coupledDerivativeJet J n hz.1 v h
    have hgerm :
        (fun x => coupledDerivativeJets J n x v) =ᶠ[𝓝 z]
        (fun x => coupledDerivativeJetValue J n x v) := by
      filter_upwards [(J.open_domain.prod isOpen_univ).mem_nhds hz] with x hx
      exact coupledDerivativeJets_apply J n hx.1 v
    simpa only [coupledDerivativeJets_apply J (n + 1) hz.1] using
      hactual.congr_germ hgerm

/-- A smooth directional tower for the joint first derivative. -/
def derivativeEvaluationSmoothDirections (J : SmoothDirections U f) :
    SmoothDirections (U ×ˢ univ) (fun z : E × E => J.D 1 z.1 (fun _ => z.2)) :=
  smoothDirectionsOfJets (J.open_domain.prod isOpen_univ) (coupledDerivativeJets J)
    (hasProjectiveJetsOn_derivativeEvaluation J)

@[simp] theorem derivativeEvaluationSmoothDirections_apply (J : SmoothDirections U f)
    (n : ℕ) {z : E × E} (hz : z.1 ∈ U) (v : Fin n → E × E) :
    (derivativeEvaluationSmoothDirections J).D n z v = coupledDerivativeJetValue J n z v :=
  coupledDerivativeJets_apply J n hz v

theorem coupledDerivativeExpressionJet_zeroLoss (p : ℕ → Seminorm ℝ E) :
    ∀ n, (coupledDerivativeExpressionJet (E := E) n).IsZeroLoss p
      (tupleGrading (fun _ : Fin n => pairGrading p p)) := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      exact ih.diff (inverseAuxTail (E × E) n) (inverseTame_tupleTail (pairGrading p p) n)
        (ContinuousLinearMap.proj 0) (inverseTame_tupleProjection (pairGrading p p) 0)

/-- The actual first derivative of a smooth tame map is smooth tame jointly
in the base point and its direction.  No norm on either space is needed. -/
theorem smoothTameOn_derivativeEvaluation
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) (htp : WithSeminorms p)
    (J : SmoothDirections U f) (hJ : J.TameBounds p q) :
    SmoothTameOn (pairGrading p p) q (U ×ˢ univ)
      (fun z : E × E => J.D 1 z.1 (fun _ => z.2)) := by
  let JD := derivativeEvaluationSmoothDirections J
  have hlocal (n : ℕ) : LocallyTameOn (jetGrading (pairGrading p p) n) q
      ((U ×ˢ univ) ×ˢ univ) (fun z => JD.D n z.1 z.2) := by
    have he := (coupledDerivativeExpressionJet (E := E) n).locallyTameOn_eval
      hp (tupleGrading_monotone _ (fun _ => tamePairGrading_monotone hp hp))
      (coupledDerivativeExpressionJet_zeroLoss p n) J
      (fun k => locallyTameOn_jetEvaluation htp J hJ k)
    apply he.congr
    intro z hz
    exact derivativeEvaluationSmoothDirections_apply J n hz.1.1 z.2
  exact smoothTameOn_of_locallyTameOn_jets (tamePairGrading_monotone hp hp)
    (withSeminorms_pairGrading htp htp) JD hlocal

end ContinuousFlexibility.Analysis
