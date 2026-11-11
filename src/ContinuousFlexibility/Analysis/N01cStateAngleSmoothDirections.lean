import ContinuousFlexibility.Analysis.N01cFiniteParameterProducts
import ContinuousFlexibility.Analysis.N01cFiniteAffineMixedJets
import ContinuousFlexibility.Analysis.N01cStateAngleJets
import ContinuousFlexibility.Analysis.N01cVolterraStateJets
import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# Genuine state-and-angle towers from the actual mixed state jets

The finite word sum has the actual joint line derivative supplied by
finite affine mixed differentiation. Its evaluated jets are continuous
when the original state-jet evaluations are continuous. Time remains an
external variable and the state space is only a topological real module.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem iteratedDeriv_stateJet_angle
    {U : Set E} {f : E × PolarPoint → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : PolarPoint, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (b k : ℕ) {x : E} (hx : x ∈ U) (t θ : ℝ) (v : Fin k → E) :
    iteratedDeriv b (fun η => (J 0 (t, η)).D k x v) θ =
      (J b (t, θ)).D k x v := by
  induction b generalizing θ with
  | zero => rfl
  | succ b ih =>
      have he : iteratedDeriv b (fun η => (J 0 (t, η)).D k x v) =
          fun η => (J b (t, η)).D k x v := funext ih
      rw [iteratedDeriv_succ, he]
      exact deriv_stateJet_angle hU hf J k b x hx t θ v

/-- The two possible new head slots are the true joint differential of
the full finite word sum. -/
theorem stateAngleJet_hasProjectiveLineDerivAt
    {U : Set E} {f : E × PolarPoint → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : PolarPoint, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (n : ℕ) {x : E} (hx : x ∈ U) (t θ : ℝ)
    (v : Fin n → E × ℝ) (u : E × ℝ) :
    HasProjectiveLineDerivAt
      (fun y : E × ℝ => stateAngleJet (fun b k => (J b (t, y.2)).D k y.1) n v)
      (stateAngleJet (fun b k => (J b (t, θ)).D k x) (n + 1) (Fin.cons u v))
      (x, θ) u := by
  classical
  have hterm (a : StateAngleWord n) : HasProjectiveLineDerivAt
      (fun y : E × ℝ =>
        (J a.angleArity (t, y.2)).D a.stateArity y.1 (a.stateDirections v) * a.angleFactor v)
      (((J a.angleArity (t, θ)).D (a.stateArity + 1) x
          (Fin.cons u.1 (a.stateDirections v)) +
        u.2 * (J (a.angleArity + 1) (t, θ)).D a.stateArity x (a.stateDirections v)) *
          a.angleFactor v) (x, θ) u := by
    simpa only [smul_eq_mul, mul_comm] using
      (hasProjectiveLineDerivAt_stateAngleEvaluation hU hf J
        a.angleArity a.stateArity hx t θ (a.stateDirections v) u).const_smul
          (a.angleFactor v)
  have hsum := HasProjectiveCurveDerivAt.finset_sum Finset.univ (fun a _ => hterm a)
  have heq :
      (∑ a : StateAngleWord n,
        ((J a.angleArity (t, θ)).D (a.stateArity + 1) x
            (Fin.cons u.1 (a.stateDirections v)) +
          u.2 * (J (a.angleArity + 1) (t, θ)).D a.stateArity x (a.stateDirections v)) *
            a.angleFactor v) =
      stateAngleJet (fun b k => (J b (t, θ)).D k x) (n + 1) (Fin.cons u v) := by
    symm
    rw [stateAngleJet_cons_apply]
    simp only [stateAngleJet_apply, continuousMultilinearFixHead_apply, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq] at hsum
  simpa only [HasProjectiveLineDerivAt, stateAngleJet_apply] using hsum

/-- Joint continuity includes every direction slot in its original
topology. No operator norm is introduced on the source. -/
theorem stateAngleJet_joint_continuous
    {U : Set E} {f : E × PolarPoint → ℝ}
    (J : ∀ b : ℕ, ∀ q : PolarPoint, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (hJ : ∀ b k, ContinuousOn
      (fun p : (E × PolarPoint) × (Fin k → E) => (J b p.1.2).D k p.1.1 p.2)
      ((U ×ˢ (univ : Set PolarPoint)) ×ˢ univ))
    (n : ℕ) :
    ContinuousOn (fun p : (E × PolarPoint) × (Fin n → E × ℝ) =>
      stateAngleJet (fun b k => (J b p.1.2).D k p.1.1) n p.2)
      ((U ×ˢ (univ : Set PolarPoint)) ×ˢ univ) := by
  classical
  simp only [stateAngleJet_apply]
  apply continuousOn_finsetSum Finset.univ
  intro a _
  have hmap : Continuous
      (fun p : (E × PolarPoint) × (Fin n → E × ℝ) => (p.1, a.stateDirections p.2)) :=
    continuous_fst.prodMk ((continuous_stateAngleWord_stateDirections a).comp continuous_snd)
  exact ((hJ a.angleArity a.stateArity).comp hmap.continuousOn
    (fun p hp => ⟨hp.1, mem_univ _⟩)).mul
      (((continuous_stateAngleWord_angleFactor a).comp continuous_snd).continuousOn)

private theorem stateAngle_fixedTime_continuousOn
    {U : Set E} {n : ℕ}
    (A : (E × PolarPoint) × (Fin n → E × ℝ) → ℝ)
    (hA : ContinuousOn A ((U ×ˢ (univ : Set PolarPoint)) ×ˢ univ))
    (t : ℝ) :
    ContinuousOn
      (fun p : (E × ℝ) × (Fin n → E × ℝ) => A ((p.1.1, (t, p.1.2)), p.2))
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) := by
  have hmap : Continuous
      (fun p : (E × ℝ) × (Fin n → E × ℝ) =>
        ((p.1.1, (t, p.1.2)), p.2)) :=
    (continuous_fst.fst.prodMk (continuous_const.prodMk continuous_fst.snd)).prodMk continuous_snd
  exact hA.comp'
    (f := fun p : (E × ℝ) × (Fin n → E × ℝ) => ((p.1.1, (t, p.1.2)), p.2))
    hmap.continuousOn (fun p hp => ⟨⟨hp.1.1, mem_univ _⟩, mem_univ _⟩)

/-- The algebraic word lift is the genuine state-and-angle smooth tower
of the original scalar family at the fixed external time. -/
def stateAngleSmoothDirections
    {U : Set E} {f : E × PolarPoint → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : PolarPoint, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (hJ : ∀ b k, ContinuousOn
      (fun p : (E × PolarPoint) × (Fin k → E) => (J b p.1.2).D k p.1.1 p.2)
      ((U ×ˢ (univ : Set PolarPoint)) ×ˢ univ))
    (t : ℝ) :
    SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun y : E × ℝ => f (y.1, (t, y.2))) where
  open_domain := hU.prod isOpen_univ
  D := fun n y => stateAngleJet (fun b k => (J b (t, y.2)).D k y.1) n
  zero := by
    intro y hy
    rw [stateAngleJet_zero]
    simpa only [iteratedDeriv_zero] using
      smoothDirections_D_zero_apply (J 0 (t, y.2)) hy.1 Fin.elim0
  continuous := by
    intro n
    change ContinuousOn (fun p : (E × ℝ) × (Fin n → E × ℝ) =>
      stateAngleJet (fun b k => (J b (t, p.1.2)).D k p.1.1) n p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)
    exact stateAngle_fixedTime_continuousOn
      (fun p : (E × PolarPoint) × (Fin n → E × ℝ) =>
        stateAngleJet (fun b k => (J b p.1.2).D k p.1.1) n p.2)
      (stateAngleJet_joint_continuous (U := U) (f := f) J hJ n) t
  derivative := by
    intro n y hy v u
    exact stateAngleJet_hasProjectiveLineDerivAt (U := U) (f := f) hU hf J n hy.1 t y.2 v u

/-- All external-time evaluation continuity is retained by the genuine
joint tower required for the Volterra construction. -/
def continuousTimeSpeedTower_of_stateAngularJets
    {U : Set E} {f : E × PolarPoint → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : PolarPoint, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (hJ : ∀ b k, ContinuousOn
      (fun p : (E × PolarPoint) × (Fin k → E) => (J b p.1.2).D k p.1.1 p.2)
      ((U ×ˢ (univ : Set PolarPoint)) ×ˢ univ)) :
    ContinuousTimeSpeedTower U f where
  jet := stateAngleSmoothDirections hU hf J hJ
  continuous := stateAngleJet_joint_continuous J hJ

theorem continuousTimeSpeedTower_of_stateAngularJets_D_apply
    {U : Set E} {f : E × PolarPoint → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : PolarPoint, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (hJ : ∀ b k, ContinuousOn
      (fun p : (E × PolarPoint) × (Fin k → E) => (J b p.1.2).D k p.1.1 p.2)
      ((U ×ˢ (univ : Set PolarPoint)) ×ˢ univ))
    (n : ℕ) (p : E × PolarPoint) (v : Fin n → E × ℝ) :
    (continuousTimeSpeedTower_of_stateAngularJets hU hf J hJ).D n p v =
      stateAngleJet (fun b k => (J b p.2).D k p.1) n v := rfl

theorem continuousTimeSpeedTower_of_stateAngularJets_pureSlots
    {U : Set E} {f : E × PolarPoint → ℝ} (hU : IsOpen U)
    (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : PolarPoint, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (hJ : ∀ b k, ContinuousOn
      (fun p : (E × PolarPoint) × (Fin k → E) => (J b p.1.2).D k p.1.1 p.2)
      ((U ×ˢ (univ : Set PolarPoint)) ×ˢ univ))
    {n : ℕ} (w : StateAngleWord n) (p : E × PolarPoint)
    (v : Fin w.stateArity → E) :
    (continuousTimeSpeedTower_of_stateAngularJets hU hf J hJ).D n p (w.pureSlots v) =
      (J w.angleArity p.2).D w.stateArity p.1 v := by
  rw [continuousTimeSpeedTower_of_stateAngularJets_D_apply, stateAngleJet_pureSlots]

end ContinuousFlexibility.Analysis
