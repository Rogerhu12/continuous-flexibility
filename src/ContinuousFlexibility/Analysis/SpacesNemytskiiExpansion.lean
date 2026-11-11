import ContinuousFlexibility.Analysis.SpacesNemytskiiDifferentiation
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# The finite spatial jet formula for smooth composition

Repeated coordinate differentiation produces an explicit finite list of
normalized composition terms. Every term has total derivative order at
most the requested mixed order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

namespace SpacesNemytskiiTerm

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {k : ℕ}

def derivativeTerms (hT : IsMaterialData D T) (radial : Bool) (t : SpacesNemytskiiTerm T γ k) :
    List (SpacesNemytskiiTerm T γ k) :=
  [t.coefficientDerivative radial, t.chainWeightDerivative hT radial, t.chainBaseDerivative hT radial] ++
    (List.ofFn fun i => t.baseDerivative i radial) ++
      List.ofFn fun i => t.directionDerivative i radial

theorem derivativeTerms_order (hT : IsMaterialData D T) (radial : Bool)
    (t : SpacesNemytskiiTerm T γ k) :
    ∀ τ ∈ t.derivativeTerms hT radial, τ.order ≤ t.order + 1 := by
  intro τ hτ
  simp only [derivativeTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn] at hτ
  rcases hτ with ((rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · simp only [coefficientDerivative_order]; omega
  · simp only [chainWeightDerivative_order]; omega
  · simp only [chainBaseDerivative_order, le_refl]
  · simp only [baseDerivative_order, le_refl]
  · simp only [directionDerivative_order, le_refl]

def evaluateTerms (L : List (SpacesNemytskiiTerm T γ k)) (F : ℝ → ℝ) (u : PolarPoint → ℝ)
    (v : Fin k → PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  (L.map fun t => t.evaluate F u v p).sum

@[simp] theorem evaluateTerms_nil (F : ℝ → ℝ) (u : PolarPoint → ℝ)
    (v : Fin k → PolarPoint → ℝ) (p : PolarPoint) :
    evaluateTerms ([] : List (SpacesNemytskiiTerm T γ k)) F u v p = 0 := rfl

@[simp] theorem evaluateTerms_cons (t : SpacesNemytskiiTerm T γ k) (L : List (SpacesNemytskiiTerm T γ k))
    (F : ℝ → ℝ) (u : PolarPoint → ℝ) (v : Fin k → PolarPoint → ℝ) (p : PolarPoint) :
    evaluateTerms (t :: L) F u v p = t.evaluate F u v p + evaluateTerms L F u v p := rfl

theorem evaluateTerms_append (L R : List (SpacesNemytskiiTerm T γ k))
    (F : ℝ → ℝ) (u : PolarPoint → ℝ) (v : Fin k → PolarPoint → ℝ) (p : PolarPoint) :
    evaluateTerms (L ++ R) F u v p = evaluateTerms L F u v p + evaluateTerms R F u v p := by
  simp only [evaluateTerms, List.map_append, List.sum_append]

theorem evaluate_derivativeTerms (hT : IsMaterialData D T) (radial : Bool)
    (t : SpacesNemytskiiTerm T γ k) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {v : Fin k → PolarPoint → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i)) (p : PolarPoint) :
    evaluateTerms (t.derivativeTerms hT radial) F u v p = spacesPartial radial (t.evaluate F u v) p := by
  rw [t.evaluate_partial hT hF hu hv]
  simp only [evaluateTerms, derivativeTerms, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  ring

theorem evaluateTerms_contDiff (hT : IsMaterialData D T) (L : List (SpacesNemytskiiTerm T γ k))
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {v : Fin k → PolarPoint → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i)) :
    ContDiff ℝ ∞ (evaluateTerms L F u v) := by
  induction L with
  | nil => exact contDiff_const
  | cons t L ih => exact (t.evaluate_contDiff hT hF hu hv).add ih

def differentiateTerms (hT : IsMaterialData D T) (radial : Bool)
    (L : List (SpacesNemytskiiTerm T γ k)) : List (SpacesNemytskiiTerm T γ k) :=
  L.flatMap (derivativeTerms hT radial)

theorem differentiateTerms_order (hT : IsMaterialData D T) (radial : Bool)
    {L : List (SpacesNemytskiiTerm T γ k)} {n : ℕ} (hL : ∀ t ∈ L, t.order ≤ n) :
    ∀ t ∈ differentiateTerms hT radial L, t.order ≤ n + 1 := by
  intro t ht
  obtain ⟨τ, hτ, htτ⟩ := List.mem_flatMap.mp ht
  exact (τ.derivativeTerms_order hT radial t htτ).trans (Nat.add_le_add_right (hL τ hτ) 1)

private theorem spacesPartial_add {f g : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (radial : Bool) (p : PolarPoint) :
    spacesPartial radial (fun q => f q + g q) p = spacesPartial radial f p + spacesPartial radial g p := by
  cases radial
  · exact angularPartial_add (hf.differentiable (by simp) p) (hg.differentiable (by simp) p)
  · exact radialPartial_add (hf.differentiable (by simp) p) (hg.differentiable (by simp) p)

theorem evaluate_differentiateTerms (hT : IsMaterialData D T) (radial : Bool)
    (L : List (SpacesNemytskiiTerm T γ k)) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {v : Fin k → PolarPoint → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i)) (p : PolarPoint) :
    evaluateTerms (differentiateTerms hT radial L) F u v p = spacesPartial radial (evaluateTerms L F u v) p := by
  induction L with
  | nil =>
    change 0 = spacesPartial radial (fun _ => 0) p
    cases radial
    · exact (angularPartial_const 0).symm
    · exact (radialPartial_const 0).symm
  | cons t L ih =>
    change evaluateTerms (t.derivativeTerms hT radial ++ differentiateTerms hT radial L) F u v p = _
    rw [evaluateTerms_append, evaluate_derivativeTerms hT radial t hF hu hv, ih]
    exact (spacesPartial_add (t.evaluate_contDiff hT hF hu hv)
      (evaluateTerms_contDiff hT L hF hu hv) radial p).symm

def angularExpansion (hT : IsMaterialData D T) (γ : ℝ) (k : ℕ) : ℕ → List (SpacesNemytskiiTerm T γ k)
  | 0 => [initial hT γ k]
  | b + 1 => differentiateTerms hT false (angularExpansion hT γ k b)

def jetExpansion (hT : IsMaterialData D T) (γ : ℝ) (k : ℕ) : ℕ → ℕ → List (SpacesNemytskiiTerm T γ k)
  | 0, b => angularExpansion hT γ k b
  | a + 1, b => differentiateTerms hT true (jetExpansion hT γ k a b)

theorem angularExpansion_order (hT : IsMaterialData D T) (γ : ℝ) (k b : ℕ) :
    ∀ t ∈ angularExpansion hT γ k b, t.order ≤ b := by
  induction b with
  | zero => simp only [angularExpansion, List.mem_singleton, forall_eq, initial_order, le_refl]
  | succ b ih => exact differentiateTerms_order hT false ih

theorem jetExpansion_order (hT : IsMaterialData D T) (γ : ℝ) (k a b : ℕ) :
    ∀ t ∈ jetExpansion hT γ k a b, t.order ≤ a + b := by
  induction a with
  | zero => simpa only [jetExpansion, Nat.zero_add] using angularExpansion_order hT γ k b
  | succ a ih =>
    have h := differentiateTerms_order hT true ih
    simpa only [jetExpansion, Nat.add_right_comm a b 1] using h

theorem evaluate_angularExpansion (hT : IsMaterialData D T) (γ : ℝ) (k b : ℕ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {v : Fin k → PolarPoint → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i)) :
    evaluateTerms (angularExpansion hT γ k b) F u v =
      mixedDerivative 0 b ((initial hT γ k).evaluate F u v) := by
  induction b with
  | zero =>
    funext p
    simp only [angularExpansion, evaluateTerms_cons, evaluateTerms_nil, add_zero,
      mixedDerivative, iteratedDeriv_zero]
  | succ b ih =>
    funext p
    rw [angularExpansion, evaluate_differentiateTerms hT false _ hF hu hv, ih]
    exact congrFun (angularPartial_mixedDerivative ((initial hT γ k).evaluate_contDiff hT hF hu hv) 0 b) p

theorem evaluate_jetExpansion (hT : IsMaterialData D T) (γ : ℝ) (k a b : ℕ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {v : Fin k → PolarPoint → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i)) :
    evaluateTerms (jetExpansion hT γ k a b) F u v =
      mixedDerivative a b ((initial hT γ k).evaluate F u v) := by
  induction a with
  | zero => exact evaluate_angularExpansion hT γ k b hF hu hv
  | succ a ih =>
    funext p
    rw [jetExpansion, evaluate_differentiateTerms hT true _ hF hu hv, ih]
    exact congrFun (radialPartial_mixedDerivative ((initial hT γ k).evaluate_contDiff hT hF hu hv) a b) p

end SpacesNemytskiiTerm

end ContinuousFlexibility.Statements
