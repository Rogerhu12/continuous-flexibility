import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Analysis.PositiveHeightTaylorInterpolation
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Genuine parameter towers of the actual logarithmic root traces

Only the finitely many raw radial traces used by the Taylor polynomial
are inputs. Their angular parameter towers construct the logarithmic
traces by the scalar partition formula at the actual root. Pointwise
smoothness at the root suffices; no common spatial collar is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- The scalar chain rule at the actual root uses exactly the radial
orders in the original ordered partitions. -/
theorem n04Realization_log_radialBoundaryJet
    {f : PolarPoint → ℝ} {c θ : ℝ}
    (hf : ContDiffAt ℝ ∞ f (c, θ)) (hpos : 0 < f (c, θ)) (n : ℕ) :
    radialBoundaryJet (fun q => Real.log (f q)) c n θ =
      ∑ π : OrderedFinpartition n,
        iteratedDeriv π.length Real.log (f (c, θ)) *
          ∏ i : Fin π.length, radialBoundaryJet f c (π.partSize i) θ := by
  have hslice : ContDiffAt ℝ ∞ (fun r : ℝ => f (r, θ)) c :=
    hf.comp c (contDiffAt_id.prodMk contDiffAt_const)
  have hlog : ContDiffAt ℝ ∞ Real.log (f (c, θ)) :=
    Real.contDiffAt_log.mpr hpos.ne'
  simpa only [radialBoundaryJet, Function.comp_def] using
    iteratedDeriv_comp_eq_sum_orderedFinpartition hlog hslice
      (by simp : (n : ℕ∞ω) ≤ ∞)

/-- A function of the angle has no positive radial derivatives. -/
theorem n04Realization_mixedDerivative_angularField
    (f : ℝ → ℝ) (a b : ℕ) (q : PolarPoint) :
    mixedDerivative a b (fun p => f p.2) q =
      if a = 0 then iteratedDeriv b f q.2 else 0 := by
  simp only [mixedDerivative, iteratedDeriv_const]

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Angular raw trace towers fit the existing mixed-jet interface without
adding radial information or a parameter regularity assumption. -/
def n04Realization_angularField_mixedJetRegularity
    {U : Set X} {f : X → ℝ → ℝ} (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiff ℝ ∞ (f x))
    (J : ∀ b θ, SmoothDirections U (fun x => iteratedDeriv b (f x) θ)) :
    MixedJetRegularity U univ (fun x q => f x q.2) where
  spatial x hx := ((hf x hx).comp contDiff_snd).contDiffOn
  parameter a b q _ := by
    by_cases ha : a = 0
    · subst a
      exact (J b q.2).congr (fun _ _ => by
        simp only [n04Realization_mixedDerivative_angularField, ite_true])
    · exact (smoothDirections_constant hU (0 : ℝ)).congr (fun _ _ => by
        simp only [n04Realization_mixedDerivative_angularField, if_neg ha])

/-- Every angular and parameter derivative of the actual logarithmic
radial trace is constructed from the raw radial prefix through `n`.
The original parameter domain is unchanged. -/
def n04Realization_logBoundaryTrace_mixedJetRegularity
    {U : Set X} {f : X → PolarPoint → ℝ} (hU : IsOpen U) (c : ℝ) (n : ℕ)
    (hf : ∀ x ∈ U, ∀ θ, ContDiffAt ℝ ∞ (f x) (c, θ))
    (hpos : ∀ x ∈ U, ∀ θ, 0 < f x (c, θ))
    (J : ∀ j : ℕ, j ≤ n → ∀ b θ,
      SmoothDirections U (fun x => iteratedDeriv b (radialBoundaryJet (f x) c j) θ)) :
    MixedJetRegularity U univ
      (fun x q => radialBoundaryJet (fun p => Real.log (f x p)) c n q.2) := by
  classical
  let F : Fin (n + 1) → X → PolarPoint → ℝ :=
    fun j x q => radialBoundaryJet (f x) c j.val q.2
  let RF : ∀ j, MixedJetRegularity U univ (F j) := fun j =>
    n04Realization_angularField_mixedJetRegularity hU
      (fun x hx => contDiff_radialBoundaryJet_of_contDiffAt c (hf x hx) j.val)
      (J j.val (Nat.le_of_lt_succ j.isLt))
  let index : (π : OrderedFinpartition n) → Fin π.length → Fin (n + 1) :=
    fun π i => ⟨π.partSize i, Nat.lt_succ_of_le (π.partSize_le i)⟩
  let V : Set (Fin (n + 1) → ℝ) := {y | 0 < y 0}
  let G : (Fin (n + 1) → ℝ) → ℝ := fun y =>
    ∑ π : OrderedFinpartition n,
      iteratedDeriv π.length Real.log (y 0) * ∏ i : Fin π.length, y (index π i)
  have hV : IsOpen V := isOpen_Ioi.preimage (continuous_apply 0)
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    fun t ht => (Real.contDiffAt_log.mpr ht.ne').contDiffWithinAt
  have hG : ContDiffOn ℝ ∞ G V := by
    apply ContDiffOn.sum
    intro π _
    have houter : ContDiffOn ℝ ∞
        (fun y : Fin (n + 1) → ℝ => iteratedDeriv π.length Real.log (y 0)) V :=
      (contDiffOn_iteratedDeriv_open isOpen_Ioi hlog π.length).comp
        (contDiff_apply ℝ ℝ (0 : Fin (n + 1))).contDiffOn (fun _ hy => hy)
    exact houter.mul (contDiffOn_prod (fun i _ =>
      (contDiff_apply ℝ ℝ (index π i)).contDiffOn))
  have hmap (x : X) (hx : x ∈ U) (q : PolarPoint) (_hq : q ∈ (univ : Set PolarPoint)) :
      (fun j => F j x q) ∈ V := by
    simpa only [V, Set.mem_setOf_eq, F, Fin.val_zero, radialBoundaryJet,
      iteratedDeriv_zero] using hpos x hx q.2
  let RG := MixedJetRegularity.finiteComp RF hU isOpen_univ hV hG hmap
  refine RG.congr isOpen_univ ?_ ?_
  · intro x hx
    exact ((contDiff_radialBoundaryJet_of_contDiffAt c
      (fun θ => (hf x hx θ).log (hpos x hx θ).ne') n).comp contDiff_snd).contDiffOn
  · intro x hx q _hq
    simpa only [G, F, index, Fin.val_zero, radialBoundaryJet, iteratedDeriv_zero]
      using (n04Realization_log_radialBoundaryJet (hf x hx q.2) (hpos x hx q.2) n).symm

/-- The axis output is a genuine parameter tower for the original
angular derivative, including the zeroth radial Taylor coefficient. -/
def n04Realization_logBoundaryTrace_parameterTower
    {U : Set X} {f : X → PolarPoint → ℝ} (hU : IsOpen U) (c : ℝ) (n : ℕ)
    (hf : ∀ x ∈ U, ∀ θ, ContDiffAt ℝ ∞ (f x) (c, θ))
    (hpos : ∀ x ∈ U, ∀ θ, 0 < f x (c, θ))
    (J : ∀ j : ℕ, j ≤ n → ∀ b θ,
      SmoothDirections U (fun x => iteratedDeriv b (radialBoundaryJet (f x) c j) θ))
    (b : ℕ) (θ : ℝ) :
    SmoothDirections U (fun x => iteratedDeriv b
      (radialBoundaryJet (fun p => Real.log (f x p)) c n) θ) :=
  ((n04Realization_logBoundaryTrace_mixedJetRegularity hU c n hf hpos J).parameter
    0 b (0, θ) (mem_univ _)).congr (fun _ _ => by
      simp only [n04Realization_mixedDerivative_angularField, ite_true])

end ContinuousFlexibility.Analysis
