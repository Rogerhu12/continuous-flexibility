module

public import ContinuousFlexibility.Analysis.IrrationalLiftRigidity
public import ContinuousFlexibility.Analysis.CircleInverseExistence

/-!
# Two-return rigidity of actual boundary circle lifts

Two simultaneous translation identities determine both boundary lifts.
Only the left reference lift needs its explicit continuous inverse; the
right reference lift is used through injectivity. This avoids assuming
any regularity of a supplied right inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function

/-- The two returns force equality of the translation lengths and of the
two normalized boundary lifts. -/
theorem boundaryLifts_eq_of_two_irrational_returns
    {l r α β Pminus Pplus : ℝ → ℝ} {T W c : ℝ}
    (hc : 0 < c) (hlower : ∀ θ, c ≤ deriv l θ)
    (hlperiod : ∀ θ, l (θ + Real.pi) = l θ + Real.pi) (hlzero : l 0 = 0)
    (hrinj : Injective r)
    (hα : Continuous α) (hαperiod : ∀ θ, α (θ + Real.pi) = α θ + Real.pi)
    (hαzero : α 0 = 0)
    (hreference : ∀ θ, r (Pminus θ) = l θ - T ∧ r (Pplus θ) = l θ + T)
    (hcanonical : ∀ θ, β (Pminus θ) = α θ - W ∧ β (Pplus θ) = α θ + W)
    (hirr : Irrational ((2 * T) / Real.pi)) :
    W = T ∧ (∀ θ, α θ = l θ) ∧ ∀ θ, β θ = r θ := by
  let v : ℝ → ℝ := Function.invFun l
  have hlbij : Bijective l := bijective_of_deriv_lower_bound hc hlower
  have hlv (t : ℝ) : l (v t) = t := rightInverse_invFun_of_deriv_lower_bound hc hlower t
  have hvl (θ : ℝ) : v (l θ) = θ := leftInverse_invFun_of_deriv_lower_bound hc hlower θ
  have hv : Continuous v := continuous_invFun_of_deriv_lower_bound hc hlower
  have hvperiod (t : ℝ) : v (t + Real.pi) = v t + Real.pi := by
    apply hlbij.1
    rw [hlv, hlperiod, hlv]
  have hvzero : v 0 = 0 := by
    apply hlbij.1
    rw [hlv, hlzero]
  let f : ℝ → ℝ := fun t => α (v t)
  have hf : Continuous f := hα.comp hv
  have hfperiod (t : ℝ) : f (t + Real.pi) = f t + Real.pi := by
    dsimp only [f]
    rw [hvperiod, hαperiod]
  have hfzero : f 0 = 0 := by
    dsimp only [f]
    rw [hvzero, hαzero]
  have hfshift (t : ℝ) : f (t + 2 * T) = f t + 2 * W := by
    have hp : Pminus (v (t + 2 * T)) = Pplus (v t) := by
      apply hrinj
      rw [(hreference _).1, (hreference _).2, hlv, hlv]
      ring
    have htwo : α (v (t + 2 * T)) - W = α (v t) + W := by
      calc
        _ = β (Pminus (v (t + 2 * T))) := (hcanonical _).1.symm
        _ = β (Pplus (v t)) := congrArg β hp
        _ = _ := (hcanonical _).2
    dsimp only [f]
    linarith only [htwo]
  obtain ⟨hwidth, hid⟩ := periodicLift_eq_id_of_irrational_shift
    Real.pi_ne_zero hf hfperiod hfshift hirr hfzero
  have hWT : W = T := by linarith only [hwidth]
  have halpha (θ : ℝ) : α θ = l θ := by
    simpa only [f, hvl] using hid (l θ)
  refine ⟨hWT, halpha, ?_⟩
  intro θ
  have hp : Pminus (v (r θ + T)) = θ := by
    apply hrinj
    rw [(hreference _).1, hlv]
    ring
  calc
    β θ = β (Pminus (v (r θ + T))) := congrArg β hp.symm
    _ = α (v (r θ + T)) - W := (hcanonical _).1
    _ = l (v (r θ + T)) - T := by rw [halpha, hWT]
    _ = r θ := by rw [hlv]; ring

end ContinuousFlexibility.Analysis
