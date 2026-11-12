import ContinuousFlexibility.Analysis.N04bLiftTranslationBounds

/-!
# Actual near-identity circle conjugacies

A periodic Lipschitz corrector g gives H_q(x)=x+q g(x). If |q| L<1,
the displacement estimate makes H_q strictly increasing. Continuity and
the period-one lift property make it surjective, so it defines an actual
unit in mathlib's monoid of lifts.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Strict monotonicity follows from the actual corrector differences. -/
theorem n04bNearIdentity_strictMono (q L : ℝ) (g : ℝ → ℝ)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (hsmall : |q| * L < 1) :
    StrictMono (fun x : ℝ => x + q * g x) := by
  intro x y hxy
  have hdiff := hLip y x
  rw [abs_of_pos (sub_pos.mpr hxy)] at hdiff
  have hmul := mul_le_mul_of_nonneg_left hdiff (abs_nonneg q)
  have hneg := neg_abs_le (q * (g y - g x))
  rw [abs_mul] at hneg
  have hpos : 0 < (1 - |q| * L) * (y - x) :=
    mul_pos (sub_pos.mpr hsmall) (sub_pos.mpr hxy)
  dsimp only
  nlinarith

def n04bNearIdentityLift (q L : ℝ) (g : ℝ → ℝ)
    (hperiod : Function.Periodic g 1)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (hsmall : |q| * L < 1) : CircleDeg1Lift where
  toFun x := x + q * g x
  monotone' := (n04bNearIdentity_strictMono q L g hLip hsmall).monotone
  map_add_one' := by
    intro x
    rw [hperiod x]
    ring

theorem n04bNearIdentityLift_apply (q L : ℝ) (g : ℝ → ℝ)
    (hperiod : Function.Periodic g 1)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (hsmall : |q| * L < 1) (x : ℝ) :
    n04bNearIdentityLift q L g hperiod hLip hsmall x = x + q * g x := rfl

theorem n04bNearIdentityLift_isUnit (q L : ℝ) (g : ℝ → ℝ)
    (hperiod : Function.Periodic g 1)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (hsmall : |q| * L < 1) (hcont : Continuous g) :
    IsUnit (n04bNearIdentityLift q L g hperiod hLip hsmall) := by
  apply CircleDeg1Lift.isUnit_iff_bijective.mpr
  refine ⟨(n04bNearIdentity_strictMono q L g hLip hsmall).injective, ?_⟩
  apply (CircleDeg1Lift.continuous_iff_surjective _).mp
  exact continuous_id.add (continuous_const.mul hcont)

def n04bNearIdentityUnit (q L : ℝ) (g : ℝ → ℝ)
    (hperiod : Function.Periodic g 1)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (hsmall : |q| * L < 1) (hcont : Continuous g) : CircleDeg1Liftˣ :=
  (n04bNearIdentityLift_isUnit q L g hperiod hLip hsmall hcont).unit

theorem n04bNearIdentityUnit_val (q L : ℝ) (g : ℝ → ℝ)
    (hperiod : Function.Periodic g 1)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (hsmall : |q| * L < 1) (hcont : Continuous g) :
    (n04bNearIdentityUnit q L g hperiod hLip hsmall hcont : CircleDeg1Lift) =
      n04bNearIdentityLift q L g hperiod hLip hsmall :=
  IsUnit.unit_spec _

theorem n04bNearIdentityUnit_apply (q L : ℝ) (g : ℝ → ℝ)
    (hperiod : Function.Periodic g 1)
    (hLip : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (hsmall : |q| * L < 1) (hcont : Continuous g) (x : ℝ) :
    n04bNearIdentityUnit q L g hperiod hLip hsmall hcont x = x + q * g x := by
  have hh := congrArg (fun F : CircleDeg1Lift => F x)
    (n04bNearIdentityUnit_val q L g hperiod hLip hsmall hcont)
  exact hh.trans (n04bNearIdentityLift_apply q L g hperiod hLip hsmall x)

end ContinuousFlexibility.Analysis
