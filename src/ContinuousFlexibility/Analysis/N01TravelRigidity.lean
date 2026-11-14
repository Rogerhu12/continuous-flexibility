module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Analysis.IrrationalLiftRigidity

/-!
# The actual N01 travel angle supplies the rigidity frequency

The control intervals are genuine negative components of the fixed
radial reference. Its frozen return margin supplies irrationality of
their travel divided by π. Thus the two return translations determine
a normalized continuous degree-one boundary lift uniquely.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n01_travel_div_pi_irrational
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    Irrational (C.travel m / Real.pi) := by
  have hgeometry : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨ho, hroot, _, hnegative, _, _, _, htravel, _⟩ := hgeometry
  have hcomponent : NegativeRadialComponent D (C.left m) (C.right m) :=
    ⟨(ho m).1, (ho m).2.1, (ho m).2.2,
      (hroot m).1, (hroot m).2.1, hnegative m⟩
  obtain ⟨_, _, hreturn⟩ := hN.1.2.2.1.2
  have hirr := (hreturn (C.left m) (C.right m) hcomponent).1.1
  simpa only [htravel m, radialTravel] using hirr

theorem n01_double_travel_div_pi_irrational
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    Irrational ((2 * C.travel m) / Real.pi) := by
  have h := (n01_travel_div_pi_irrational hN m).natCast_mul (m := 2) (by decide)
  simpa only [Nat.cast_ofNat, mul_div_assoc] using h

/-- Once the actual characteristic-return identities give a second
constant increment, its size and the whole normalized boundary lift
are forced. No quantitative coordinate estimate enters this result. -/
theorem n01_periodicLift_eq_id_of_return_increment
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ)
    {f : ℝ → ℝ} {b : ℝ} (hf : Continuous f)
    (hperiod : ∀ t, f (t + Real.pi) = f t + Real.pi)
    (hreturn : ∀ t, f (t + 2 * C.travel m) = f t + b)
    (hzero : f 0 = 0) :
    b = 2 * C.travel m ∧ ∀ t, f t = t :=
  periodicLift_eq_id_of_irrational_shift Real.pi_ne_zero hf hperiod hreturn
    (n01_double_travel_div_pi_irrational hN m) hzero

end ContinuousFlexibility.Analysis
