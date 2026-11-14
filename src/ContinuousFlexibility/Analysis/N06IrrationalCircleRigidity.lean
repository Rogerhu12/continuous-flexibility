module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Rigidity of the actual reference boundary circle

A continuous lift of a circle map has the same displacement as any
translation that it conjugates to a translation.  If that displacement
is incommensurable with the circle period, the lift differs from the
identity by a constant.  Reflection fixes that constant.

The last theorem uses the irrationality retained by the original
`RadialReturnMargins`; it does not introduce a new nonresonance premise.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped Topology

theorem n06_periodic_eq_const_of_irrational
    {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (ha : Function.Periodic f a) (hb : Function.Periodic f b)
    (hirr : Irrational (a / b)) (x : ℝ) : f x = f 0 := by
  let P : AddSubgroup ℝ :=
    { carrier := {t | Function.Periodic f t}
      zero_mem' := fun y => by simp only [add_zero]
      add_mem' := fun hp hq => hp.add_period hq
      neg_mem' := fun hp => hp.neg }
  have hsub : AddSubgroup.closure ({a, b} : Set ℝ) ≤ P := by
    apply (AddSubgroup.closure_le P).mpr
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact ha
    · rw [Set.mem_singleton_iff] at ht
      subst t
      exact hb
  have heq : EqOn f (fun _ => f 0)
      (AddSubgroup.closure ({a, b} : Set ℝ) : Set ℝ) := by
    intro t ht
    simpa only [zero_add] using (hsub ht) 0
  exact heq.closure hf continuous_const
    ((dense_addSubgroupClosure_pair_iff.mpr hirr) x)

/-- The lift condition determines the displacement of a second
translation.  Continuity supplies exactly the finite period integrals. -/
theorem n06_circleLift_translation_displacement
    {β : ℝ → ℝ} {t c : ℝ} (hβ : Continuous β)
    (hlift : ∀ θ, β (θ + Real.pi) = β θ + Real.pi)
    (hstep : ∀ θ, β (θ + t) = β θ + c) : c = t := by
  let d : ℝ → ℝ := fun θ => β θ - θ
  have hd : Continuous d := hβ.sub continuous_id
  have hp : Function.Periodic d Real.pi := by
    intro θ
    dsimp only [d]
    rw [hlift]
    ring
  have htranslate : (∫ θ in (0 : ℝ)..Real.pi, d (θ + t)) =
      ∫ θ in (0 : ℝ)..Real.pi, d θ := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm t Real.pi] using hp.intervalIntegral_add_eq t 0
  have hfun : (fun θ => d (θ + t)) = (fun θ => d θ + (c - t)) := by
    funext θ
    dsimp only [d]
    rw [hstep]
    ring
  rw [hfun, intervalIntegral.integral_add
    (hd.intervalIntegrable 0 Real.pi)
    (continuous_const.intervalIntegrable 0 Real.pi),
    intervalIntegral.integral_const] at htranslate
  simp only [sub_zero, smul_eq_mul] at htranslate
  have hzero : Real.pi * (c - t) = 0 := by linarith only [htranslate]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left Real.pi_ne_zero)

/-- A circle lift commuting with an irrational rotation is a translation;
the original reflection law makes it the identity. -/
theorem n06_circleLift_eq_id_of_irrational
    {β : ℝ → ℝ} {t : ℝ} (hβ : Continuous β)
    (hlift : ∀ θ, β (θ + Real.pi) = β θ + Real.pi)
    (hodd : Function.Odd β)
    (hstep : ∀ θ, β (θ + t) = β θ + t)
    (hirr : Irrational (t / Real.pi)) : β = id := by
  have hzero : β 0 = 0 := by
    have hz := hodd 0
    simp only [neg_zero] at hz
    linarith only [hz]
  have hp : Function.Periodic (fun θ => β θ - θ) Real.pi := by
    intro θ
    change β (θ + Real.pi) - (θ + Real.pi) = β θ - θ
    rw [hlift]
    ring
  have ht : Function.Periodic (fun θ => β θ - θ) t := by
    intro θ
    change β (θ + t) - (θ + t) = β θ - θ
    rw [hstep]
    ring
  funext θ
  have he := n06_periodic_eq_const_of_irrational
    (hβ.sub continuous_id) ht hp hirr θ
  change β θ - θ = β 0 - 0 at he
  change β θ = θ
  linarith only [he, hzero]

/-- At the end of a negative component, the actual retained return
margin eliminates every nontrivial odd boundary reparametrization. -/
theorem n06_referenceBoundaryCircle_eq_id
    {D : ReferenceData} (hD : RadialReturnMargins D)
    {l r : ℝ} (hneg : NegativeRadialComponent D l r)
    {β : ℝ → ℝ} (hβ : Continuous β)
    (hlift : ∀ θ, β (θ + Real.pi) = β θ + Real.pi)
    (hodd : Function.Odd β)
    (hstep : ∀ θ, β (θ + radialTravel D l r) = β θ + radialTravel D l r) :
    β = id := by
  obtain ⟨C, _, hreturn⟩ := hD.2
  exact n06_circleLift_eq_id_of_irrational hβ hlift hodd hstep
    (hreturn l r hneg).1.1

end ContinuousFlexibility.Statements
