import ContinuousFlexibility.Analysis.CircleReturnAlgebra
import ContinuousFlexibility.Analysis.N01ReturnMargins
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Uniqueness for the actual circle return operator

The kernel argument needs only continuity, oddness and an irrational
travel angle. A function killed by `M_T` has periods pi and `2T`.
Those periods generate a dense subgroup, so continuity makes the
function constant; oddness makes the constant zero.

Unlike the finite-sum uniqueness lemma, this applies to every element
of the supplied physical circle model, without assuming a Fourier
expansion in advance.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set

/-- A continuous function with two incommensurable periods is constant. -/
theorem circleReturn_eq_zero_value_of_two_periods {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (ha : Function.Periodic f a) (hb : Function.Periodic f b)
    (hirr : Irrational (a / b)) (x : ℝ) : f x = f 0 := by
  let P : AddSubgroup ℝ :=
    { carrier := {t | Function.Periodic f t}
      zero_mem' := fun t => by rw [add_zero]
      add_mem' := fun hu hv => hu.add_period hv
      neg_mem' := fun hu => hu.neg }
  have hgen : AddSubgroup.closure ({a, b} : Set ℝ) ≤ P := by
    apply (AddSubgroup.closure_le P).mpr
    intro t ht
    rcases Set.mem_insert_iff.mp ht with hta | htb
    · subst t
      exact ha
    · have htb' : t = b := Set.mem_singleton_iff.mp htb
      subst t
      exact hb
  have hd : Dense (AddSubgroup.closure ({a, b} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  have heq : f = fun _ : ℝ => f 0 := by
    apply Continuous.ext_on hd hf continuous_const
    intro t ht
    have hp : Function.Periodic f t := hgen ht
    simpa only [zero_add] using hp 0
  exact congrFun heq x

/-- Zero return residual gives the second period on the entire function,
not just on a collection of Fourier coefficients. -/
theorem circleReturnShift_zero_period {f : ℝ → ℝ} {T : ℝ}
    (hodd : ∀ θ, f (-θ) = -f θ) (hz : ∀ θ, circleReturnShift T f θ = 0) :
    Function.Periodic f (2 * T) := by
  intro θ
  have h := hz (θ + T)
  rw [circleReturnShift_odd hodd] at h
  have hplus : θ + T + T = θ + 2 * T := by ring
  have hminus : θ + T - T = θ := by ring
  rw [hplus, hminus] at h
  linarith

/-- The return operator has zero kernel among continuous odd functions
of period pi whenever its travel angle divided by pi is irrational. -/
theorem circleReturnShift_odd_kernel {f : ℝ → ℝ} {T : ℝ}
    (hf : Continuous f) (hp : Function.Periodic f Real.pi)
    (hodd : ∀ θ, f (-θ) = -f θ) (hT : Irrational (T / Real.pi))
    (hz : ∀ θ, circleReturnShift T f θ = 0) : ∀ θ, f θ = 0 := by
  have h2 : Irrational ((2 * T) / Real.pi) := by
    have h := hT.natCast_mul (m := 2) (by decide)
    simpa only [Nat.cast_ofNat, mul_div_assoc] using h
  have hperiod := circleReturnShift_zero_period hodd hz
  have hzero : f 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    linarith
  intro θ
  rw [circleReturn_eq_zero_value_of_two_periods hf hperiod hp h2 θ, hzero]

theorem circleReturnShift_sub (T : ℝ) (f g : ℝ → ℝ) (θ : ℝ) :
    circleReturnShift T (fun t => f t - g t) θ =
      circleReturnShift T f θ - circleReturnShift T g θ := by
  unfold circleReturnShift circleReturnEven
  ring

/-- Full, rather than finite-Fourier, uniqueness of the odd preimage. -/
theorem circleReturnShift_injective_on_odd {f g : ℝ → ℝ} {T : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfp : Function.Periodic f Real.pi) (hgp : Function.Periodic g Real.pi)
    (hfo : ∀ θ, f (-θ) = -f θ) (hgo : ∀ θ, g (-θ) = -g θ)
    (hT : Irrational (T / Real.pi))
    (heq : ∀ θ, circleReturnShift T f θ = circleReturnShift T g θ) : f = g := by
  have hp : Function.Periodic (fun θ => f θ - g θ) Real.pi := by
    intro θ
    dsimp only
    rw [hfp θ, hgp θ]
  have ho : ∀ θ, (f (-θ) - g (-θ)) = -(f θ - g θ) := by
    intro θ
    rw [hfo, hgo]
    ring
  have hz : ∀ θ, circleReturnShift T (fun t => f t - g t) θ = 0 := by
    intro θ
    rw [circleReturnShift_sub, heq θ, sub_self]
  have h := circleReturnShift_odd_kernel (hf.sub hg) hp ho hT hz
  funext θ
  exact sub_eq_zero.mp (h θ)

open ContinuousFlexibility.Statements

/-- Uniqueness on the actual circle carrier supplied by N01. The result
uses the decoding injectivity and the nonresonance already proved for
the stored travel angles. -/
theorem n01Properties_circleRotationDifference_injective
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε) (hS : IsPhysicalSpaces D T S)
    {u v : CircleSpace S} (hu : IsOddCircle S u) (hv : IsOddCircle S v)
    (heq : ∀ m θ, circleRotationDifference S C u m θ =
      circleRotationDifference S C v m θ) : u = v := by
  have hm := hS.2.1 (3 / 4 : ℝ)
  apply hm.2.2.2.2.2.1
  funext m
  have hup := (hm.2.2.2.1 u).1 m
  have hvp := (hm.2.2.2.1 v).1 m
  apply circleReturnShift_injective_on_odd hup.1.continuous hvp.1.continuous
    hup.2 hvp.2 (hu m) (hv m)
    (n01Properties_travel_quadraticIrrational hN01 m).1
  exact heq m

end ContinuousFlexibility.Analysis
