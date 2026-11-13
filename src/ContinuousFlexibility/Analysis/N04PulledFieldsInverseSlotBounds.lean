import ContinuousFlexibility.Analysis.N04RealizationDoubleExpansionHeight
import ContinuousFlexibility.Analysis.N04RealizationMixedJointDirections

/-!
# The original parameter count in the inverse-point spatial expansion

A pure parameter slot uses exactly one parameter derivative.  A pure
physical slot uses a radial or angular derivative and contributes no
parameter derivative.  The existing double scalar expansion therefore
uses only mixed jets with the original word's exact parameter count.
The factor `2 ^ angleArity` accounts for the two physical coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem n04PulledFieldsInverseSlot_head_zero
    (n : ℕ)
    (A : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (v : Fin (n + 1) → (E × ℝ) × ℝ) (hv : (v 0).1.1 = 0) :
    scalarAngularExpansion n
      (fun b k => scalarAngularExpansion k
        (fun a j => scalarAngularHead (fun a j => A a b j) (v 0).1 a j))
      (Fin.tail v) = 0 := by
  have hhead (b : ℕ) :
      (fun a j => scalarAngularHead (fun a j => A a b j) (v 0).1 a j) =
        (0 : ScalarAngularJetData E) := by
    funext a j
    apply MultilinearMap.ext
    intro u
    rw [scalarAngularHead_apply]
    exact (A a b (j + 1)).map_coord_zero 0 (by simpa only [Fin.cons_zero] using hv)
  have hzero :
      (fun b k => scalarAngularExpansion k
        (fun a j => scalarAngularHead (fun a j => A a b j) (v 0).1 a j)) =
        (0 : ScalarAngularJetData (E × ℝ)) := by
    funext b k
    simp only [hhead b, map_zero, Pi.zero_apply]
  rw [hzero, map_zero, zero_apply]

/-- Only the exact state count of a pure word enters its double
expansion.  The permitted parameter directions can be any predicate. -/
theorem n04PulledFields_doubleExpansion_pureSlots_bound
    (allowed : E → Prop) {n : ℕ} (w : StateAngleWord n)
    (A : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ a b : ℕ, a + b = w.angleArity →
      ∀ u : Fin w.stateArity → E, (∀ i, allowed (u i)) →
        |A a b w.stateArity u| ≤ C)
    (v : Fin n → (E × ℝ) × ℝ)
    (hv : ∀ i, allowed (v i).1.1)
    (hrad : ∀ i, |(v i).1.2| ≤ 1) (hang : ∀ i, |(v i).2| ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1.1 = 0)
    (hspatial : ∀ i, w.isState i = true → ((v i).1.2, (v i).2) = 0) :
    |scalarAngularExpansion n
      (fun b k => scalarAngularExpansion k (fun a j => A a b j)) v| ≤
        C * 2 ^ w.angleArity := by
  induction w generalizing A C with
  | nil =>
      have hh : |A 0 0 0 Fin.elim0| ≤ C := hA 0 0 rfl Fin.elim0 (fun i => i.elim0)
      change |A 0 0 0 Fin.elim0| ≤ C * 2 ^ 0
      simpa only [pow_zero, mul_one] using hh
  | @state n w ih =>
      let AH : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
        fun a b k => scalarAngularHead (fun a j => A a b j) (v 0).1 a k
      have hAH (a b : ℕ) (hab : a + b = w.angleArity)
          (u : Fin w.stateArity → E) (hu : ∀ i, allowed (u i)) :
          |AH a b w.stateArity u| ≤ C := by
        simpa only [AH, scalarAngularHead_apply, StateAngleWord.stateArity] using
          hA a b hab (Fin.cons (v 0).1.1 u)
            (fun i => Fin.cases (hv 0) (fun j => hu j) i)
      have hh := ih AH hC hAH (Fin.tail v) (fun i => hv i.succ)
        (fun i => hrad i.succ) (fun i => hang i.succ)
        (fun i hi => hstate i.succ hi) (fun i hi => hspatial i.succ hi)
      have hhead := hspatial 0 rfl
      have hr : (v 0).1.2 = 0 := congrArg Prod.fst hhead
      have ha : (v 0).2 = 0 := congrArg Prod.snd hhead
      rw [n04Realization_doubleAngularExpansion_succ_apply, hr, ha, zero_mul,
        zero_mul, add_zero, add_zero]
      exact hh
  | @angle n w ih =>
      let AR : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
        fun a b k => scalarAngularShift (fun a j => A a b j) a k
      let AT : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
        fun a b k => A a (b + 1) k
      have hAR (a b : ℕ) (hab : a + b = w.angleArity)
          (u : Fin w.stateArity → E) (hu : ∀ i, allowed (u i)) :
          |AR a b w.stateArity u| ≤ C :=
        hA (a + 1) b (by change (a + 1) + b = w.angleArity + 1; omega) u hu
      have hAT (a b : ℕ) (hab : a + b = w.angleArity)
          (u : Fin w.stateArity → E) (hu : ∀ i, allowed (u i)) :
          |AT a b w.stateArity u| ≤ C :=
        hA a (b + 1) (by change a + (b + 1) = w.angleArity + 1; omega) u hu
      have hr := ih AR hC hAR (Fin.tail v) (fun i => hv i.succ)
        (fun i => hrad i.succ) (fun i => hang i.succ)
        (fun i hi => hstate i.succ hi) (fun i hi => hspatial i.succ hi)
      have ha := ih AT hC hAT (Fin.tail v) (fun i => hv i.succ)
        (fun i => hrad i.succ) (fun i => hang i.succ)
        (fun i hi => hstate i.succ hi) (fun i hi => hspatial i.succ hi)
      have hM : 0 ≤ C * 2 ^ w.angleArity := mul_nonneg hC (pow_nonneg (by norm_num) _)
      have hr' := (mul_le_mul_of_nonneg_left hr (abs_nonneg (v 0).1.2)).trans
        (mul_le_of_le_one_left hM (hrad 0))
      have ha' := (mul_le_mul_of_nonneg_left ha (abs_nonneg (v 0).2)).trans
        (mul_le_of_le_one_left hM (hang 0))
      rw [n04Realization_doubleAngularExpansion_succ_apply,
        n04PulledFieldsInverseSlot_head_zero n A v (hstate 0 rfl), zero_add]
      change |(v 0).1.2 * scalarAngularExpansion n
          (fun b k => scalarAngularExpansion k (fun a j => AR a b j)) (Fin.tail v) +
        (v 0).2 * scalarAngularExpansion n
          (fun b k => scalarAngularExpansion k (fun a j => AT a b j)) (Fin.tail v)| ≤ _
      calc
        _ ≤ |(v 0).1.2| * |scalarAngularExpansion n
              (fun b k => scalarAngularExpansion k (fun a j => AR a b j)) (Fin.tail v)| +
            |(v 0).2| * |scalarAngularExpansion n
              (fun b k => scalarAngularExpansion k (fun a j => AT a b j)) (Fin.tail v)| := by
          simpa only [abs_mul] using abs_add_le
            ((v 0).1.2 * scalarAngularExpansion n
              (fun b k => scalarAngularExpansion k (fun a j => AR a b j)) (Fin.tail v))
            ((v 0).2 * scalarAngularExpansion n
              (fun b k => scalarAngularExpansion k (fun a j => AT a b j)) (Fin.tail v))
        _ ≤ C * 2 ^ w.angleArity + C * 2 ^ w.angleArity := add_le_add hr' ha'
        _ = C * 2 ^ (StateAngleWord.angle w).angleArity := by
          simp only [StateAngleWord.angleArity, pow_succ]
          ring

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The exact count estimate applies to any genuine tower of the same
joint function, by uniqueness against the existing mixed constructor. -/
theorem n04PulledFields_mixedJoint_pureSlots_bound
    {U : Set E} {I : Set ℝ} {f : E → PolarPoint → ℝ}
    (RF : MixedJetRegularity U (I ×ˢ (univ : Set ℝ)) f)
    (hU : IsOpen U) (hcU : Convex ℝ U) (hI : IsOpen I) (hcI : Convex ℝ I)
    (hb : ∀ a b, UniformScalarJetSeminormBounds
      (fun q : I ×ˢ (univ : Set ℝ) => RF.parameter a b q.val q.property))
    (J : SmoothDirections (U ×ˢ (I ×ˢ (univ : Set ℝ)))
      (fun z : E × PolarPoint => f z.1 z.2))
    (allowed : E → Prop) {n : ℕ} (w : StateAngleWord n)
    {x : E} (hx : x ∈ U) {q : PolarPoint} (hq : q ∈ I ×ˢ (univ : Set ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hraw : ∀ a b : ℕ, a + b = w.angleArity →
      ∀ u : Fin w.stateArity → E, (∀ i, allowed (u i)) →
        |(RF.parameter a b q hq).D w.stateArity x u| ≤ C)
    (v : Fin n → E × PolarPoint) (hv : ∀ i, allowed (v i).1)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    |J.D n (x, q) v| ≤ C * 2 ^ w.angleArity := by
  rw [J.unique (n04Realization_mixedJointDirections RF hU hcU hI hcI hb)
    n (x, q) ⟨hx, hq⟩]
  rw [n04Realization_mixedJointDirections_expansion RF hU hcU hI hcI hb n x q hq]
  apply n04PulledFields_doubleExpansion_pureSlots_bound allowed w
    (fun a b k => ((RF.parameter a b q hq).D k x).toMultilinearMap) hC hraw
    (fun i => (((v i).1, (v i).2.1), (v i).2.2)) hv
    (fun i => ?_) (fun i => ?_) hstate hspatial
  · have hcoord : |(v i).2.1| ≤ ‖(v i).2‖ := by
      simpa only [Real.norm_eq_abs] using norm_fst_le (v i).2
    exact hcoord.trans (hphysical i)
  · have hcoord : |(v i).2.2| ≤ ‖(v i).2‖ := by
      simpa only [Real.norm_eq_abs] using norm_snd_le (v i).2
    exact hcoord.trans (hphysical i)

end ContinuousFlexibility.Analysis
