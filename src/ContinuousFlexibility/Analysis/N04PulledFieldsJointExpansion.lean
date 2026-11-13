import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
import ContinuousFlexibility.Analysis.N04RealizationDoubleExpansionHeight

/-!
# Exact mixed expansion of any genuine joint tower

Multilinearity splits each joint direction into its parameter, radial
and angular parts. The actual mixed derivatives identify these three
recursions with the double scalar expansion. No uniform bound on the
raw jets, or special construction of the supplied tower, is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}

private theorem n04PulledFields_jointHead_split
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (hc : Convex ℝ (U ×ˢ V)) (n : ℕ) (x : E) (hx : x ∈ U)
    (q : PolarPoint) (hq : q ∈ V) (v : Fin (n + 1) → E × PolarPoint) :
    J.D (n + 1) (x, q) v =
      (J.fixedLast ((v 0).1, 0)).D n (x, q) (Fin.tail v) +
      (v 0).2.1 * (J.fixedLast (0, (1, 0))).D n (x, q) (Fin.tail v) +
      (v 0).2.2 * (J.fixedLast (0, (0, 1))).D n (x, q) (Fin.tail v) := by
  let L := projectiveJetHeadLinear J.D n (x, q) (Fin.tail v)
  have hL (w : E × PolarPoint) :
      L w = (J.fixedLast w).D n (x, q) (Fin.tail v) :=
    (projectiveJetHeadLinear_apply J.D n (x, q) (Fin.tail v) w).trans
      (J.fixedLast_eq_cons hc w n (x, q) ⟨hx, hq⟩ (Fin.tail v)).symm
  have hdir : v 0 = ((v 0).1, (0 : PolarPoint)) +
      (v 0).2.1 • ((0, (1, 0)) : E × PolarPoint) +
      (v 0).2.2 • ((0, (0, 1)) : E × PolarPoint) := by
    apply Prod.ext
    · change (v 0).1 = (v 0).1 + (v 0).2.1 • (0 : E) + (v 0).2.2 • (0 : E)
      simp only [smul_zero, add_zero]
    · apply Prod.ext
      · change (v 0).2.1 = (0 : ℝ) + (v 0).2.1 * 1 + (v 0).2.2 * 0
        ring
      · change (v 0).2.2 = (0 : ℝ) + (v 0).2.1 * 0 + (v 0).2.2 * 1
        ring
  calc
    _ = L (v 0) := by
      dsimp only [L]
      rw [projectiveJetHeadLinear_apply]
      exact congrArg (J.D (n + 1) (x, q)) (Fin.cons_self_tail v).symm
    _ = L (((v 0).1, (0 : PolarPoint)) +
        (v 0).2.1 • ((0, (1, 0)) : E × PolarPoint) +
        (v 0).2.2 • ((0, (0, 1)) : E × PolarPoint)) := congrArg L hdir
    _ = _ := by
      rw [map_add, map_add, map_smul, map_smul, hL, hL, hL]
      simp only [smul_eq_mul]

private theorem n04PulledFields_jointExpansion_of_mixed
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V) :
    ∀ n : ℕ, ∀ {f : E × PolarPoint → ℝ}, ∀ J : SmoothDirections (U ×ˢ V) f,
      ∀ A : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ,
      (∀ a b j : ℕ, ∀ u : Fin j → E,
        A a b j u = mixedDerivative a b
          (fun p => J.D j (x, p) (fun i => (u i, 0))) q) →
      ∀ v : Fin n → E × PolarPoint,
        J.D n (x, q) v =
          scalarAngularExpansion n (fun b k => scalarAngularExpansion k
            (fun a j => A a b j))
            (fun i => (((v i).1, (v i).2.1), (v i).2.2)) := by
  intro n
  induction n with
  | zero =>
      intro f J A hA v
      simp only [scalarAngularExpansion_zero_apply]
      rw [hA]
      simpa only [mixedDerivative, iteratedDeriv_zero] using
        congrArg (J.D 0 (x, q))
          (show v = (fun i : Fin 0 => ((Fin.elim0 i : E), (0 : PolarPoint))) from
            Subsingleton.elim _ _)
  | succ n ih =>
      intro f J A hA v
      let AH : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
        fun a b j => scalarAngularHead (fun a j => A a b j)
          ((v 0).1, (v 0).2.1) a j
      let AR : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
        fun a b j => scalarAngularShift (fun a j => A a b j) a j
      let AT : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
        fun a b j => A a (b + 1) j
      have hAH (a b j : ℕ) (u : Fin j → E) :
          AH a b j u = mixedDerivative a b
            (fun p => (J.fixedLast ((v 0).1, 0)).D j (x, p)
              (fun i => (u i, 0))) q := by
        have hslots : (fun i : Fin (j + 1) =>
            (Fin.cons (α := fun _ : Fin (j + 1) => E) (v 0).1 u i, (0 : PolarPoint))) =
            Fin.cons (α := fun _ : Fin (j + 1) => E × PolarPoint)
              ((v 0).1, (0 : PolarPoint)) (fun i => (u i, (0 : PolarPoint))) := by
          funext i
          refine Fin.cases ?_ (fun k => ?_) i <;> rfl
        calc
          AH a b j u = A a b (j + 1)
              (Fin.cons (α := fun _ : Fin (j + 1) => E) (v 0).1 u) :=
            scalarAngularHead_apply _ _ _ _ _
          _ = mixedDerivative a b
              (fun p => J.D (j + 1) (x, p)
                (fun i => (Fin.cons (α := fun _ : Fin (j + 1) => E)
                  (v 0).1 u i, (0 : PolarPoint)))) q :=
            hA a b (j + 1) (Fin.cons (α := fun _ : Fin (j + 1) => E) (v 0).1 u)
          _ = _ := by
            refine mixedDerivative_congr_on_open hV ?_ a b hq
            intro p hp
            exact (congrArg (J.D (j + 1) (x, p)) hslots).trans
              (J.fixedLast_eq_cons hc ((v 0).1, 0) j (x, p) ⟨hx, hp⟩
                (fun i => (u i, 0))).symm
      have hAR (a b j : ℕ) (u : Fin j → E) :
          AR a b j u = mixedDerivative a b
            (fun p => (J.fixedLast (0, (1, 0))).D j (x, p)
              (fun i => (u i, 0))) q := by
        calc
          AR a b j u = A (a + 1) b j u := rfl
          _ = mixedDerivative (a + 1) b
              (fun p => J.D j (x, p) (fun i => (u i, 0))) q := hA (a + 1) b j u
          _ = _ := J.jointJet_mixed_radial_step hV hc a b j x hx (fun i => (u i, 0)) hq
      have hAT (a b j : ℕ) (u : Fin j → E) :
          AT a b j u = mixedDerivative a b
            (fun p => (J.fixedLast (0, (0, 1))).D j (x, p)
              (fun i => (u i, 0))) q := by
        calc
          AT a b j u = A a (b + 1) j u := rfl
          _ = mixedDerivative a (b + 1)
              (fun p => J.D j (x, p) (fun i => (u i, 0))) q := hA a (b + 1) j u
          _ = _ := J.jointJet_mixed_angular_step hV hc a b j x hx (fun i => (u i, 0)) hq
      rw [n04PulledFields_jointHead_split J hc n x hx q hq v,
        ih (J.fixedLast ((v 0).1, 0)) AH hAH,
        ih (J.fixedLast (0, (1, 0))) AR hAR,
        ih (J.fixedLast (0, (0, 1))) AT hAT,
        n04Realization_doubleAngularExpansion_succ_apply] <;> rfl

/-- Every genuine joint tower has the exact double expansion in any
genuine mixed parameter tower of the same field. The domain is unchanged
and no seminorm estimate is needed for this identity. -/
theorem n04PulledFields_jointDirections_mixedExpansion
    {f : E → PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ V) (fun z : E × PolarPoint => f z.1 z.2))
    (RF : MixedJetRegularity U V f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n : ℕ) (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V)
    (v : Fin n → E × PolarPoint) :
    J.D n (x, q) v =
      scalarAngularExpansion n (fun b k => scalarAngularExpansion k
        (fun a j => ((RF.parameter a b q hq).D j x).toMultilinearMap))
        (fun i => (((v i).1, (v i).2.1), (v i).2.2)) := by
  exact n04PulledFields_jointExpansion_of_mixed hV hc x hx q hq n J
    (fun a b j => ((RF.parameter a b q hq).D j x).toMultilinearMap)
    (fun a b j u => n04Realization_mixedParameter_eq_joint J hU hV hc
      a b j x hx q hq (RF.parameter a b q hq) u) v

end ContinuousFlexibility.Analysis
