import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
import ContinuousFlexibility.Analysis.N04RealizationMixedSlotBudget
import ContinuousFlexibility.Analysis.N01cStateAngleGraphBudget
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Exact parameter and spatial arities in a genuine joint tower

A pure parameter slot is retained as a parameter slot. A pure physical
slot splits into its radial and angular components. Consequently the
mixed-to-joint estimate uses exactly the original parameter arity and
spatial arity, with only a factor `2^spatialArity`.

The arbitrary two-index majorant can carry both the sampled height and
the saved spatial degree required in implicit inverse estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}

theorem StateAngleWord.negativeInverse_selectedProduct_eq_prod {n : ℕ}
    (w : StateAngleWord n) (a : Fin n → ℝ) :
    w.selectedProduct a = ∏ i, if w.isState i then 1 else a i := by
  induction w with
  | nil => simp only [selectedProduct, Fin.prod_univ_zero]
  | state w ih =>
      simpa only [selectedProduct, isState, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, if_true, one_mul, Fin.tail] using ih (Fin.tail a)
  | angle w ih =>
      simpa only [selectedProduct, isState, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, if_false, Fin.tail] using
        congrArg (fun t : ℝ => a 0 * t) (ih (Fin.tail a))

/-- Normalize only the physical slots. The parameter directions remain
unchanged, and a zero physical vector is handled without division assumptions. -/
theorem n04NegativeInverse_pureSpatial_homogeneous
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (w : StateAngleWord n) (A : (E × PolarPoint) [×n]→L[ℝ] F)
    (u : Fin n → E) {C : ℝ}
    (hunit : ∀ y : Fin n → PolarPoint, (∀ i, ‖y i‖ ≤ 1) →
      ‖A (fun i => if w.isState i then (u i, 0) else (0, y i))‖ ≤ C)
    (y : Fin n → PolarPoint) :
    ‖A (fun i => if w.isState i then (u i, 0) else (0, y i))‖ ≤
      C * w.selectedProduct (fun i => ‖y i‖) := by
  classical
  let v : Fin n → PolarPoint := fun i => ‖y i‖⁻¹ • y i
  let c : Fin n → ℝ := fun i => if w.isState i then 1 else ‖y i‖
  have hv (i : Fin n) : ‖v i‖ ≤ 1 := by
    by_cases hy : y i = 0
    · simp only [v, hy, norm_zero, inv_zero, zero_smul, zero_le_one]
    · exact (norm_smul_inv_norm (𝕜 := ℝ) hy).le
  have hc (i : Fin n) : 0 ≤ c i := by
    dsimp only [c]
    split <;> positivity
  have heq : (fun i => if w.isState i then (u i, (0 : PolarPoint)) else (0, y i)) =
      fun i => c i • (if w.isState i then (u i, (0 : PolarPoint)) else (0, v i)) := by
    funext i
    cases hi : w.isState i with
    | true => simp only [c, hi, if_true, one_smul]
    | false =>
        simp only [c, hi, Bool.false_eq_true, if_false]
        apply Prod.ext
        · change (0 : E) = ‖y i‖ • (0 : E)
          exact (smul_zero _).symm
        · change y i = ‖y i‖ • (‖y i‖⁻¹ • y i)
          by_cases hy : y i = 0
          · simp only [hy, norm_zero, inv_zero, zero_smul]
          · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]
  calc
    _ = (∏ i, c i) * ‖A (fun i => if w.isState i then (u i, 0) else (0, v i))‖ := by
      rw [heq, A.map_smul_univ, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg (fun i _ => hc i))]
    _ ≤ (∏ i, c i) * C := mul_le_mul_of_nonneg_left (hunit v hv)
      (Finset.prod_nonneg (fun i _ => hc i))
    _ = C * w.selectedProduct (fun i => ‖y i‖) := by
      rw [w.negativeInverse_selectedProduct_eq_prod]
      exact mul_comm _ _

/-- Pure tagged slots preserve both arities when mixed jets are joined. -/
theorem n04NegativeInverse_pureJoint_of_mixed
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (low high : Seminorm ℝ E) (R : ℝ)
    (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V)
    {n : ℕ} (w : StateAngleWord n)
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (B : ℕ → ℕ → ℝ) (hB : ∀ k s, 0 ≤ B k s)
    (hb : ∀ k a b : ℕ, k ≤ w.stateArity → a + b ≤ w.angleArity →
      ∀ u : Fin k → E, (∀ i, low (u i) ≤ 1) → (∀ i, high (u i) ≤ R) →
        |mixedDerivative a b (fun p => J.D k (x, p) (fun i => (u i, 0))) q| ≤
          B k (a + b))
    (v : Fin n → E × PolarPoint)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    |J.D n (x, q) v| ≤ (2 : ℝ) ^ w.angleArity * B w.stateArity w.angleArity := by
  induction w generalizing f B with
  | nil =>
      have he : v = fun i : Fin 0 => ((Fin.elim0 i : E), (0 : PolarPoint)) :=
        Subsingleton.elim _ _
      simpa only [he, StateAngleWord.stateArity, StateAngleWord.angleArity,
        mixedDerivative, iteratedDeriv_zero, pow_zero, one_mul, Nat.zero_add] using
        hb 0 0 0 le_rfl le_rfl Fin.elim0 (fun i => Fin.elim0 i)
          (fun i => Fin.elim0 i)
  | @state n w ih =>
      let tail : Fin n → E × PolarPoint := Fin.tail v
      let z : E := (v 0).1
      have hz : (v 0).2 = 0 := hspatial 0 rfl
      have htailState (i : Fin n) (hi : w.isState i = false) : (tail i).1 = 0 :=
        hstate i.succ (by simpa only [StateAngleWord.isState, Fin.cons_succ] using hi)
      have htailSpatial (i : Fin n) (hi : w.isState i = true) : (tail i).2 = 0 :=
        hspatial i.succ (by simpa only [StateAngleWord.isState, Fin.cons_succ] using hi)
      have hbound (k a b : ℕ) (hk : k ≤ w.stateArity) (hab : a + b ≤ w.angleArity)
          (u : Fin k → E) (hu : ∀ i, low (u i) ≤ 1) (huh : ∀ i, high (u i) ≤ R) :
          |mixedDerivative a b
            (fun p => (J.fixedLast (z, 0)).D k (x, p) (fun i => (u i, 0))) q| ≤
              B (k + 1) (a + b) := by
        have hslots : Fin.snoc (α := fun _ : Fin (k + 1) => E × PolarPoint)
            (fun i : Fin k => (u i, (0 : PolarPoint))) (z, 0) =
            fun i : Fin (k + 1) =>
              (Fin.snoc (α := fun _ : Fin (k + 1) => E) u z i, (0 : PolarPoint)) := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp only [Fin.snoc_last]
          · simp only [Fin.snoc_castSucc]
        have heq : (fun p => (J.fixedLast (z, 0)).D k (x, p)
            (fun i => (u i, (0 : PolarPoint)))) =
            fun p => J.D (k + 1) (x, p)
              (fun i => (Fin.snoc (α := fun _ : Fin (k + 1) => E) u z i,
                (0 : PolarPoint))) := by
          funext p
          rw [J.fixedLast_apply, hslots]
        rw [heq]
        have hk' : k + 1 ≤ w.state.stateArity := by
          simpa only [StateAngleWord.stateArity] using (Nat.add_le_add_right hk 1)
        apply hb (k + 1) a b hk' hab
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa only [Fin.snoc_last, z] using hlow 0
          · simpa only [Fin.snoc_castSucc] using hu j
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa only [Fin.snoc_last, z] using hhigh 0
          · simpa only [Fin.snoc_castSucc] using huh j
      have h := ih (J := J.fixedLast (z, 0)) (B := fun k s => B (k + 1) s)
        (fun k s => hB (k + 1) s) hbound tail
        (fun i => hlow i.succ) (fun i => hhigh i.succ) (fun i => hphysical i.succ)
        htailState htailSpatial
      have heq : J.D (n + 1) (x, q) v = (J.fixedLast (z, 0)).D n (x, q) tail := by
        rw [J.fixedLast_eq_cons hc _ n (x, q) ⟨hx, hq⟩ tail]
        apply congrArg (J.D (n + 1) (x, q))
        have hh : (z, (0 : PolarPoint)) = v 0 := by
          apply Prod.ext
          · rfl
          · exact hz.symm
        rw [hh]
        exact (Fin.cons_self_tail v).symm
      rw [heq]
      exact h
  | @angle n w ih =>
      let tail : Fin n → E × PolarPoint := Fin.tail v
      let er : E × PolarPoint := (0, (1, 0))
      let ea : E × PolarPoint := (0, (0, 1))
      have hz : (v 0).1 = 0 := hstate 0 rfl
      have htailState (i : Fin n) (hi : w.isState i = false) : (tail i).1 = 0 :=
        hstate i.succ (by simpa only [StateAngleWord.isState, Fin.cons_succ] using hi)
      have htailSpatial (i : Fin n) (hi : w.isState i = true) : (tail i).2 = 0 :=
        hspatial i.succ (by simpa only [StateAngleWord.isState, Fin.cons_succ] using hi)
      have hrad (k a b : ℕ) (hk : k ≤ w.stateArity) (hab : a + b ≤ w.angleArity)
          (u : Fin k → E) (hu : ∀ i, low (u i) ≤ 1) (huh : ∀ i, high (u i) ≤ R) :
          |mixedDerivative a b
            (fun p => (J.fixedLast er).D k (x, p) (fun i => (u i, 0))) q| ≤
              B k (a + b + 1) := by
        rw [← J.jointJet_mixed_radial_step hV hc a b k x hx
          (fun i => (u i, 0)) hq]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hb k (a + 1) b hk (by change a + 1 + b ≤ w.angleArity + 1; omega) u hu huh
      have hang (k a b : ℕ) (hk : k ≤ w.stateArity) (hab : a + b ≤ w.angleArity)
          (u : Fin k → E) (hu : ∀ i, low (u i) ≤ 1) (huh : ∀ i, high (u i) ≤ R) :
          |mixedDerivative a b
            (fun p => (J.fixedLast ea).D k (x, p) (fun i => (u i, 0))) q| ≤
              B k (a + b + 1) := by
        rw [← J.jointJet_mixed_angular_step hV hc a b k x hx
          (fun i => (u i, 0)) hq]
        simpa only [Nat.add_assoc] using
          hb k a (b + 1) hk (by change a + (b + 1) ≤ w.angleArity + 1; omega) u hu huh
      have hr := ih (J := J.fixedLast er) (B := fun k s => B k (s + 1))
        (fun k s => hB k (s + 1)) hrad tail
        (fun i => hlow i.succ) (fun i => hhigh i.succ) (fun i => hphysical i.succ)
        htailState htailSpatial
      have ha := ih (J := J.fixedLast ea) (B := fun k s => B k (s + 1))
        (fun k s => hB k (s + 1)) hang tail
        (fun i => hlow i.succ) (fun i => hhigh i.succ) (fun i => hphysical i.succ)
        htailState htailSpatial
      let M : ℝ := (2 : ℝ) ^ w.angleArity * B w.stateArity (w.angleArity + 1)
      have hrunit : |(v 0).2.1| ≤ 1 :=
        (show |(v 0).2.1| ≤ ‖(v 0).2‖ from by
          simpa only [Real.norm_eq_abs] using norm_fst_le (v 0).2).trans (hphysical 0)
      have haunit : |(v 0).2.2| ≤ 1 :=
        (show |(v 0).2.2| ≤ ‖(v 0).2‖ from by
          simpa only [Real.norm_eq_abs] using norm_snd_le (v 0).2).trans (hphysical 0)
      have hrt : |(v 0).2.1 * (J.fixedLast er).D n (x, q) tail| ≤ M := by
        rw [abs_mul]
        exact (mul_le_mul hrunit hr (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      have hat : |(v 0).2.2 * (J.fixedLast ea).D n (x, q) tail| ≤ M := by
        rw [abs_mul]
        exact (mul_le_mul haunit ha (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      let L := projectiveJetHeadLinear J.D n (x, q) tail
      have hL (u : E × PolarPoint) : L u = (J.fixedLast u).D n (x, q) tail :=
        (projectiveJetHeadLinear_apply J.D n (x, q) tail u).trans
          (J.fixedLast_eq_cons hc u n (x, q) ⟨hx, hq⟩ tail).symm
      have hsplit : J.D (n + 1) (x, q) v =
          (v 0).2.1 * (J.fixedLast er).D n (x, q) tail +
            (v 0).2.2 * (J.fixedLast ea).D n (x, q) tail := by
        have hdir : v 0 = (v 0).2.1 • er + (v 0).2.2 • ea := by
          apply Prod.ext
          · change (v 0).1 = (v 0).2.1 • (0 : E) + (v 0).2.2 • (0 : E)
            simpa only [smul_zero, add_zero] using hz
          · apply Prod.ext
            · change (v 0).2.1 = (v 0).2.1 * 1 + (v 0).2.2 * 0
              rw [mul_one, mul_zero, add_zero]
            · change (v 0).2.2 = (v 0).2.1 * 0 + (v 0).2.2 * 1
              rw [mul_zero, mul_one, zero_add]
        calc
          _ = L (v 0) := by
            dsimp only [L]
            rw [projectiveJetHeadLinear_apply]
            exact congrArg (J.D (n + 1) (x, q)) (Fin.cons_self_tail v).symm
          _ = L ((v 0).2.1 • er + (v 0).2.2 • ea) := congrArg L hdir
          _ = _ := by
            rw [map_add, map_smul, map_smul, hL, hL]
            simp only [smul_eq_mul]
      rw [hsplit]
      exact ((abs_add_le _ _).trans (add_le_add hrt hat)).trans_eq (by
        dsimp only [M, StateAngleWord.stateArity, StateAngleWord.angleArity]
        rw [pow_succ]
        ring)

/-- Any genuine mixed parameter towers may supply the two-index
majorant; uniqueness identifies them with the given genuine joint tower. -/
theorem n04NegativeInverse_pureJoint_of_parameterTowers
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (low high : Seminorm ℝ E) (R : ℝ)
    (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ V)
    {n : ℕ} (w : StateAngleWord n)
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (B : ℕ → ℕ → ℝ) (hB : ∀ k s, 0 ≤ B k s)
    (hb : ∀ k a b : ℕ, k ≤ w.stateArity → a + b ≤ w.angleArity →
      ∀ Q : SmoothDirections U (fun z => mixedDerivative a b (fun p => f (z, p)) q),
      ∀ u : Fin k → E, (∀ i, low (u i) ≤ 1) → (∀ i, high (u i) ≤ R) →
        |Q.D k x u| ≤ B k (a + b))
    (v : Fin n → E × PolarPoint)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    |J.D n (x, q) v| ≤ (2 : ℝ) ^ w.angleArity * B w.stateArity w.angleArity := by
  apply n04NegativeInverse_pureJoint_of_mixed hV hc low high R x hx q hq w J B hB
    (v := v) (hlow := hlow) (hhigh := hhigh) (hphysical := hphysical)
    (hstate := hstate) (hspatial := hspatial)
  intro k a b hk hab u hu huh
  let Q := (n04Realization_jointMixedRegularity J hU hV hc).parameter a b q hq
  rw [← n04Realization_mixedParameter_eq_joint J hU hV hc a b k x hx q hq Q u]
  exact hb k a b hk hab Q u hu huh

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeInverse_pureJoint_of_parameterTowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeInverse_pureJoint_of_parameterTowers
