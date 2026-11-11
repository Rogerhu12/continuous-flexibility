import ContinuousFlexibility.Analysis.JointJetSpatialRegularity
import ContinuousFlexibility.Analysis.WeightedJointComposition
import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# A fixed joint-order budget from the actual mixed parameter jets

Each direction is split into its parameter, radial and angular parts.
Fixing the last slot of the genuine tower identifies the two spatial
parts with the actual mixed derivatives. At joint order `r` only mixed
orders whose sum with the parameter arity is at most `r` occur. The
resulting constant is independent of the spatial point and of any
additional component label. Spatial coordinates of the base point do
not enter the grading.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}

private theorem jointJet_unit_bound_aux
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (low high : Seminorm ℝ E) (x : E) (hx : x ∈ U)
    (p : PolarPoint) (hp : p ∈ V) :
    ∀ r : ℕ, ∀ f : E × PolarPoint → ℝ,
    ∀ J : SmoothDirections (U ×ˢ V) f, ∀ C H : ℝ,
      0 ≤ C → 0 ≤ H →
      (∀ k a b : ℕ, k + a + b ≤ r → ∀ u : Fin k → E,
        (∀ i, low (u i) ≤ 1) →
        |mixedDerivative a b (fun q => J.D k (x, q) (fun i => (u i, 0))) p| ≤
          C * (H + ∑ i : Fin k, high (u i))) →
      ∀ v : Fin r → E × PolarPoint,
        (∀ i, low (v i).1 ≤ 1 ∧ |(v i).2.1| ≤ 1 ∧ |(v i).2.2| ≤ 1) →
        |J.D r (x, p) v| ≤
          (3 : ℝ) ^ r * C * (H + ∑ i : Fin r, high (v i).1) := by
  intro r
  induction r with
  | zero =>
      intro f J C H hC hH hb v hv
      have h := hb 0 0 0 (by omega) Fin.elim0 (fun i => Fin.elim0 i)
      have he : v = fun i : Fin 0 => ((Fin.elim0 i : E), (0 : PolarPoint)) :=
        Subsingleton.elim _ _
      simpa only [he, mixedDerivative, iteratedDeriv_zero, pow_zero, one_mul,
        Fin.sum_univ_zero, add_zero] using h
  | succ r ih =>
      intro f J C H hC hH hb v hv
      let tail : Fin r → E × PolarPoint := Fin.tail v
      let w : E := (v 0).1
      let er : E × PolarPoint := (0, (1, 0))
      let ea : E × PolarPoint := (0, (0, 1))
      have htail (i : Fin r) :
          low (tail i).1 ≤ 1 ∧ |(tail i).2.1| ≤ 1 ∧ |(tail i).2.2| ≤ 1 :=
        hv i.succ
      have hparam (k a b : ℕ) (horder : k + a + b ≤ r)
          (u : Fin k → E) (hu : ∀ i, low (u i) ≤ 1) :
          |mixedDerivative a b
            (fun q => (J.fixedLast (w, 0)).D k (x, q) (fun i => (u i, 0))) p| ≤
            C * ((H + high w) + ∑ i : Fin k, high (u i)) := by
        have hslots : Fin.snoc (fun i : Fin k => (u i, (0 : PolarPoint))) (w, 0) =
            fun i : Fin (k + 1) => (Fin.snoc u w i, (0 : PolarPoint)) := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp only [Fin.snoc_last]
          · simp only [Fin.snoc_castSucc]
        have heq : (fun q => (J.fixedLast (w, 0)).D k (x, q)
            (fun i => (u i, (0 : PolarPoint)))) =
            fun q => J.D (k + 1) (x, q)
              (fun i => (Fin.snoc u w i, (0 : PolarPoint))) := by
          funext q
          rw [J.fixedLast_apply, hslots]
        rw [heq]
        have hus (i : Fin (k + 1)) : low (Fin.snoc u w i) ≤ 1 := by
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa only [Fin.snoc_last] using (hv 0).1
          · simpa only [Fin.snoc_castSucc] using hu j
        have hs : (∑ i : Fin (k + 1), high (Fin.snoc u w i)) =
            (∑ i : Fin k, high (u i)) + high w := by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact (hb (k + 1) a b (by omega) (Fin.snoc u w) hus).trans_eq
          (by rw [hs]; ring)
      have hrad (k a b : ℕ) (horder : k + a + b ≤ r)
          (u : Fin k → E) (hu : ∀ i, low (u i) ≤ 1) :
          |mixedDerivative a b
            (fun q => (J.fixedLast er).D k (x, q) (fun i => (u i, 0))) p| ≤
            C * (H + ∑ i : Fin k, high (u i)) := by
        rw [← J.jointJet_mixed_radial_step hV hc a b k x hx
          (fun i => (u i, 0)) hp]
        exact hb k (a + 1) b (by omega) u hu
      have hang (k a b : ℕ) (horder : k + a + b ≤ r)
          (u : Fin k → E) (hu : ∀ i, low (u i) ≤ 1) :
          |mixedDerivative a b
            (fun q => (J.fixedLast ea).D k (x, q) (fun i => (u i, 0))) p| ≤
            C * (H + ∑ i : Fin k, high (u i)) := by
        rw [← J.jointJet_mixed_angular_step hV hc a b k x hx
          (fun i => (u i, 0)) hp]
        exact hb k a (b + 1) (by omega) u hu
      let K : ℝ := (3 : ℝ) ^ r * C
      let Z : ℝ := H + ∑ i : Fin (r + 1), high (v i).1
      have hK : 0 ≤ K := mul_nonneg (pow_nonneg (by norm_num) r) hC
      have hZ : 0 ≤ Z := add_nonneg hH (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))
      have hparamBound : |(J.fixedLast (w, 0)).D r (x, p) tail| ≤ K * Z := by
        have ht := ih _ (J.fixedLast (w, 0)) C (H + high w) hC
          (add_nonneg hH (apply_nonneg _ _)) hparam tail htail
        simpa only [K, Z, w, tail, Fin.sum_univ_succ, Fin.tail, add_assoc] using ht
      have hrest : H + (∑ i : Fin r, high (tail i).1) ≤ Z := by
        dsimp only [Z]
        rw [Fin.sum_univ_succ]
        have hh := apply_nonneg high w
        dsimp only [tail, Fin.tail, w] at *
        linarith only [hh]
      have hradBound : |(J.fixedLast er).D r (x, p) tail| ≤ K * Z :=
        (ih _ (J.fixedLast er) C H hC hH hrad tail htail).trans
          (mul_le_mul_of_nonneg_left hrest hK)
      have hangBound : |(J.fixedLast ea).D r (x, p) tail| ≤ K * Z :=
        (ih _ (J.fixedLast ea) C H hC hH hang tail htail).trans
          (mul_le_mul_of_nonneg_left hrest hK)
      have hrTerm : |(v 0).2.1 * (J.fixedLast er).D r (x, p) tail| ≤ K * Z := by
        rw [abs_mul]
        exact (mul_le_mul (hv 0).2.1 hradBound (abs_nonneg _) zero_le_one).trans_eq
          (one_mul _)
      have haTerm : |(v 0).2.2 * (J.fixedLast ea).D r (x, p) tail| ≤ K * Z := by
        rw [abs_mul]
        exact (mul_le_mul (hv 0).2.2 hangBound (abs_nonneg _) zero_le_one).trans_eq
          (one_mul _)
      let L := projectiveJetHeadLinear J.D r (x, p) tail
      have hL (u : E × PolarPoint) : L u = (J.fixedLast u).D r (x, p) tail :=
        (projectiveJetHeadLinear_apply J.D r (x, p) tail u).trans
          (J.fixedLast_eq_cons hc u r (x, p) ⟨hx, hp⟩ tail).symm
      have hsplit : J.D (r + 1) (x, p) v =
          (J.fixedLast (w, 0)).D r (x, p) tail +
            (v 0).2.1 * (J.fixedLast er).D r (x, p) tail +
            (v 0).2.2 * (J.fixedLast ea).D r (x, p) tail := by
        have hdir : v 0 = (w, (0 : PolarPoint)) + (v 0).2.1 • er + (v 0).2.2 • ea := by
          ext <;> simp only [w, er, ea, Prod.fst_add, Prod.snd_add,
            Prod.fst_smul, Prod.snd_smul, Prod.fst_zero, Prod.snd_zero,
            smul_zero, zero_add, add_zero, smul_eq_mul, mul_one, mul_zero]
        calc
          _ = L (v 0) := by
            dsimp only [L]
            rw [projectiveJetHeadLinear_apply]
            exact congrArg (J.D (r + 1) (x, p)) (Fin.cons_self_tail v).symm
          _ = L ((w, (0 : PolarPoint)) + (v 0).2.1 • er + (v 0).2.2 • ea) :=
            congrArg L hdir
          _ = _ := by
            rw [map_add, map_add, map_smul, map_smul, hL, hL, hL]
            simp only [smul_eq_mul]
      rw [hsplit]
      calc
        _ ≤ (|(J.fixedLast (w, 0)).D r (x, p) tail| +
              |(v 0).2.1 * (J.fixedLast er).D r (x, p) tail|) +
            |(v 0).2.2 * (J.fixedLast ea).D r (x, p) tail| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ K * Z + K * Z + K * Z := add_le_add (add_le_add hparamBound hrTerm) haTerm
        _ = _ := by dsimp only [K, Z]; rw [pow_succ]; ring

/-- Mixed pure-parameter bounds up to one total order control the actual
joint jet. The factor `3^r` counts the three genuine directional pieces. -/
theorem SmoothDirections.jointJet_unit_bound_of_mixed_parameter_bounds
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (low high : Seminorm ℝ E) (r : ℕ) (x : E) (hx : x ∈ U)
    (p : PolarPoint) (hp : p ∈ V) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hbound : ∀ k a b : ℕ, k + a + b ≤ r → ∀ u : Fin k → E,
      (∀ i, low (u i) ≤ 1) →
      |mixedDerivative a b (fun q => J.D k (x, q) (fun i => (u i, 0))) p| ≤
        C * (H + ∑ i : Fin k, high (u i)))
    (v : Fin r → E × PolarPoint)
    (hv : ∀ i, low (v i).1 ≤ 1 ∧ |(v i).2.1| ≤ 1 ∧ |(v i).2.2| ≤ 1) :
    |J.D r (x, p) v| ≤ (3 : ℝ) ^ r * C * (H + ∑ i : Fin r, high (v i).1) :=
  jointJet_unit_bound_aux hV hc low high x hx p hp r f J C H hC hH hbound v hv

/-- The mixed-to-joint adapter preserves the same fixed loss. Its
component exponent is zero, and its constants are uniform in labels. -/
theorem uniformWeightedJointGrowth_of_mixed_parameter_oneHigh
    {ι : Type*} {V : ι → Set PolarPoint} {f : ι → E × PolarPoint → ℝ}
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (f i))
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (W : ι → ℝ)
    (base loss B : ℕ) (hB : base ≤ B)
    (hbound : ∀ R : ℝ, 0 ≤ R → ∀ n s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i x, x ∈ U → p base x ≤ R → ∀ y ∈ V i, ∀ v : Fin n → E,
      ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (fun q => (J i).D n (x, q) (fun j => (v j, 0))) y| ≤
          C * oneHighVariationWeight p base (s + loss) x v) :
    UniformWeightedJointGrowth p W J B loss := by
  classical
  intro R hR r
  choose C hC hCb using fun n : Fin (r + 1) => hbound R hR n r
  let A : ℝ := ∑ n : Fin (r + 1), C n
  have hA : 0 ≤ A := Finset.sum_nonneg (fun n _ => hC n)
  refine ⟨(3 : ℝ) ^ r * A, 0, mul_nonneg (pow_nonneg (by norm_num) r) hA,
    le_rfl, fun i x hx hlow y hy v hv => ?_⟩
  have hinput (k a b : ℕ) (horder : k + a + b ≤ r)
      (u : Fin k → E) (hu : ∀ j, p base (u j) ≤ 1) :
      |mixedDerivative a b (fun q => (J i).D k (x, q) (fun j => (u j, 0))) y| ≤
        A * ((1 + p (r + loss) x) + ∑ j : Fin k, p (r + loss) (u j)) := by
    let ik : Fin (r + 1) := ⟨k, by omega⟩
    have hCA : C ik ≤ A := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ ik)
    have hw : oneHighVariationWeight p base (r + loss) x u ≤
        (1 + p (r + loss) x) + ∑ j : Fin k, p (r + loss) (u j) :=
      multilinearTameSize_le_affine (p base) (p (r + loss)) k
        (add_nonneg zero_le_one (apply_nonneg _ _)) u hu
    have hg : 0 ≤ (1 + p (r + loss) x) + ∑ j : Fin k, p (r + loss) (u j) := by
      positivity
    exact (hCb ik i x hx ((hp hB x).trans hlow) y hy u a b (by omega)).trans
      ((mul_le_mul_of_nonneg_left hw (hC ik)).trans
        (mul_le_mul_of_nonneg_right hCA hg))
  have hunit (j : Fin r) :
      p base (v j).1 ≤ 1 ∧ |(v j).2.1| ≤ 1 ∧ |(v j).2.2| ≤ 1 := by
    have hl : p B (v j).1 ≤ 1 :=
      (le_add_of_nonneg_right (norm_nonneg (v j).2)).trans (hv j)
    have hs : ‖(v j).2‖ ≤ 1 :=
      (le_add_of_nonneg_left (apply_nonneg (p B) (v j).1)).trans (hv j)
    refine ⟨(hp hB (v j).1).trans hl, ?_, ?_⟩
    · exact (by simpa only [Real.norm_eq_abs] using norm_fst_le (v j).2).trans hs
    · exact (by simpa only [Real.norm_eq_abs] using norm_snd_le (v j).2).trans hs
  have h := (J i).jointJet_unit_bound_of_mixed_parameter_bounds (hV i) (hc i)
    (p base) (p (r + loss)) r x hx y hy hA
    (add_nonneg zero_le_one (apply_nonneg _ _)) hinput v hunit
  simpa only [Real.norm_eq_abs, Real.rpow_zero, mul_one] using h

end ContinuousFlexibility.Analysis
