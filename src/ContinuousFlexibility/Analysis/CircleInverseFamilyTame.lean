module

public import ContinuousFlexibility.Analysis.CircleInverseModel
public import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Homogeneous tame bounds for the actual inverse composition family

The joint low-seminorm growth estimate is normalized only in the outer
field. This produces the frozen linear-family bound with one high factor
and a loss chosen before the output order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

theorem linearMap_oneHigh_bound_of_unitBall
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (q : Seminorm ℝ F) (low high : Seminorm ℝ E)
    {C a : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ u, low u < 1 → q (L u) ≤ C * (a + high u)) (u : E) :
    q (L u) ≤ C * (a * low u + high u) := by
  let A : MultilinearMap ℝ (fun _ : Fin 1 => E) F :=
    MultilinearMap.ofSubsingleton ℝ E F (0 : Fin 1) L
  have hu (v : Fin 1 → E) (hv : ∀ i, low (v i) < 1) :
      q (A v) ≤ C * (a + ∑ i, high (v i)) := by
    simpa [A] using hlocal (v 0) (hv 0)
  have h := multilinearMap_bound_of_unitBall A q low high hC hu (fun _ : Fin 1 => u)
  simpa [A, multilinearTameSize] using h

private theorem seminorm_unit_growth_of_indexed_measure
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (U : Set E) (base loss : ℕ)
    (V : E → E → E) (q : ℕ → E → E → ℝ)
    (hgrading : ∀ e ∈ U, ∀ u s c, 0 ≤ c →
      (∀ j ≤ s, q j e u ≤ c) → p s (V e u) ≤ c)
    (hgrow : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : {z : E × E // z.1 ∈ U ∧ p base z.2 ≤ 1},
        q s i.val.1 i.val.2 ≤
          C * (1 + p (s + loss) i.val.1 + p (s + loss) i.val.2)) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ e ∈ U, ∀ u : E,
      p base u ≤ 1 → p s (V e u) ≤
        C * (1 + p (s + loss) e + p (s + loss) u) := by
  classical
  choose C hC hc using hgrow
  intro s
  let B : ℝ := ∑ j ∈ Finset.range (s + 1), C j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨B, hB, fun e he u hu => ?_⟩
  have hsize : 0 ≤ 1 + p (s + loss) e + p (s + loss) u :=
    add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _)
  apply hgrading e he u s _ (mul_nonneg hB hsize)
  intro j hj
  have hnorm := hc j ⟨(e, u), he, hu⟩
  have hCj : C j ≤ B := Finset.single_le_sum (f := C) (fun k _ => hC k)
    (Finset.mem_range.mpr (by omega))
  have hs : 1 + p (j + loss) e + p (j + loss) u ≤
      1 + p (s + loss) e + p (s + loss) u :=
    add_le_add (add_le_add le_rfl (hp (Nat.add_le_add_right hj loss) e))
      (hp (Nat.add_le_add_right hj loss) u)
  exact hnorm.trans ((mul_le_mul_of_nonneg_left hs (hC j)).trans
    (mul_le_mul_of_nonneg_right hCj hsize))

private theorem linearFamilyTame_of_unit_growth
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (U : Set E) (base loss : ℕ) (V : E → E →ₗ[ℝ] E)
    (hunit : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ e ∈ U, ∀ u : E,
      p base u ≤ 1 → p s (V e u) ≤
        C * (1 + p (s + loss) e + p (s + loss) u)) :
    Statements.LinearFamilyTame p p p U V := by
  refine ⟨loss, base, ?_⟩
  intro s hs
  obtain ⟨C, hC, hc⟩ := hunit s
  refine ⟨C, hC, fun e he u => ?_⟩
  have h := linearMap_oneHigh_bound_of_unitBall (V e)
    (p s) (p base) (p (s + loss)) hC (fun v hv => hc e he v hv.le) u
  simpa only [add_comm] using h

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circleInverseComposeLinear_unit_growth
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (base loss : ℕ) (hbase : loss + 2 ≤ base)
    (hinterp : ∀ b c : ℕ, base < b → b + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        S.grading b x ≤ C * (S.grading base x) ^ (((c : ℝ) - b - loss) / (c - base)) *
          (S.grading c x) ^ (((b : ℝ) - base + loss) / (c - base)))
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (U : Set S.Space)
    (K : ℝ) (hK : 0 ≤ K)
    (hUlow : ∀ e ∈ U, S.grading base e ≤ K)
    (hUpos : ∀ e ∈ U, ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ e ∈ U, ∀ u : S.Space,
      S.grading base u ≤ 1 →
      S.grading s (circleInverseComposeLinear hS hT hD hγ travel a ha e u) ≤
        C * (1 + S.grading (s + (base + loss + 2)) e +
          S.grading (s + (base + loss + 2)) u) := by
  let I := {z : S.Space × S.Space // z.1 ∈ U ∧ S.grading base z.2 ≤ 1}
  let e : I → S.Space := fun i => i.val.1
  let u : I → S.Space := fun i => i.val.2
  have he (i : I) : S.grading base (e i) ≤ max K 1 :=
    (hUlow i.val.1 i.property.1).trans (le_max_left _ _)
  have hu (i : I) : S.grading base (u i) ≤ max K 1 :=
    i.property.2.trans (le_max_right _ _)
  let upper := material_circle_power_upper (D := D) (T := T) (γ := γ) hT hD hγ
  let A : ℝ := upper.choose
  have hA : 0 ≤ A := upper.choose_spec.1
  have hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A := upper.choose_spec.2
  have hw := material_circle_sample_weights_pos hT hD
  have hgrow (s : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i : I,
      circleNorm T γ s (fun m => S.decode (u i) m ∘ circleAffineInverse travel (e i) m) ≤
        C * (1 + S.grading (s + (base + loss + 2)) (e i) +
          S.grading (s + (base + loss + 2)) (u i)) :=
    circleNorm_inverseCompose_family_growth (T := T) (γ := γ) (S := S)
      hS hw.1 hw.2 hA hHA base loss hbase
      hinterp (max K 1) (hK.trans (le_max_left _ _)) e u he hu travel
      (fun i => circleAffineInverse travel (e i)) ha
      (fun i => hUpos i.val.1 i.property.1)
      (fun i => circleAffineInverse_left travel (e i) ha (hUpos i.val.1 i.property.1))
      (fun i => circleAffineInverse_right hS hT hD hγ travel (e i)) s
  exact seminorm_unit_growth_of_indexed_measure S.grading
    (gradedSeminorm_monotone (fun j => S.level j) S.bond) U base (base + loss + 2)
    (fun e u => circleInverseComposeLinear hS hT hD hγ travel a ha e u)
    (fun s e u => circleNorm T γ s (fun m => S.decode u m ∘ circleAffineInverse travel e m))
    (fun e he u s c hc hb =>
      (circleGrading_le_iff_circleNorm hS s _ hc).mpr (fun j hj =>
        (congrArg (circleNorm T γ j)
          (circleInverseComposeLinear_decode (D := D) (T := T) (γ := γ) (S := S)
            hS hT hD hγ travel a ha e u (hUpos e he))).trans_le (hb j hj)))
    hgrow

theorem circleInverseComposeLinear_linearFamilyTame
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (base loss : ℕ) (hbase : loss + 2 ≤ base)
    (hinterp : ∀ b c : ℕ, base < b → b + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        S.grading b x ≤ C * (S.grading base x) ^ (((c : ℝ) - b - loss) / (c - base)) *
          (S.grading c x) ^ (((b : ℝ) - base + loss) / (c - base)))
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (U : Set S.Space)
    (K : ℝ) (hK : 0 ≤ K)
    (hUlow : ∀ e ∈ U, S.grading base e ≤ K)
    (hUpos : ∀ e ∈ U, ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) :
    LinearFamilyTame S.grading S.grading S.grading U
      (circleInverseComposeLinear hS hT hD hγ travel a ha) := by
  exact linearFamilyTame_of_unit_growth S.grading U base (base + loss + 2)
    (circleInverseComposeLinear hS hT hD hγ travel a ha)
    (circleInverseComposeLinear_unit_growth (D := D) (T := T) (γ := γ) (S := S)
      hS hT hD hγ base loss hbase hinterp travel a ha U K hK hUlow hUpos)

end ContinuousFlexibility.Statements
