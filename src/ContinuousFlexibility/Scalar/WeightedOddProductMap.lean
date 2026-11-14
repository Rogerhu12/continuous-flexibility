module

public import ContinuousFlexibility.Scalar.WeightedOddProductPrimitive
public import ContinuousFlexibility.Scalar.WeightedDecodedProductMap

/-!
# The continuous bilinear primitive encoding of odd products

This map represents the literal integral of f times the angular derivative
of g. Algebraic linearity is proved on the globally smooth decoded fields.
The actual physical one-high-factor estimate supplies continuity in the
prescribed projective topology and is retained after lifting.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

theorem scalarOddProductPrimitive_add_left {f₀ f₁ g : PolarPoint → ℝ}
    (h₀ : ContDiff ℝ ∞ f₀) (h₁ : ContDiff ℝ ∞ f₁) (hg : ContDiff ℝ ∞ g) :
    scalarOddProductPrimitive (fun p => f₀ p + f₁ p) g =
      fun p => scalarOddProductPrimitive f₀ g p + scalarOddProductPrimitive f₁ g p := by
  have he : scalarAngularProduct (fun p => f₀ p + f₁ p) g =
      fun p => scalarAngularProduct f₀ g p + scalarAngularProduct f₁ g p := by
    funext p
    simp only [scalarAngularProduct]
    ring
  unfold scalarOddProductPrimitive
  rw [he]
  exact scalarAngularPrimitive_add (scalarAngularProduct_contDiff h₀ hg).continuous
    (scalarAngularProduct_contDiff h₁ hg).continuous

theorem scalarOddProductPrimitive_const_mul_left (c : ℝ) (f g : PolarPoint → ℝ) :
    scalarOddProductPrimitive (fun p => c * f p) g =
      fun p => c * scalarOddProductPrimitive f g p := by
  have he : scalarAngularProduct (fun p => c * f p) g =
      fun p => c * scalarAngularProduct f g p := by
    funext p
    simp only [scalarAngularProduct]
    ring
  unfold scalarOddProductPrimitive
  rw [he, scalarAngularPrimitive_const_mul]

theorem scalarOddProductPrimitive_add_right {f g₀ g₁ : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (h₀ : ContDiff ℝ ∞ g₀) (h₁ : ContDiff ℝ ∞ g₁) :
    scalarOddProductPrimitive f (fun p => g₀ p + g₁ p) =
      fun p => scalarOddProductPrimitive f g₀ p + scalarOddProductPrimitive f g₁ p := by
  have hd : angularPartial (fun p => g₀ p + g₁ p) =
      fun p => angularPartial g₀ p + angularPartial g₁ p :=
    funext fun p => angularPartial_add
      (h₀.differentiable (by simp) p) (h₁.differentiable (by simp) p)
  have he : scalarAngularProduct f (fun p => g₀ p + g₁ p) =
      fun p => scalarAngularProduct f g₀ p + scalarAngularProduct f g₁ p := by
    funext p
    simp only [scalarAngularProduct, hd]
    ring
  unfold scalarOddProductPrimitive
  rw [he]
  exact scalarAngularPrimitive_add (scalarAngularProduct_contDiff hf h₀).continuous
    (scalarAngularProduct_contDiff hf h₁).continuous

theorem scalarOddProductPrimitive_const_mul_right
    (c : ℝ) (f : PolarPoint → ℝ) {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g) :
    scalarOddProductPrimitive f (fun p => c * g p) =
      fun p => c * scalarOddProductPrimitive f g p := by
  have hd : angularPartial (fun p => c * g p) = fun p => c * angularPartial g p := by
    funext p
    simpa only [angularPartial_const, zero_mul, zero_add] using
      angularPartial_mul (differentiableAt_const c) (hg.differentiable (by simp) p)
  have he : scalarAngularProduct f (fun p => c * g p) =
      fun p => c * scalarAngularProduct f g p := by
    funext p
    simp only [scalarAngularProduct, hd]
    ring
  unfold scalarOddProductPrimitive
  rw [he, scalarAngularPrimitive_const_mul]

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- The two arguments retain their order: only the second one is
differentiated before angular integration. -/
def oddProductPrimitiveFieldMultilinear
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (hγ : 0 < γ) :
    MultilinearMap ℝ (fun _ : Fin 2 => A.Space) (PolarPoint → ℝ) := by
  classical
  have hc (u : A.Space) : ContDiff ℝ ∞ (A.decode u) :=
    (heightMember_contDiff_and_flatJets hT hγ (hA.2.2.2.1 u)).1
  have hadd (x y : A.Space) :
      A.decode (x + y) = fun p => A.decode x p + A.decode y p := by
    funext p
    simp only [map_add, Pi.add_apply]
  have hsmul (c : ℝ) (x : A.Space) :
      A.decode (c • x) = fun p => c * A.decode x p := by
    funext p
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  refine MultilinearMap.mk'
    (fun u : Fin 2 → A.Space => scalarOddProductPrimitive (A.decode (u 0)) (A.decode (u 1)))
    ?_ ?_
  · intro u i x y
    fin_cases i
    · change scalarOddProductPrimitive (A.decode (x + y)) (A.decode (u 1)) =
        scalarOddProductPrimitive (A.decode x) (A.decode (u 1)) +
          scalarOddProductPrimitive (A.decode y) (A.decode (u 1))
      rw [hadd]
      funext p
      simpa only [Pi.add_apply] using
        congrFun (scalarOddProductPrimitive_add_left (hc x) (hc y) (hc (u 1))) p
    · change scalarOddProductPrimitive (A.decode (u 0)) (A.decode (x + y)) =
        scalarOddProductPrimitive (A.decode (u 0)) (A.decode x) +
          scalarOddProductPrimitive (A.decode (u 0)) (A.decode y)
      rw [hadd]
      funext p
      simpa only [Pi.add_apply] using
        congrFun (scalarOddProductPrimitive_add_right (hc (u 0)) (hc x) (hc y)) p
  · intro u i c x
    fin_cases i
    · change scalarOddProductPrimitive (A.decode (c • x)) (A.decode (u 1)) =
        c • scalarOddProductPrimitive (A.decode x) (A.decode (u 1))
      rw [hsmul]
      funext p
      simpa only [Pi.smul_apply, smul_eq_mul] using
        congrFun (scalarOddProductPrimitive_const_mul_left c (A.decode x) (A.decode (u 1))) p
    · change scalarOddProductPrimitive (A.decode (u 0)) (A.decode (c • x)) =
        c • scalarOddProductPrimitive (A.decode (u 0)) (A.decode x)
      rw [hsmul]
      funext p
      simpa only [Pi.smul_apply, smul_eq_mul] using
        congrFun (scalarOddProductPrimitive_const_mul_right c (A.decode (u 0)) (hc x)) p

theorem oddProductPrimitiveFieldMultilinear_apply
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (hγ : 0 < γ)
    (u : Fin 2 → A.Space) :
    oddProductPrimitiveFieldMultilinear hT hA hγ u =
      scalarOddProductPrimitive (A.decode (u 0)) (A.decode (u 1)) := rfl

private theorem oddProductPrimitiveField_heightMember
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) (u : Fin 2 → A.Space) :
    HeightMember D T γ (oddProductPrimitiveFieldMultilinear hT hA hγ u) :=
  scalarOddProductPrimitive_heightMember hT hA hinterp hγ u

private theorem oddProductPrimitiveField_productBound
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) :
    ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin 2 → A.Space,
      physicalNorm T γ s (oddProductPrimitiveFieldMultilinear hT hA hγ u) ≤
        C * ∏ i, A.grading t (u i) := by
  obtain ⟨base, loss, _, hbound⟩ :=
    scalarOddProductPrimitive_physicalNorm_oneHigh hT hA hinterp hγ
  intro s
  obtain ⟨C, hC, hCu⟩ := hbound s
  refine ⟨max base (s + loss), C * 2, mul_nonneg hC (by norm_num), ?_⟩
  intro u
  rw [oddProductPrimitiveFieldMultilinear_apply]
  have hsum :
      (∑ i, A.grading (s + loss) (u i) *
        ∏ j ∈ Finset.univ.erase i, A.grading base (u j)) ≤
      (Fintype.card (Fin 2) : ℝ) * ∏ i, A.grading (max base (s + loss)) (u i) :=
    oneHigh_le_card_product (p := A.grading)
      (gradedSeminorm_monotone (fun n => A.level n) A.bond) base (s + loss) u
  exact ((hCu u).trans (mul_le_mul_of_nonneg_left hsum hC)).trans_eq (by
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    ring)

/-- The actual continuous bilinear map with output decoded as the primitive
of the first field times the angular derivative of the second field. -/
def oddProductPrimitiveMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => A.Space) A.Space :=
  liftContinuousMultilinear hA (oddProductPrimitiveFieldMultilinear hT hA hγ)
    (oddProductPrimitiveField_heightMember hT hA hinterp hγ)
    (p := A.grading) (withSeminorms_graded (fun n => A.level n) A.bond)
    (oddProductPrimitiveField_productBound hT hA hinterp hγ)

theorem decode_oddProductPrimitiveMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) (u : Fin 2 → A.Space) :
    A.decode (oddProductPrimitiveMap hT hA hinterp hγ u) =
      scalarOddProductPrimitive (A.decode (u 0)) (A.decode (u 1)) :=
  (decode_liftContinuousMultilinear hA (oddProductPrimitiveFieldMultilinear hT hA hγ)
    (oddProductPrimitiveField_heightMember hT hA hinterp hγ)
    (p := A.grading) (withSeminorms_graded (fun n => A.level n) A.bond)
    (oddProductPrimitiveField_productBound hT hA hinterp hγ) u).trans
      (oddProductPrimitiveFieldMultilinear_apply hT hA hγ u)

theorem angularPartial_decode_oddProductPrimitiveMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) (u : Fin 2 → A.Space) :
    angularPartial (A.decode (oddProductPrimitiveMap hT hA hinterp hγ u)) =
      fun p => A.decode (u 0) p * angularPartial (A.decode (u 1)) p := by
  rw [decode_oddProductPrimitiveMap, scalarOddProductPrimitive]
  exact angularPartial_scalarAngularPrimitive
    (scalarAngularProduct_contDiff
      (heightMember_contDiff_and_flatJets hT hγ (hA.2.2.2.1 (u 0))).1
      (heightMember_contDiff_and_flatJets hT hγ (hA.2.2.2.1 (u 1))).1)

/-- The continuous lift retains the physical estimate with one high input
and one common base and loss for every output order. -/
theorem oddProductPrimitiveMap_oneHigh
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin 2 → A.Space,
        A.grading s (oddProductPrimitiveMap hT hA hinterp hγ u) ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  obtain ⟨base, loss, hbase, hbound⟩ :=
    scalarOddProductPrimitive_physicalNorm_oneHigh hT hA hinterp hγ
  refine ⟨base, loss, hbase, ?_⟩
  intro s
  obtain ⟨C, hC, hCu⟩ := hbound s
  refine ⟨C, hC, fun u => ?_⟩
  rw [sobolevGrading_eq_physicalNorm hA, decode_oddProductPrimitiveMap]
  exact hCu u

end SobolevModelData

end ContinuousFlexibility.Statements
