module

public import ContinuousFlexibility.Analysis.CircleJetEncoding
public import ContinuousFlexibility.Analysis.CylinderTestPairing
public import ContinuousFlexibility.Analysis.ProjectiveLimitSubspace

/-!
# Parity projections on the actual circle spaces

Reflection preserves every weighted circle norm. Transporting this reflection
through any exact circle model gives continuous linear even and odd projections
with zero tame loss. The result uses the genuine decoded functions and the exact
norm identities in `IsCircleModel`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff ENNReal

/-- Reflection in a fundamental interval, which agrees with angular negation
on periodic functions. -/
def circleReflectFunctions (f : ℕ → ℝ → ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  f m (Real.pi - θ)

theorem circleReflectFunctions_eq_neg {T : MaterialData} {γ : ℝ}
    {f : ℕ → ℝ → ℝ} (hf : CircleMember T γ f) (m : ℕ) (θ : ℝ) :
    circleReflectFunctions f m θ = f m (-θ) :=
  (hf.1 m).2.sub_eq'

theorem circleReflectFunctions_involutive (f : ℕ → ℝ → ℝ) :
    circleReflectFunctions (circleReflectFunctions f) = f := by
  funext m θ
  simp only [circleReflectFunctions, sub_sub_cancel]

private theorem circle_reflection_jet_norm {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (b : ℕ) :
    eLpNorm (iteratedDeriv b (fun θ => f (Real.pi - θ))) 2 angleMeasure =
      eLpNorm (iteratedDeriv b f) 2 angleMeasure := by
  rw [iteratedDeriv_comp_const_sub]
  change eLpNorm (((-1 : ℝ) ^ b) •
    ((iteratedDeriv b f) ∘ (fun θ => Real.pi - θ))) 2 angleMeasure = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_pow, abs_neg, abs_one,
    one_pow, ENNReal.ofReal_one, one_mul]
  exact eLpNorm_comp_measurePreserving
    (memLp_angleMeasure_iteratedDeriv_of_contDiff hf b).aestronglyMeasurable
    measurePreserving_angleReflection

theorem circleMember_reflectFunctions {T : MaterialData} {γ : ℝ}
    {f : ℕ → ℝ → ℝ} (hf : CircleMember T γ f) :
    CircleMember T γ (circleReflectFunctions f) := by
  have hs (m : ℕ) : ContDiff ℝ ∞ (circleReflectFunctions f m) :=
    (hf.1 m).1.comp (contDiff_const.sub contDiff_id)
  have hn (m b : ℕ) :
      eLpNorm (iteratedDeriv b (circleReflectFunctions f m)) 2 angleMeasure =
        eLpNorm (iteratedDeriv b (f m)) 2 angleMeasure :=
    circle_reflection_jet_norm (hf.1 m).1 b
  refine ⟨fun m => ⟨hs m, ?_⟩,
    fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (hs m) b, ?_⟩
  · intro θ
    change f m (Real.pi - (θ + Real.pi)) = f m (Real.pi - θ)
    rw [sub_add_eq_sub_sub]
    exact (hf.1 m).2.sub_eq _
  · intro s
    simpa only [hn] using hf.2.2 s

theorem circleNorm_reflectFunctions {T : MaterialData} {γ : ℝ}
    {f : ℕ → ℝ → ℝ} (hf : CircleMember T γ f) (s : ℕ) :
    circleNorm T γ s (circleReflectFunctions f) = circleNorm T γ s f := by
  have hn (m b : ℕ) :
      eLpNorm (iteratedDeriv b (circleReflectFunctions f m)) 2 angleMeasure =
        eLpNorm (iteratedDeriv b (f m)) 2 angleMeasure :=
    circle_reflection_jet_norm (hf.1 m).1 b
  unfold circleNorm
  simp only [hn]

section Model

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}
variable (hS : IsCircleModel T γ S)

include hS

private theorem circleModel_reflected_exists (u : S.Space) :
    ∃ v : S.Space, S.decode v = circleReflectFunctions (S.decode u) :=
  hS.2.2.2.2.1 _ (circleMember_reflectFunctions (hS.2.2.2.1 u))

/-- The unique element whose decoded function is the reflected one. -/
def circleModelReflectionFun (u : S.Space) : S.Space :=
  Classical.choose (circleModel_reflected_exists hS u)

theorem circleModelReflectionFun_decode (u : S.Space) :
    S.decode (circleModelReflectionFun hS u) = circleReflectFunctions (S.decode u) :=
  Classical.choose_spec (circleModel_reflected_exists hS u)

def circleModelReflectionLinear : S.Space →ₗ[ℝ] S.Space where
  toFun := circleModelReflectionFun hS
  map_add' := by
    intro u v
    apply hS.2.2.2.2.2.1
    funext m θ
    simp only [circleModelReflectionFun_decode, map_add, Pi.add_apply, circleReflectFunctions]
  map_smul' := by
    intro c u
    apply hS.2.2.2.2.2.1
    funext m θ
    simp only [circleModelReflectionFun_decode, map_smul, Pi.smul_apply, circleReflectFunctions,
      RingHom.id_apply]

theorem circleModelReflectionLinear_decode (u : S.Space) :
    S.decode (circleModelReflectionLinear hS u) = circleReflectFunctions (S.decode u) :=
  circleModelReflectionFun_decode hS u

theorem circleModelReflectionLinear_level_norm (u : S.Space) (s : ℕ) :
    ‖(circleModelReflectionLinear hS u).val s‖ = ‖u.val s‖ := by
  calc
    ‖(circleModelReflectionLinear hS u).val s‖ =
        circleNorm T γ s (S.decode (circleModelReflectionLinear hS u)) :=
      hS.2.2.2.2.2.2.2 (circleModelReflectionLinear hS u) s
    _ = circleNorm T γ s (circleReflectFunctions (S.decode u)) :=
      congrArg (circleNorm T γ s) (circleModelReflectionLinear_decode hS u)
    _ = circleNorm T γ s (S.decode u) := circleNorm_reflectFunctions (hS.2.2.2.1 u) s
    _ = ‖u.val s‖ := (hS.2.2.2.2.2.2.2 u s).symm

theorem circleModelReflectionLinear_grading (u : S.Space) (s : ℕ) :
    S.grading s (circleModelReflectionLinear hS u) = S.grading s u :=
  Analysis.gradedSeminorm_eq_of_norm_eq s _ _
    (fun i _ => circleModelReflectionLinear_level_norm hS u i)

theorem circleModelReflectionLinear_isTame :
    Analysis.IsTameLinear S.grading S.grading (circleModelReflectionLinear hS) 0 0 := by
  intro s _
  refine ⟨1, fun u => ?_⟩
  simpa only [NNReal.coe_one, one_mul, Nat.add_zero,
    circleModelReflectionLinear_grading] using le_refl (S.grading s u)

/-- Angular reflection as a continuous linear map of the actual model. -/
def circleModelReflection : S.Space →L[ℝ] S.Space :=
  (circleModelReflectionLinear_isTame hS).toContinuousLinearMap
    (Analysis.withSeminorms_graded _ _) (Analysis.withSeminorms_graded _ _)
    (Analysis.gradedSeminorm_monotone _ _)

theorem circleModelReflection_apply (u : S.Space) :
    circleModelReflection hS u = circleModelReflectionLinear hS u :=
  Analysis.IsTameLinear.toContinuousLinearMap_apply _ _ _ _ u

theorem circleModelReflection_decode (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleModelReflection hS u) m θ = S.decode u m (-θ) := by
  exact (congrArg (fun v : S.Space => S.decode v m θ) (circleModelReflection_apply hS u)).trans
    ((congrFun (congrFun (circleModelReflectionLinear_decode hS u) m) θ).trans
      (circleReflectFunctions_eq_neg (hS.2.2.2.1 u) m θ))

theorem circleModelReflection_involutive (u : S.Space) :
    circleModelReflection hS (circleModelReflection hS u) = u := by
  apply hS.2.2.2.2.2.1
  funext m θ
  simpa only [neg_neg] using (circleModelReflection_decode hS (circleModelReflection hS u) m θ).trans
    (circleModelReflection_decode hS u m (-θ))

theorem circleModelReflection_isTame :
    Analysis.IsTameLinear S.grading S.grading (circleModelReflection hS).toLinearMap 0 0 :=
  circleModelReflectionLinear_isTame hS

/-- Projection onto the even angular functions. -/
def circleModelEvenProjection : S.Space →L[ℝ] S.Space :=
  SMul.smul (M := ℝ) (α := S.Space →L[ℝ] S.Space) (1 / 2)
    (ContinuousLinearMap.id ℝ S.Space + circleModelReflection hS)

/-- Projection onto the odd angular functions. -/
def circleModelOddProjection : S.Space →L[ℝ] S.Space :=
  SMul.smul (M := ℝ) (α := S.Space →L[ℝ] S.Space) (1 / 2)
    (ContinuousLinearMap.id ℝ S.Space - circleModelReflection hS)

theorem circleModelEvenProjection_decode (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleModelEvenProjection hS u) m θ =
      (S.decode u m θ + S.decode u m (-θ)) / 2 := by
  have hs := congrFun (congrFun
    (S.decode.map_smul (1 / 2 : ℝ) (u + circleModelReflection hS u)) m) θ
  have ha := congrFun (congrFun (S.decode.map_add u (circleModelReflection hS u)) m) θ
  calc
    S.decode (circleModelEvenProjection hS u) m θ =
        (1 / 2 : ℝ) * S.decode (u + circleModelReflection hS u) m θ := hs
    _ = (1 / 2 : ℝ) * (S.decode u m θ + S.decode (circleModelReflection hS u) m θ) :=
      congrArg (fun x : ℝ => (1 / 2 : ℝ) * x) ha
    _ = (1 / 2 : ℝ) * (S.decode u m θ + S.decode u m (-θ)) :=
      congrArg (fun x : ℝ => (1 / 2 : ℝ) * (S.decode u m θ + x))
        (circleModelReflection_decode hS u m θ)
    _ = _ := by ring

theorem circleModelOddProjection_decode (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleModelOddProjection hS u) m θ =
      (S.decode u m θ - S.decode u m (-θ)) / 2 := by
  have hs := congrFun (congrFun
    (S.decode.map_smul (1 / 2 : ℝ) (u - circleModelReflection hS u)) m) θ
  have ha := congrFun (congrFun (S.decode.map_sub u (circleModelReflection hS u)) m) θ
  calc
    S.decode (circleModelOddProjection hS u) m θ =
        (1 / 2 : ℝ) * S.decode (u - circleModelReflection hS u) m θ := hs
    _ = (1 / 2 : ℝ) * (S.decode u m θ - S.decode (circleModelReflection hS u) m θ) :=
      congrArg (fun x : ℝ => (1 / 2 : ℝ) * x) ha
    _ = (1 / 2 : ℝ) * (S.decode u m θ - S.decode u m (-θ)) :=
      congrArg (fun x : ℝ => (1 / 2 : ℝ) * (S.decode u m θ - x))
        (circleModelReflection_decode hS u m θ)
    _ = _ := by ring

theorem circleModelEvenProjection_idempotent (u : S.Space) :
    circleModelEvenProjection hS (circleModelEvenProjection hS u) =
      circleModelEvenProjection hS u := by
  apply hS.2.2.2.2.2.1
  funext m θ
  have he := circleModelEvenProjection_decode hS u m θ
  have hen : S.decode (circleModelEvenProjection hS u) m (-θ) =
      (S.decode u m (-θ) + S.decode u m θ) / 2 := by
    simpa only [neg_neg] using circleModelEvenProjection_decode hS u m (-θ)
  calc
    S.decode (circleModelEvenProjection hS (circleModelEvenProjection hS u)) m θ =
        (S.decode (circleModelEvenProjection hS u) m θ +
          S.decode (circleModelEvenProjection hS u) m (-θ)) / 2 :=
      circleModelEvenProjection_decode hS (circleModelEvenProjection hS u) m θ
    _ = ((S.decode u m θ + S.decode u m (-θ)) / 2 +
        (S.decode u m (-θ) + S.decode u m θ) / 2) / 2 :=
      congrArg₂ (fun x y : ℝ => (x + y) / 2) he hen
    _ = (S.decode u m θ + S.decode u m (-θ)) / 2 := by ring
    _ = S.decode (circleModelEvenProjection hS u) m θ := he.symm

theorem circleModelOddProjection_idempotent (u : S.Space) :
    circleModelOddProjection hS (circleModelOddProjection hS u) =
      circleModelOddProjection hS u := by
  apply hS.2.2.2.2.2.1
  funext m θ
  have ho := circleModelOddProjection_decode hS u m θ
  have hon : S.decode (circleModelOddProjection hS u) m (-θ) =
      (S.decode u m (-θ) - S.decode u m θ) / 2 := by
    simpa only [neg_neg] using circleModelOddProjection_decode hS u m (-θ)
  calc
    S.decode (circleModelOddProjection hS (circleModelOddProjection hS u)) m θ =
        (S.decode (circleModelOddProjection hS u) m θ -
          S.decode (circleModelOddProjection hS u) m (-θ)) / 2 :=
      circleModelOddProjection_decode hS (circleModelOddProjection hS u) m θ
    _ = ((S.decode u m θ - S.decode u m (-θ)) / 2 -
        (S.decode u m (-θ) - S.decode u m θ) / 2) / 2 :=
      congrArg₂ (fun x y : ℝ => (x - y) / 2) ho hon
    _ = (S.decode u m θ - S.decode u m (-θ)) / 2 := by ring
    _ = S.decode (circleModelOddProjection hS u) m θ := ho.symm

theorem circleModelEvenProjection_isTame :
    Analysis.IsTameLinear S.grading S.grading
      (circleModelEvenProjection hS).toLinearMap 0 0 :=
  ((Analysis.IsTameLinear.id S.grading).add
    (Analysis.gradedSeminorm_monotone _ _) (circleModelReflection_isTame hS)).smul (1 / 2)

theorem circleModelOddProjection_isTame :
    Analysis.IsTameLinear S.grading S.grading
      (circleModelOddProjection hS).toLinearMap 0 0 :=
  ((Analysis.IsTameLinear.id S.grading).sub
    (Analysis.gradedSeminorm_monotone _ _) (circleModelReflection_isTame hS)).smul (1 / 2)

/-- Even and odd circle projections, with their exact decoded formulas and
zero-loss tame estimates. -/
theorem circleModel_exists_parity_projections :
    ∃ even odd : S.Space →L[ℝ] S.Space,
      (∀ u m θ, S.decode (even u) m θ =
        (S.decode u m θ + S.decode u m (-θ)) / 2) ∧
      (∀ u m θ, S.decode (odd u) m θ =
        (S.decode u m θ - S.decode u m (-θ)) / 2) ∧
      (∀ u, even (even u) = even u ∧ odd (odd u) = odd u) ∧
      Analysis.IsTameLinear S.grading S.grading even.toLinearMap 0 0 ∧
      Analysis.IsTameLinear S.grading S.grading odd.toLinearMap 0 0 :=
  ⟨circleModelEvenProjection hS, circleModelOddProjection hS,
    circleModelEvenProjection_decode hS, circleModelOddProjection_decode hS,
    fun u => ⟨circleModelEvenProjection_idempotent hS u, circleModelOddProjection_idempotent hS u⟩,
    circleModelEvenProjection_isTame hS, circleModelOddProjection_isTame hS⟩

end Model

end ContinuousFlexibility.Statements
