module

public import ContinuousFlexibility.Analysis.CircleInverseSmoothTame
public import ContinuousFlexibility.Analysis.TameTopologicalComposition
public import ContinuousFlexibility.Analysis.TameProductDirections

/-!
# The actual inverse lift displacement

The inverse of `θ ↦ θ + travel + e θ` differs from the opposite
translation by `-e` composed with that inverse. This is an element of
the original circle space, and the diagonal of the inverse-composition
family has its genuine smooth tame tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem smoothTameOn_neg_diagonal
    {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, NormedSpace ℝ (G n)]
    [∀ n, CompleteSpace (G n)] {g : ∀ n, G (n + 1) →L[ℝ] G n}
    {p : ℕ → Seminorm ℝ (ProjectiveLimit G g)}
    (hp : Monotone p) (ht : WithSeminorms p)
    {U : Set (ProjectiveLimit G g)} (hU : IsOpen U)
    {f : ProjectiveLimit G g × ProjectiveLimit G g → ProjectiveLimit G g}
    (hf : SmoothTameOn (pairGrading p p) p (U ×ˢ univ) f) :
    SmoothTameOn p p U (fun e => -f (e, e)) := by
  have hid : SmoothTameOn p p U (fun e : ProjectiveLimit G g => e) :=
    smoothTameOn_restrict_open
      (smoothTameOn_continuousLinear (ContinuousLinearMap.id ℝ (ProjectiveLimit G g))
        (IsTameLinear.id p)) hU (subset_univ _)
  have hdiag := smoothTameOn_prodMk hp ht hid hid
  have hvalue : SmoothTameOn p p U (fun e => f (e, e)) :=
    smoothTameOn_comp_topological hp ht (withSeminorms_pairGrading ht ht)
      hU (hU.prod isOpen_univ) (fun e he => ⟨he, mem_univ _⟩) hdiag hf
  let N : ProjectiveLimit G g →L[ℝ] ProjectiveLimit G g :=
    -ContinuousLinearMap.id ℝ (ProjectiveLimit G g)
  have hN : IsTameLinear p p N.toLinearMap 0 0 := (IsTameLinear.id p).neg
  have hneg : SmoothTameOn p p univ (fun e : ProjectiveLimit G g => -e) := by
    refine smoothTameOn_congr (smoothTameOn_continuousLinear N hN) ?_
    intro e he
    change (-ContinuousLinearMap.id ℝ (ProjectiveLimit G g)) e = -e
    simp only [neg_apply, ContinuousLinearMap.id_apply]
  exact smoothTameOn_comp_topological hp ht ht hU isOpen_univ
    (fun _ _ => mem_univ _) hvalue hneg

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleInversePerturbation
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (e : S.Space) : S.Space :=
  -circleInverseComposeLinear hS hT hD hγ travel a ha e e

theorem circleInversePerturbation_decode
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (e : S.Space)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) :
    S.decode (circleInversePerturbation hS hT hD hγ travel a ha e) =
      fun m θ => circleAffineInverse travel e m θ - (θ - travel m) := by
  have hdecode := circleInverseComposeLinear_decode hS hT hD hγ travel a ha e e hlower
  funext m θ
  have hneg :
      S.decode (circleInversePerturbation hS hT hD hγ travel a ha e) m θ =
        -S.decode e m (circleAffineInverse travel e m θ) := by
    exact (congrFun (congrFun (S.decode.map_neg
      (circleInverseComposeLinear hS hT hD hγ travel a ha e e)) m) θ).trans
        (congrArg Neg.neg (congrFun (congrFun hdecode m) θ))
  have hright : circleAffineInverse travel e m θ + travel m +
      S.decode e m (circleAffineInverse travel e m θ) = θ := by
    simpa only [circleAffineLift, one_mul] using
      circleAffineInverse_right hS hT hD hγ travel e m θ
  exact hneg.trans (by linarith only [hright])

theorem smoothTameOn_circleInversePerturbation
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    {U : Set S.Space} (hU : IsOpen U)
    (hV : SmoothTameOn (pairGrading S.grading S.grading) S.grading (U ×ˢ univ)
      (fun z : S.Space × S.Space =>
        circleInverseComposeLinear hS hT hD hγ travel a ha z.1 z.2)) :
    SmoothTameOn S.grading S.grading U
      (circleInversePerturbation hS hT hD hγ travel a ha) := by
  letI : ∀ n, CompleteSpace (S.level n) :=
    fun n => (hS.2.1 n).isComplete.completeSpace_coe
  exact smoothTameOn_neg_diagonal
    (gradedSeminorm_monotone (fun n => S.level n) S.bond)
    (withSeminorms_graded (fun n => S.level n) S.bond) hU hV

end ContinuousFlexibility.Statements
