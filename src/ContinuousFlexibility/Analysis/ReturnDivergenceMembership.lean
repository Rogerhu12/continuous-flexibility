import ContinuousFlexibility.Analysis.ReturnDivergenceBilinear
import ContinuousFlexibility.Analysis.MaterialDivergenceNormBounds
import ContinuousFlexibility.Scalar.Conservation

/-!
# Physical membership of the actual bilinear divergence

The odd/even coefficient pair acts on the original even periodic height.
Its zero extension has the exact source symmetries. A fixed material
weight power for every coefficient derivative gives every physical L²
jet and preserves the sharp coefficient/height derivative-order budget.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def SymmetricErrorCoefficientSymmetry (A : PolarPoint → ℝ × ℝ) : Prop :=
  (∀ r θ, (A (r, -θ)).1 = -(A (r, θ)).1) ∧
  (∀ r θ, (A (r, -θ)).2 = (A (r, θ)).2) ∧
  Function.Periodic A (0, Real.pi)

theorem symmetricDivergenceBilinear_even
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D) (hA : SymmetricErrorCoefficientSymmetry A.val)
    (η : HeightPair S) (r θ : ℝ) :
    symmetricDivergenceBilinear hS hT A η (r, -θ) =
      symmetricDivergenceBilinear hS hT A η (r, θ) := by
  let u := (S.height (3 / 4 : ℝ)).decode η.1
  let F (p : PolarPoint) := (A.val p).1 * angularPartial u p
  let G (p : PolarPoint) :=
    (A.val p).1 * radialPartial u p + (A.val p).2 * angularPartial u p
  have hu : ∀ s ψ, u (s, -ψ) = u (s, ψ) := ((hS.1 _).2.2.2.1 η.1).2.1
  have hF : ∀ s ψ, F (s, -ψ) = F (s, ψ) := by
    intro s ψ
    dsimp only [F]
    rw [hA.1, angularPartial_of_even u hu]
    ring
  have hG : ∀ s ψ, G (s, -ψ) = -G (s, ψ) := by
    intro s ψ
    dsimp only [G]
    rw [hA.1, hA.2.1, radialPartial_of_even u hu, angularPartial_of_even u hu]
    ring
  have hd := congrArg₂ (fun a b : ℝ => a + b)
    (radialPartial_of_even F hF r θ) (angularPartial_of_odd G hG r θ)
  by_cases hr : r ∈ Ioo D.a D.b
  · have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ _⟩
    have hp' : (r, -θ) ∈ annularOpen D := ⟨hr, mem_univ _⟩
    rw [symmetricDivergenceBilinear_apply, symmetricDivergenceBilinear_apply,
      if_pos hp', if_pos hp]
    exact hd
  · have hp : (r, θ) ∉ annularOpen D := fun hp => hr hp.1
    have hp' : (r, -θ) ∉ annularOpen D := fun hp => hr hp.1
    rw [symmetricDivergenceBilinear_apply, symmetricDivergenceBilinear_apply,
      if_neg hp', if_neg hp]

theorem symmetricDivergenceBilinear_periodic
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D) (hA : SymmetricErrorCoefficientSymmetry A.val)
    (η : HeightPair S) :
    Function.Periodic (symmetricDivergenceBilinear hS hT A η) (0, Real.pi) := by
  let u := (S.height (3 / 4 : ℝ)).decode η.1
  have hu : Function.Periodic u (0, Real.pi) := ((hS.1 _).2.2.2.1 η.1).2.2.1
  have hfirst : Function.Periodic (fun p => (A.val p).1) (0, Real.pi) :=
    fun p => congrArg Prod.fst (hA.2.2 p)
  have hsecond : Function.Periodic (fun p => (A.val p).2) (0, Real.pi) :=
    fun p => congrArg Prod.snd (hA.2.2 p)
  have hF := hfirst.mul (periodic_angularPartial hu)
  have hG := (hfirst.mul (periodic_radialPartial hu)).add
    (hsecond.mul (periodic_angularPartial hu))
  have hd := (periodic_radialPartial hF).add (periodic_angularPartial hG)
  intro p
  have hmem : p + (0, Real.pi) ∈ annularOpen D ↔ p ∈ annularOpen D := by
    simp only [annularOpen, mem_prod, mem_univ, and_true, Prod.fst_add,
      Prod.fst_mk, add_zero]
  by_cases hp : p ∈ annularOpen D
  · rw [symmetricDivergenceBilinear_apply, symmetricDivergenceBilinear_apply,
      if_pos (hmem.mpr hp), if_pos hp]
    exact hd p
  · rw [symmetricDivergenceBilinear_apply, symmetricDivergenceBilinear_apply,
      if_neg (fun h => hp (hmem.mp h)), if_neg hp]

theorem symmetricDivergenceBilinear_memLp
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D) (d : ℕ)
    (hbound : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ p : PolarPoint,
      |mixedDerivative a b (fun q => (A.val (T.radius q.1, q.2)).1) p| ≤
        K * T.M (T.radius p.1) ^ d ∧
      |mixedDerivative a b (fun q => (A.val (T.radius q.1, q.2)).2) p| ≤
        K * T.M (T.radius p.1) ^ d)
    (η : HeightPair S) (a b c : ℕ) :
    MemLp (weightedPhysicalJet T (3 / 4 : ℝ) a b c
      (symmetricDivergenceBilinear hS hT A η)) 2 materialCylinderMeasure := by
  let u := (S.height (3 / 4 : ℝ)).decode η.1
  have hu : HeightMember D T (3 / 4 : ℝ) u := (hS.1 _).2.2.2.1 η.1
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hur := contDiffOn_radialPartial_of_isOpen hU hu.1
  have hut := contDiffOn_angularPartial_of_isOpen hU hu.1
  have hurLp := memLp_weightedPhysicalJet_radialPartial hT hu.1 hu.2.2.2.2
  have hutLp := memLp_weightedPhysicalJet_angularPartial hT hu.1 hu.2.2.2.2
  have hfirst (i j : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : PolarPoint,
      |mixedDerivative i j (fun q => (A.val (T.radius q.1, q.2)).1) p| ≤
        K * T.M (T.radius p.1) ^ d :=
    ⟨(hbound i j).choose, (hbound i j).choose_spec.1,
      fun p => ((hbound i j).choose_spec.2 p).1⟩
  have hsecond (i j : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : PolarPoint,
      |mixedDerivative i j (fun q => (A.val (T.radius q.1, q.2)).2) p| ≤
        K * T.M (T.radius p.1) ^ d :=
    ⟨(hbound i j).choose, (hbound i j).choose_spec.1,
      fun p => ((hbound i j).choose_spec.2 p).2⟩
  let F (p : PolarPoint) := (A.val p).1 * angularPartial u p
  let G (p : PolarPoint) :=
    (A.val p).1 * radialPartial u p + (A.val p).2 * angularPartial u p
  have hF : ContDiffOn ℝ ∞ F (annularOpen D) := A.property.fst.mul hut
  have hG : ContDiffOn ℝ ∞ G (annularOpen D) :=
    (A.property.fst.mul hur).add (A.property.snd.mul hut)
  have hFLp := memLp_weightedPhysicalJet_mul_of_material_bound hT A.property.fst hut hutLp d hfirst
  have hGLp (i j k : ℕ) := memLp_weightedPhysicalJet_add hT
    (A.property.fst.mul hur) (A.property.snd.mul hut)
    (memLp_weightedPhysicalJet_mul_of_material_bound hT A.property.fst hur hurLp d hfirst i j k)
    (memLp_weightedPhysicalJet_mul_of_material_bound hT A.property.snd hut hutLp d hsecond i j k)
  have hd := memLp_weightedPhysicalJet_add hT
    (contDiffOn_radialPartial_of_isOpen hU hF) (contDiffOn_angularPartial_of_isOpen hU hG)
    (memLp_weightedPhysicalJet_radialPartial hT hF hFLp a b c)
    (memLp_weightedPhysicalJet_angularPartial hT hG hGLp a b c)
  have heq : EqOn (symmetricDivergenceBilinear hS hT A η)
      (fun p => radialPartial F p + angularPartial G p) (annularOpen D) := by
    intro p hp
    rw [symmetricDivergenceBilinear_apply, if_pos hp]
  rw [weightedPhysicalJet_eq_of_eqOn_annularOpen hT heq a b c]
  exact hd

theorem symmetricDivergenceBilinear_heightMember
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D)
    (hA : SymmetricErrorCoefficientSymmetry A.val) (d : ℕ)
    (hbound : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ p : PolarPoint,
      |mixedDerivative a b (fun q => (A.val (T.radius q.1, q.2)).1) p| ≤
        K * T.M (T.radius p.1) ^ d ∧
      |mixedDerivative a b (fun q => (A.val (T.radius q.1, q.2)).2) p| ≤
        K * T.M (T.radius p.1) ^ d)
    (η : HeightPair S) :
    HeightMember D T (3 / 4 : ℝ) (symmetricDivergenceBilinear hS hT A η) := by
  refine ⟨symmetricDivergenceBilinear_contDiffOn hS hT A η,
    symmetricDivergenceBilinear_even hS hT A hA η,
    symmetricDivergenceBilinear_periodic hS hT A hA η, ?_,
    symmetricDivergenceBilinear_memLp hS hT A d hbound η⟩
  intro p hp
  rw [symmetricDivergenceBilinear_apply, if_neg hp]

theorem physicalNorm_eq_of_eqOn_annularOpen
    {γ : ℝ} {f g : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (heq : EqOn f g (annularOpen D)) (s : ℕ) :
    physicalNorm T γ s f = physicalNorm T γ s g := by
  unfold physicalNorm
  simp only [weightedPhysicalJet_eq_of_eqOn_annularOpen hT heq]

theorem exists_physicalNorm_symmetricDivergenceBilinear_bound
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (s d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : annularSmoothCoefficientSpace D,
      ∀ K : ℕ → ℝ, (∀ k, 0 ≤ K k) →
      (∀ a b, ∀ p : PolarPoint,
        |mixedDerivative a b (fun q => (A.val (T.radius q.1, q.2)).1) p| ≤
          K (a + b) * T.M (T.radius p.1) ^ d ∧
        |mixedDerivative a b (fun q => (A.val (T.radius q.1, q.2)).2) p| ≤
          K (a + b) * T.M (T.radius p.1) ^ d) →
      ∀ η : HeightPair S,
      physicalNorm T (3 / 4 : ℝ) s (symmetricDivergenceBilinear hS hT A η) ≤
        C * ∑ k ∈ Finset.range (s + 3),
          K k * physicalNorm T (3 / 4 : ℝ) (s + 4 - k + d)
            ((S.height (3 / 4 : ℝ)).decode η.1) := by
  obtain ⟨C, hC, hb⟩ := exists_physicalNorm_symmetric_divergence_bound hT (3 / 4 : ℝ) s d
  refine ⟨C, hC, fun A K hK hcoeff η => ?_⟩
  have hu := (hS.1 (3 / 4 : ℝ)).2.2.2.1 η.1
  have heq : EqOn (symmetricDivergenceBilinear hS hT A η)
      (fun p => radialPartial (fun q => (A.val q).1 *
          angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) q) p +
        angularPartial (fun q => (A.val q).1 *
          radialPartial ((S.height (3 / 4 : ℝ)).decode η.1) q +
          (A.val q).2 * angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) q) p)
      (annularOpen D) := by
    intro p hp
    rw [symmetricDivergenceBilinear_apply, if_pos hp]
  exact (physicalNorm_eq_of_eqOn_annularOpen hT heq s).trans_le
    (hb (fun p => (A.val p).1) (fun p => (A.val p).2)
      A.property.fst A.property.snd K hK hcoeff _ hu.1 hu.2.2.2.2)

end ContinuousFlexibility.Statements
