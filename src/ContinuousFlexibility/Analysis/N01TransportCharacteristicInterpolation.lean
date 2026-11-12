import ContinuousFlexibility.Analysis.N01CharacteristicJointGrowth
import ContinuousFlexibility.Analysis.N01TransportAngularInterpolation
import ContinuousFlexibility.Analysis.WeightedJointMixedInterpolation

/-!
# Characteristic interpolation on the full correction parameter space

The original speed is independent of the separate residual input.
Projection preserves its genuine joint tower and every quantitative
bound, with the same base and loss. Uniqueness then transfers this bound
to any supplied actual tower. A single interpolation step gives the
primitive mixed bounds used by the radial transport recurrence.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

section Projection

variable {I E F P G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.fstParameter_apply
    {U : Set E} {V : Set P} {f : E × P → G}
    (J : SmoothDirections (U ×ˢ V) f) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ) (x : E × F) (y : P) (v : Fin n → (E × F) × P) :
    (J.fstParameter (F := F) hU hV).D n (x, y) v =
      J.D n (x.1, y) (fun i => ((v i).1.1, (v i).2)) := by
  simp only [SmoothDirections.fstParameter, SmoothDirections.compLinear,
    SmoothDirections.congrOn, SmoothDirections.compAffine_apply, zero_add,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

/-- Adding an independent parameter keeps the original constants, base,
loss, and spatial directions. -/
theorem UniformWeightedJointGrowth.fstParameter
    {p : ℕ → Seminorm ℝ E} (q : ℕ → Seminorm ℝ F)
    {W : I → ℝ} (hW : ∀ i, 0 ≤ W i)
    {U : Set E} {V : I → Set P} {f : I → E × P → G}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) :
    UniformWeightedJointGrowth (pairGrading p q) W
      (fun i => (J i).fstParameter (F := F) hU (hV i)) base loss := by
  have hfst (s : ℕ) (x : E × F) : p s x.1 ≤ pairGrading p q s x := by
    rw [pairGrading_apply]
    exact le_add_of_nonneg_right (apply_nonneg (q s) x.2)
  intro R hR n
  obtain ⟨C, A, hC, hA, hb⟩ := hJ R hR n
  refine ⟨C, A, hC, hA, fun i x hx hlow y hy v hv => ?_⟩
  rw [SmoothDirections.fstParameter_apply]
  have hunit (j : Fin n) : p base (v j).1.1 + ‖(v j).2‖ ≤ 1 :=
    (add_le_add (hfst base (v j).1) le_rfl).trans (hv j)
  have h := hb i x.1 hx.1 ((hfst base x).trans hlow) y hy
    (fun j => ((v j).1.1, (v j).2)) hunit
  refine h.trans (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg hC (Real.rpow_nonneg (hW i) _)))
  exact add_le_add (add_le_add le_rfl (hfst (n + loss) x))
    (Finset.sum_le_sum (fun j _ => hfst (n + loss) (v j).1))

end Projection

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n01TransportCharacteristicInterpolationStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The same actual characteristic bound on the parameter space that
also contains the independent residual. -/
theorem N01Properties.minusCharacteristicSpeed_correction_joint_growth
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a p ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (J : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        minusCharacteristicSpeed
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)) x.2)) :
    ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧
      UniformWeightedJointGrowth
        (pairGrading (pairGrading (sectorGrading S) realGrading)
          (S.circle (3 / 4 : ℝ)).grading)
        (fun m => radialE (D.cellIndex (j m))) J B L := by
  obtain ⟨K, B, L, hb, hloss, hg⟩ :=
    hN.exists_minusCharacteristicSpeed_strip_joint_growth
      hS hT j hcell l h hl hh hlam hP hpositive
  have hlift := hg.fstParameter (S.circle (3 / 4 : ℝ)).grading
    (fun m => zero_le_one.trans (one_le_radialE_of_nat _))
    (sectorNeighborhood_isOpen S base ε ε) (fun _ => isOpen_Ioo.prod isOpen_univ)
  exact ⟨B, L, hb, hloss, hlift.congr J (fun _ _ _ => rfl)⟩

/-- Primitive characteristic jets have exactly the total spatial order
as their exponent budget on the same high scale as the angular fields. -/
theorem N01Properties.minusCharacteristicSpeed_correction_mixed_interpolation
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (p : PolarPoint),
      p.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a p ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (J : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        minusCharacteristicSpeed
          (originalCoefficients D S C (liftSectorParameter S C x.1.1)) x.2))
    (nmax : ℕ) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    ∃ B : ℕ, ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ a b : ℕ, a + b ≤ N →
      ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
        ∀ m x, x ∈ sectorNeighborhood S base ε ε ×ˢ univ → ∀ w,
        p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n a b x w y| ≤
          K * radialE (D.cellIndex (j m)) ^ Q *
            (1 + p (N + B + 1) x + p (N + B + 1) w) ^
              (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
  obtain ⟨B₀, L, _, _, hg⟩ :=
    hN.minusCharacteristicSpeed_correction_joint_growth
      hS hT j hcell l h hl hh hlam hP hpositive J
  have hdomain (m : ℕ) : Convex ℝ
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo (l m) (h m) ×ˢ (univ : Set ℝ))) :=
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ)
  obtain ⟨B, _, hbound⟩ := hg.mixed_diagonal_spatial_interpolation
    (correctionParameterGrading_monotone S) (correctionParameterGrading_hasInterpolation hS)
    (fun m => one_le_radialE_of_nat _) (fun _ => isOpen_Ioo.prod isOpen_univ) hdomain nmax
  refine ⟨B, fun A hA N n hn a b hab => ?_⟩
  obtain ⟨K, Q, hK, hQ, hb⟩ := hbound A hA N n hn a b hab
  exact ⟨K, Q, hK, hQ, fun m x hx w hxlow hwlow y hy =>
    hb m x hx w hxlow hwlow y ⟨hy, mem_univ _⟩⟩

end ContinuousFlexibility.Statements
