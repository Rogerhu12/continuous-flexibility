module

public import ContinuousFlexibility.Analysis.N01CharacteristicJointGrowth
public import ContinuousFlexibility.Analysis.N01TransportAngularInterpolation
public import ContinuousFlexibility.Analysis.WeightedJointMixedInterpolation

/-!
# Characteristic interpolation on the full correction parameter space

The original speed is independent of the separate residual input.
Projection preserves its genuine joint tower and every quantitative
bound, with the same base and loss. Uniqueness then transfers this bound
to any supplied actual tower. A single interpolation step gives the
primitive mixed bounds used by the radial transport recurrence.
-/

@[expose] public section

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
  let L : (E × F) × P →L[ℝ] E × P :=
    ((ContinuousLinearMap.fst ℝ E F).comp
      (ContinuousLinearMap.fst ℝ (E × F) P)).prod
        (ContinuousLinearMap.snd ℝ (E × F) P)
  have hL (z : (E × F) × P) : L z = (z.1.1, z.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hW : IsOpen ((U ×ˢ (univ : Set F)) ×ˢ V) := (hU.prod isOpen_univ).prod hV
  have hmap : MapsTo (fun z => (0 : E × P) + L z)
      ((U ×ˢ (univ : Set F)) ×ˢ V) (U ×ˢ V) := by
    intro z hz
    have hz' : (z.1.1, z.2) ∈ U ×ˢ V := ⟨hz.1.1, hz.2⟩
    simpa only [zero_add, hL] using hz'
  have hD : (J.compAffine L 0 hW hmap).D n (x, y) v =
      J.D n (0 + L (x, y)) (fun i => L (v i)) :=
    SmoothDirections.compAffine_apply
      (E := (E × F) × P) (F := E × P) (G := G)
      (U := U ×ˢ V) (V := (U ×ˢ (univ : Set F)) ×ˢ V) (f := f)
      J L 0 hW hmap n (x, y) v
  simpa only [SmoothDirections.fstParameter, SmoothDirections.compLinear,
    SmoothDirections.congrOn, zero_add, hL] using hD

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
  let p : ℕ → Seminorm ℝ (StateDirections S × ℝ) :=
    pairGrading (sectorGrading S) realGrading
  let q : ℕ → Seminorm ℝ (CircleSpace S) := (S.circle (3 / 4 : ℝ)).grading
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let f : ℕ → (StateDirections S × ℝ) × PolarPoint → ℝ := fun _ x =>
    minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let data : ∃ K : ∀ m, SmoothDirections (U ×ˢ V m) (f m),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W K B L :=
    hN.exists_minusCharacteristicSpeed_strip_joint_growth
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT j hcell l h hl hh hlam hP hpositive
  let K : ∀ m, SmoothDirections (U ×ˢ V m) (f m) := data.choose
  let B : ℕ := data.choose_spec.choose
  let L : ℕ := data.choose_spec.choose_spec.choose
  have hb : base ≤ B := data.choose_spec.choose_spec.choose_spec.1
  have hloss : loss ≤ B := data.choose_spec.choose_spec.choose_spec.2.1
  have hg : UniformWeightedJointGrowth p W K B L :=
    data.choose_spec.choose_spec.choose_spec.2.2
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hV (m : ℕ) : IsOpen (V m) := isOpen_Ioo.prod isOpen_univ
  let K' : ∀ m, SmoothDirections ((U ×ˢ (univ : Set (CircleSpace S))) ×ˢ V m)
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        f m (x.1.1, x.2)) :=
    fun m => SmoothDirections.fstParameter
      (E := StateDirections S × ℝ) (F := CircleSpace S) (P := PolarPoint) (G := ℝ)
      (U := U) (V := V m) (f := f m) (K m) hU (hV m)
  have hlift : UniformWeightedJointGrowth (pairGrading p q) W K' B L :=
    UniformWeightedJointGrowth.fstParameter
      (I := ℕ) (E := StateDirections S × ℝ) (F := CircleSpace S)
      (P := PolarPoint) (G := ℝ) (p := p) (W := W) (U := U) (V := V)
      (f := f) (J := K) (base := B) (loss := L) q
      (fun m => zero_le_one.trans (one_le_radialE_of_nat (D.cellIndex (j m)))) hg hU hV
  exact ⟨B, L, hb, hloss, UniformWeightedJointGrowth.congr
    (I := ℕ) (E := (StateDirections S × ℝ) × CircleSpace S) (P := PolarPoint) (F := ℝ)
    (p := pairGrading p q) (W := W) (U := U ×ˢ univ) (V := V)
    (f := fun m x => f m (x.1.1, x.2))
    (g := fun _ x => minusCharacteristicSpeed
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)) x.2)
    (J := K') (base := B) (loss := L) hlift J (fun _ _ _ => rfl)⟩

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
  let p : ℕ → Seminorm ℝ ((StateDirections S × ℝ) × CircleSpace S) :=
    pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading
  let U : Set ((StateDirections S × ℝ) × CircleSpace S) :=
    sectorNeighborhood S base ε ε ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let f : ℕ → (((StateDirections S × ℝ) × CircleSpace S) × PolarPoint) → ℝ :=
    fun _ x => minusCharacteristicSpeed
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)) x.2
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let data : ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W J B L :=
    hN.minusCharacteristicSpeed_correction_joint_growth
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT j hcell l h hl hh hlam hP hpositive J
  let B₀ : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hg : UniformWeightedJointGrowth p W J B₀ L :=
    data.choose_spec.choose_spec.2.2
  have hdomain (m : ℕ) : Convex ℝ (U ×ˢ V m) :=
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ).prod
      ((convex_Ioo (l m) (h m)).prod convex_univ)
  let bound : ∃ B : ℕ, B₀ ≤ B ∧ ∀ A : ℝ, 0 ≤ A →
      ∀ N n : ℕ, n ≤ nmax → ∀ a b : ℕ, a + b ≤ N →
      ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
        ∀ m x, x ∈ U → ∀ w : (StateDirections S × ℝ) × CircleSpace S,
          p B x ≤ A → p B w ≤ 1 → ∀ y ∈ V m,
          |jointMixedDiagonal (J m) n a b x w y| ≤
            K * W m ^ Q * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
              (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)) :=
    UniformWeightedJointGrowth.mixed_diagonal_spatial_interpolation
      (I := ℕ) (E := (StateDirections S × ℝ) × CircleSpace S)
      (p := p) (W := W) (U := U) (V := V) (f := f) (J := J) (base := B₀) (loss := L)
      hg (correctionParameterGrading_monotone S) (correctionParameterGrading_hasInterpolation hS)
      (fun m => one_le_radialE_of_nat (D.cellIndex (j m)))
      (fun _ => isOpen_Ioo.prod isOpen_univ) hdomain nmax
  let B : ℕ := bound.choose
  refine ⟨B, fun A hA N n hn a b hab => ?_⟩
  let scaleData : ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
      ∀ m x, x ∈ U → ∀ w : (StateDirections S × ℝ) × CircleSpace S,
        p B x ≤ A → p B w ≤ 1 → ∀ y ∈ V m,
        |jointMixedDiagonal (J m) n a b x w y| ≤
          K * W m ^ Q * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)) :=
    bound.choose_spec.2 A hA N n hn a b hab
  let K : ℝ := scaleData.choose
  let Q : ℝ := scaleData.choose_spec.choose
  have hK : 0 ≤ K := scaleData.choose_spec.choose_spec.1
  have hQ : 0 ≤ Q := scaleData.choose_spec.choose_spec.2.1
  exact ⟨K, Q, hK, hQ, fun m x hx w hxlow hwlow y hy =>
    scaleData.choose_spec.choose_spec.2.2 m x hx w hxlow hwlow y ⟨hy, mem_univ _⟩⟩

end ContinuousFlexibility.Statements
