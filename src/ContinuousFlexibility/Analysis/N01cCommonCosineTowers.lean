import ContinuousFlexibility.Analysis.N01cActualCosineSpeedTower
import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection
import ContinuousFlexibility.Analysis.N01cBoundsRestriction
import ContinuousFlexibility.Analysis.N01cSpeedTowerRestriction
import ContinuousFlexibility.Analysis.N01cOrdinarySpeedJointTowers

/-!
# One common actual cosine-speed tower neighbourhood

The primitive geometric witness supplies the optical root and its
positive endpoint quotient. Smoothing supplies one interpolation base.
Taking the minimum of the two radii and the original radius gives all
component towers on the same original state neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem n01c_commonSpeed_with_radii
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hinterp : HasInterpolation p)
    (base : ℕ) {ε : ℝ} (hε : 0 < ε)
    {B Q P : ℕ → ℝ → Prop} {R : ℝ → ℕ → ℕ → Prop}
    (hB : ∀ b e, base ≤ b → e ≤ ε → B b e)
    (hR : ∃ eo : ℝ, 0 < eo ∧ ∀ e : ℝ, 0 < e → e ≤ eo → ∀ b loss, R e b loss)
    (hQ : ∃ eq : ℝ, 0 < eq ∧ ∀ b, Q b eq)
    (hQmono : ∀ b e e', e' ≤ e → Q b e → Q b e')
    (hP : ∀ b loss e, 0 < e → e ≤ 1 / 2 → B b e → Q b e →
      (∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
        ∀ n : ℕ, n ≤ s → ∀ x : X, p b x ≤ 1 →
        ∀ Z : ℝ, 1 ≤ Z → p (s + loss) x ≤ Z →
          p (n + 4) x ≤ A * Z ^ ((n : ℝ) / ((s : ℝ) + 1))) →
      R e b loss → P b e) :
    ∃ b : ℕ, ∃ e : ℝ, base ≤ b ∧ 0 < e ∧ e ≤ ε ∧ B b e ∧ Q b e ∧ P b e := by
  obtain ⟨eo, heo, ho⟩ := hR
  obtain ⟨eq, heq, hq⟩ := hQ
  let e : ℝ := min ε (min (1 / 2) (min eo eq))
  have he : 0 < e := lt_min hε (lt_min (by norm_num) (lt_min heo heq))
  have heε : e ≤ ε := min_le_left _ _
  have he2 : e ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have heo' : e ≤ eo :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have heq' : e ≤ eq :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpos (b : ℕ) : Q b e := hQmono b eq e heq' (hq b)
  obtain ⟨b, loss, hb, hresult⟩ :=
    exists_base_ge_of_spatialPower_continuation p hp hinterp base 4 (fun b _ => P b e)
      (fun b loss hb hI =>
        hP b loss e he he2 (hB b e hb heε) (hpos b) hI (ho e he heo' b loss))
  exact ⟨b, e, hb, he, heε, hB b e hb heε, hpos b, hresult⟩

private theorem n01c_commonSpeed_project
    {base : ℕ} {ε : ℝ} {B Q P R : ℕ → ℝ → Prop}
    (h : ∃ b : ℕ, ∃ e : ℝ, base ≤ b ∧ 0 < e ∧ e ≤ ε ∧
      B b e ∧ Q b e ∧ P b e ∧ R b e) :
    ∃ b : ℕ, ∃ e : ℝ, base ≤ b ∧ 0 < e ∧ e ≤ ε ∧ B b e ∧ Q b e ∧ P b e := by
  obtain ⟨b, e, hb, he, her, hB, hQ, hP, _⟩ := h
  exact ⟨b, e, hb, he, her, hB, hQ, hP⟩

private theorem n01c_commonSpeed_stabilize
    {base : ℕ} {ε : ℝ} {B Q P : ℕ → ℝ → Prop}
    (h : ∃ b : ℕ, ∃ e : ℝ, base ≤ b ∧ 0 < e ∧ e ≤ ε ∧ B b e ∧ Q b e ∧ P b e)
    (hB : ∀ b e b' e', b ≤ b' → e' ≤ e → B b e → B b' e')
    (hQ : ∀ b e b' e', b ≤ b' → e' ≤ e → Q b e → Q b' e')
    (hP : ∀ b e b' e', b ≤ b' → e' ≤ e → P b e → P b' e') :
    ∃ b : ℕ, ∃ e : ℝ, base ≤ b ∧ 0 < e ∧ e ≤ ε ∧
      ∀ b' : ℕ, b ≤ b' → ∀ e' : ℝ, 0 < e' → e' ≤ e →
        B b' e' ∧ Q b' e' ∧ P b' e' := by
  obtain ⟨b, e, hb, he, her, hB₀, hQ₀, hP₀⟩ := h
  exact ⟨b, e, hb, he, her, fun b' hb' e' _ he' =>
    ⟨hB b e b' e' hb' he' hB₀, hQ b e b' e' hb' he' hQ₀,
      hP b e b' e' hb' he' hP₀⟩⟩

private theorem n01c_commonSpeed_forall_mono
    {X : Type*} {U V : Set X} {P : X → Prop} (hVU : V ⊆ U)
    (h : ∀ x ∈ U, P x) : ∀ x ∈ V, P x :=
  fun x hx => h x (hVU hx)

private theorem n01c_commonSpeed_timeTowers_restrict
    {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U V : Set X} {G : ι → X × PolarPoint → ℝ}
    (hV : IsOpen V) (hVU : V ⊆ U)
    (h : Nonempty (∀ i, ContinuousTimeSpeedTower U (G i))) :
    Nonempty (∀ i, ContinuousTimeSpeedTower V (G i)) := by
  obtain ⟨J⟩ := h
  exact ⟨fun i => (J i).n01c_restrict hV hVU⟩

private theorem n01c_commonSpeed_radialTowers_restrict
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U V : Set X} {Q : ℕ → ℝ → Prop} {F : ℕ → ℕ → ℝ → X × ℝ → ℝ}
    (hV : IsOpen V) (hVU : V ⊆ U)
    (h : Nonempty (∀ m a : ℕ, ∀ r : ℝ, Q m r →
      SmoothDirections (U ×ˢ (univ : Set ℝ)) (F m a r))) :
    Nonempty (∀ m a : ℕ, ∀ r : ℝ, Q m r →
      SmoothDirections (V ×ˢ (univ : Set ℝ)) (F m a r)) := by
  obtain ⟨J⟩ := h
  exact ⟨fun m a r hr => (J m a r hr).restrict (hV.prod isOpen_univ)
    (fun _ hy => ⟨hVU hy.1, hy.2⟩)⟩

/-- All actual cosine speeds have continuous time-indexed state-angle
towers after one enlargement of the low order and one shrinking of the
radius. No characteristic-flow regularity or tame estimate is assumed. -/
theorem n01_exists_commonSpeed_towers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01PartB D S C base' ε' ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
        r ∈ Icc (C.left m) (C.right m) →
          0 < twoRootDivided (componentOpticalSquare D S C m z)
            (C.left m) (C.right m) r) ∧
      Nonempty (∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
        (componentCosineSpeed D S C m)) ∧
      Nonempty (OrdinarySpeedRadialTowers D S C (stateNeighborhood S C base' ε')) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  exact n01c_commonSpeed_with_radii
    (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
    (jointStateGrading_hasInterpolation hS) base hε
    (fun b e hb he => n01PartB_mono hB hb he)
    (n01_exists_stateOpticalRoot_endpoint_powerBounds hS hT hA hE hG.1 hG.2.2)
    (n01_exists_componentOpticalQuotient_positive hS hT hA hG)
    (fun b e e' he => n01c_commonSpeed_forall_mono
      (stateNeighborhood_subset (S := S) (C := C) (base := b) le_rfl he))
    (fun b loss e he he2 hB' hpos hI hroot => by
      let G := Classical.choice hroot.1
      let F := wholeCharacteristicSpeed_powerControl
        hS hT hA he (he2.trans (by norm_num)) hB' hE hG.1 hG.2.1 hI G hroot.2
      exact ⟨⟨fun m => componentCosineSpeed_continuousTimeSpeedTower
        hS hT hA he he2 hB' hE hG.1 hG.2.1 hI G hroot.2 hpos m⟩,
        ⟨minusCharacteristicSpeed_radialJointSmoothDirections
          hS hT hA he2 hB' hE hpos F⟩⟩)

/-- The cosine-only interface is a projection of the common construction. -/
theorem n01_exists_componentCosineSpeed_towers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01PartB D S C base' ε' ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
        r ∈ Icc (C.left m) (C.right m) →
          0 < twoRootDivided (componentOpticalSquare D S C m z)
            (C.left m) (C.right m) r) ∧
      Nonempty (∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
        (componentCosineSpeed D S C m)) := by
  exact n01c_commonSpeed_project (n01_exists_commonSpeed_towers hS hT hA hε hB hG hE)

/-- After the single choice, every stronger base and smaller positive
radius inherits the same actual towers and endpoint quotient positivity. -/
theorem n01_exists_stable_componentCosineSpeed_towers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ, base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ ε ∧
      ∀ base' : ℕ, base₀ ≤ base' → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
        N01PartB D S C base' ε' ∧
        (∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
          r ∈ Icc (C.left m) (C.right m) →
            0 < twoRootDivided (componentOpticalSquare D S C m z)
              (C.left m) (C.right m) r) ∧
        Nonempty (∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
          (componentCosineSpeed D S C m)) := by
  exact n01c_commonSpeed_stabilize
    (n01_exists_componentCosineSpeed_towers hS hT hA hε hB hG hE)
    (fun b e b' e' hb he hB' => n01PartB_mono hB' hb he)
    (fun b e b' e' hb he => n01c_commonSpeed_forall_mono
      (stateNeighborhood_subset (S := S) (C := C) hb he))
    (fun b e b' e' hb he => n01c_commonSpeed_timeTowers_restrict
      (isOpen_stateNeighborhood S C b' e') (stateNeighborhood_subset hb he))

/-- Both kinds of actual speed tower persist on every subsequent
stronger-base, smaller-radius state neighbourhood. -/
theorem n01_exists_stable_commonSpeed_towers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ, base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ ε ∧
      ∀ base' : ℕ, base₀ ≤ base' → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
        N01PartB D S C base' ε' ∧
        (∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
          r ∈ Icc (C.left m) (C.right m) →
            0 < twoRootDivided (componentOpticalSquare D S C m z)
              (C.left m) (C.right m) r) ∧
        Nonempty (∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
          (componentCosineSpeed D S C m)) ∧
        Nonempty (OrdinarySpeedRadialTowers D S C (stateNeighborhood S C base' ε')) := by
  exact n01c_commonSpeed_stabilize
    (n01_exists_commonSpeed_towers hS hT hA hε hB hG hE)
    (fun b e b' e' hb he hB' => n01PartB_mono hB' hb he)
    (fun b e b' e' hb he => n01c_commonSpeed_forall_mono
      (stateNeighborhood_subset (S := S) (C := C) hb he))
    (fun b e b' e' hb he => And.imp
      (n01c_commonSpeed_timeTowers_restrict
        (isOpen_stateNeighborhood S C b' e') (stateNeighborhood_subset hb he))
      (n01c_commonSpeed_radialTowers_restrict
        (isOpen_stateNeighborhood S C b' e') (stateNeighborhood_subset hb he)))

end ContinuousFlexibility.Blueprint
