import ContinuousFlexibility.Analysis.N06PrimitivePrincipalWeightedBudget
import ContinuousFlexibility.Analysis.N07aAngularSequenceBandLift
import ContinuousFlexibility.Analysis.N07aVolumeLinearLift

/-!
# Every actual principal block belongs to the original source level

The graph consists of the genuine weak angular derivatives and the
original even reflection.  A single outer L2 majorant supplies all of its
coordinates.  No a priori bounded relative operator is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/- Eliminate witnesses only while the motive is an arbitrary proposition. -/
private theorem n06_bandLift_bind
    {X : Type*} (P : X → Prop) (Q : Prop)
    (h : ∃ x, P x) (hnext : ∀ x, P x → Q) : Q :=
  h.elim hnext

private theorem n06_bandLift_map_uniform
    {X Y : Type*} (A : Y → Prop) (P Q : X → Y → Prop)
    (h : ∃ x, ∃ y, A y ∧ P x y) (hmap : ∀ x y, P x y → Q x y) :
    ∃ x, ∃ y, A y ∧ Q x y :=
  h.elim (fun x hx => hx.elim (fun y hy => ⟨x, y, hy.1, hmap x y hy.2⟩))

private theorem n06_bandLift_transport_bound
    {X : Type*} (P : X → Prop) (n : X → ℝ) (u v : ℝ) (huv : u = v)
    (h : ∃ x, P x ∧ n x ≤ u) : ∃ x, P x ∧ n x ≤ v :=
  huv ▸ h

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}

local instance n06BandLiftLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06BandLiftLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

/- The band lift itself only sees a canonical sequence and an outer majorant. -/
set_option diagnostics true in
private theorem n06_bandLift_of_majorant
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m) (l : ℕ)
    (f : CanonicalSequence S K) (hf : ∀ m, n07aAngularReflection m (f m) = f m)
    (a : lp (fun _ : ℕ => ℝ) 2) (ha : ∀ m, 0 ≤ a m)
    (κ M : ℝ) (hκ : 0 ≤ κ) (hanorm : ‖a‖ ≤ M)
    (hpiece : ∀ m, (n07aVolumeWeight T K (3 / 4 : ℝ) 0 m)⁻¹ *
      Real.sqrt (n07aAngularJetWeightSq b l) *
      ‖n07aAngularBand m (hI m) l (f m)‖ ≤ κ * a m) :
    ∃ G : V.level (3 / 4 : ℝ) 0 b,
      V.forget (3 / 4 : ℝ) 0 b G = n07aAngularSequenceBand hI l f ∧
      ‖G‖ ≤ κ * M := by
  let v : lp (fun _ : ℕ => ℝ) 2 := κ • a
  have hv (m : ℕ) : ‖v m‖ = κ * a m := by
    simp only [v, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hκ (ha m))]
  have hbound (m : ℕ) : (n07aVolumeWeight T K (3 / 4 : ℝ) 0 m)⁻¹ *
      Real.sqrt (n07aAngularJetWeightSq b l) *
      ‖n07aAngularBand m (hI m) l (f m)‖ ≤ ‖v m‖ := by
    rw [hv]
    exact hpiece m
  let G : V.level (3 / 4 : ℝ) 0 b :=
    n07aAngularSequenceBandLift hD hT hV (3 / 4 : ℝ) 0 hI b l f hf v hbound
  refine ⟨G, n07aAngularSequenceBandLift_forget hD hT hV
    (3 / 4 : ℝ) 0 hI b l f hf v hbound, ?_⟩
  calc
    ‖G‖ ≤ ‖v‖ := n07aAngularSequenceBandLift_norm_le hD hT hV
      (3 / 4 : ℝ) 0 hI b l f hf v hbound
    _ = κ * ‖a‖ := by rw [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg hκ]
    _ ≤ κ * M := mul_le_mul_of_nonneg_left hanorm hκ

private theorem n06_bandLift_bound_reassociate (A ρ τ x : ℝ) :
    (ρ * τ) * (A * x) = A * ρ * τ * x := by
  ring

/- Keep the dependent actual-source payload behind named predicates while
selecting the uniform constants and the individual outer majorants. -/
private def N06BandLiftMajorantBudget
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ) (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (j : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) (a : lp (fun _ : ℕ => ℝ) 2) : Prop :=
  (∀ m, 0 ≤ a m) ∧ ‖a‖ ≤ A * ‖F‖ ∧
    ∀ m l, (n07aVolumeWeight T K (3 / 4 : ℝ) 0 m)⁻¹ *
      Real.sqrt (n07aAngularJetWeightSq b l) *
      ‖n07aAngularBand m (hI m) l
        (n06PrimitivePrincipalSource href hcur hI J z hz F m)‖ ≤
      parameterGrading S N z * n07aAngularTail ((j : ℤ) - l) * a m

private def N06BandLiftWeightedBudget
    (hV : IsVolumeModel T S K V)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ) : Prop :=
  ∀ z (hz : z ∈ sectorNeighborhood S base ε ε) j
    (F : V.level (3 / 4 : ℝ) 0 b),
    n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b j F = F →
    ∃ a : lp (fun _ : ℕ => ℝ) 2, N06BandLiftMajorantBudget href hcur hI J N A z hz j F a

private def N06BandLiftBlock
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ) (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (j l : ℕ) (F : V.level (3 / 4 : ℝ) 0 b) : Prop :=
  ∃ G : V.level (3 / 4 : ℝ) 0 b,
    V.forget (3 / 4 : ℝ) 0 b G = n07aAngularSequenceBand hI l
      (n06PrimitivePrincipalSource href hcur hI J z hz F) ∧
    ‖G‖ ≤ A * parameterGrading S N z * n07aAngularTail ((j : ℤ) - l) * ‖F‖

private def N06BandLiftEstimate
    (hV : IsVolumeModel T S K V)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ) : Prop :=
  ∀ z (hz : z ∈ sectorNeighborhood S base ε ε) j l
    (F : V.level (3 / 4 : ℝ) 0 b),
    n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b j F = F →
    N06BandLiftBlock href hcur hI J N A z hz j l F

set_option diagnostics true in
private theorem n06_bandLift_actual_pointwise
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ) (z : StateDirections S × ℝ)
    (hz : z ∈ sectorNeighborhood S base ε ε)
    (j l : ℕ) (F : V.level (3 / 4 : ℝ) 0 b)
    (a : lp (fun _ : ℕ => ℝ) 2) (ha : ∀ m, 0 ≤ a m)
    (hanorm : ‖a‖ ≤ A * ‖F‖)
    (hpiece : ∀ m, (n07aVolumeWeight T K (3 / 4 : ℝ) 0 m)⁻¹ *
      Real.sqrt (n07aAngularJetWeightSq b l) *
      ‖n07aAngularBand m (hI m) l
        (n06PrimitivePrincipalSource href hcur hI J z hz F m)‖ ≤
      parameterGrading S N z * n07aAngularTail ((j : ℤ) - l) * a m) :
    N06BandLiftBlock href hcur hI J N A z hz j l F := by
  have hreflect (m : ℕ) : n07aAngularReflection m
      (n06PrimitivePrincipalSource href hcur hI J z hz F m) =
      n06PrimitivePrincipalSource href hcur hI J z hz F m :=
    n06PrimitivePrincipalSource_reflection hT hS h01 h03 h04 h05
      href hcur hI J z hz F m
  have hρ : 0 ≤ parameterGrading S N z := apply_nonneg _ _
  exact n06_bandLift_transport_bound
    (fun G : V.level (3 / 4 : ℝ) 0 b =>
      V.forget (3 / 4 : ℝ) 0 b G = n07aAngularSequenceBand hI l
        (n06PrimitivePrincipalSource href hcur hI J z hz F))
    (fun G : V.level (3 / 4 : ℝ) 0 b => ‖G‖)
    ((parameterGrading S N z * n07aAngularTail ((j : ℤ) - l)) * (A * ‖F‖))
    (A * parameterGrading S N z * n07aAngularTail ((j : ℤ) - l) * ‖F‖)
    (n06_bandLift_bound_reassociate A (parameterGrading S N z)
      (n07aAngularTail ((j : ℤ) - l)) ‖F‖)
    (n06_bandLift_of_majorant (D := D) (T := T) (S := S) (K := K) (V := V) (b := b)
      h01.1.1 hT h05.2.1 hI l
      (n06PrimitivePrincipalSource href hcur hI J z hz F) hreflect a ha
      (parameterGrading S N z * n07aAngularTail ((j : ℤ) - l)) (A * ‖F‖)
      (mul_nonneg hρ (n07aAngularTail_nonneg _)) hanorm hpiece)

set_option diagnostics true in
private theorem n06_bandLift_fixed_budget
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ)
    (hbudget : N06BandLiftWeightedBudget h05.2.1 href hcur hI J N A) :
    N06BandLiftEstimate h05.2.1 href hcur hI J N A := by
  intro z hz j l F hF
  exact n06_bandLift_bind
    (N06BandLiftMajorantBudget (B := B) href hcur hI J N A z hz j F)
    (N06BandLiftBlock (B := B) href hcur hI J N A z hz j l F)
    (hbudget z hz j F hF)
    (fun a ha => n06_bandLift_actual_pointwise
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε)
      hT hS h01 h03 h04 h05 href hcur hI J
      N A z hz j l F a ha.1 ha.2.1 (fun m => ha.2.2 m l))

set_option diagnostics true in
private theorem n06_bandLift_weighted_budget
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      N06BandLiftWeightedBudget h.2.2.1 href hcur hI J N A := by
  exact n06_primitivePrincipal_weighted_budget
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
    (K := K) (V := V) (b := b) (B := B)
    (base := base) (loss := loss) (ε := ε)
    hT hS h href hcur hprincipal hR hAux hI J

set_option diagnostics true in
private theorem n06_bandLift_uniform
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ N06BandLiftEstimate h.2.2.1 href hcur hI J N A := by
  exact n06_bandLift_map_uniform
    (fun A : ℝ => 0 ≤ A)
    (N06BandLiftWeightedBudget (B := B) h.2.2.1 href hcur hI J)
    (N06BandLiftEstimate (B := B) h.2.2.1 href hcur hI J)
    (n06_bandLift_weighted_budget
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε)
      hT hS h href hcur hprincipal hR hAux hI J)
    (fun N A => n06_bandLift_fixed_budget
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε)
      hT hS h.1.1.1.1 h.1.1.2 h.1.2.2.2.2.1 h.2 href hcur hI J N A)

set_option diagnostics true in
theorem n06_primitivePrincipal_band_lift
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε) j l
        (F : V.level (3 / 4 : ℝ) 0 b),
      n07aAngularLevelBand h.2.2.1 (3 / 4 : ℝ) 0 hI b j F = F →
      ∃ G : V.level (3 / 4 : ℝ) 0 b,
        V.forget (3 / 4 : ℝ) 0 b G =
          n07aAngularSequenceBand hI l
            (n06PrimitivePrincipalSource href hcur hI J z hz F) ∧
        ‖G‖ ≤ A * parameterGrading S N z * n07aAngularTail ((j : ℤ) - l) * ‖F‖ := by
  exact n06_bandLift_uniform
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
    (K := K) (V := V) (b := b) (B := B)
    (base := base) (loss := loss) (ε := ε)
    hT hS h href hcur hprincipal hR hAux hI J

end ContinuousFlexibility.Analysis
