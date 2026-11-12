import ContinuousFlexibility.Analysis.N06PrimitivePrincipalBandLift
import ContinuousFlexibility.Analysis.N06CanonicalSourceSchur

/-!
# The actual principal relative operator on the same source space

The Schur construction realizes the genuine cubic principal difference
of the original N05 inverse.  Its source is identified on every input by
the original compact canonical tests.  The statement retains the given
K, V, b and B and does not use an N06 inverse or a pre-existing relative
operator bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Statements CanonicalGeometry

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}

local instance n06PrincipalOperatorLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06PrincipalOperatorLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

/-- Keep the source identity named while the fixed-state realization is
elaborated.  Its source is still the actual primitive source below. -/
private def n06PrincipalOperatorRealizes
    (f : V.level (3 / 4 : ℝ) 0 b → CanonicalSequence S K)
    (Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b) : Prop :=
  ∀ F, V.forget (3 / 4 : ℝ) 0 b (Mc F) = f F

private def n06PrincipalOperatorBlocks
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m)
    (f : V.level (3 / 4 : ℝ) 0 b →ₗ[ℝ] CanonicalSequence S K) (A : ℝ) : Prop :=
  ∀ j l (F : V.level (3 / 4 : ℝ) 0 b),
    n07aAngularLevelBand hV (3 / 4 : ℝ) 0 hI b j F = F →
    ∃ G : V.level (3 / 4 : ℝ) 0 b,
      V.forget (3 / 4 : ℝ) 0 b G = n07aAngularSequenceBand hI l (f F) ∧
      ‖G‖ ≤ A * n07aAngularTail ((j : ℤ) - l) * ‖F‖

private def n06PrincipalOperatorPositivePairing
    (B : CanonicalDomainData S K V b) (z : Parameter S)
    (Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b) : Prop :=
  ∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
    (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc F) m p * φ p
      ∂canonicalMeasure S K m) =
      ∫ p, (B.inverse F).val.1.1 m p *
        divergenceOperator
          (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
            (K.dividedDifference (liftSectorParameter S C z) m).a
            (K.dividedDifference (liftSectorParameter S C z) m).b
            (K.dividedDifference (liftSectorParameter S C z) m).c) φ p
          ∂canonicalMeasure S K m

private def n06PrincipalOperatorNegative
    (Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b) : Prop :=
  ∀ F m, K.positive m = false → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0

private def n06PrincipalOperatorBlockFamily
    (hV : IsVolumeModel T S K V)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ) : Prop :=
  ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
    n06PrincipalOperatorBlocks hV hI
      (n06PrimitivePrincipalSourceLinear href hcur hI J z hz)
      (A * parameterGrading S N z)

private def n06PrincipalOperatorSourceFamily
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ) : Prop :=
  ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
    ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ‖Mc‖ ≤ A * parameterGrading S N z ∧
      n06PrincipalOperatorRealizes (n06PrimitivePrincipalSource href hcur hI J z hz) Mc

private def n06PrincipalOperatorPhysicalFamily
    (B : CanonicalDomainData S K V b) (base : ℕ) (ε : ℝ) (N : ℕ) (A : ℝ) : Prop :=
  ∀ z (_hz : z ∈ sectorNeighborhood S base ε ε),
    ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ‖Mc‖ ≤ A * parameterGrading S N z ∧
      n06PrincipalOperatorPositivePairing (C := C) B z Mc ∧ n06PrincipalOperatorNegative Mc

/-- Existential payloads are transformed without elaborating their analytic
contents in the elimination motive. -/
private theorem n06PrincipalOperator_map_exists
    {X : Type*} (P Q : X → Prop) (h : ∃ x, P x)
    (hmap : ∀ x, P x → Q x) : ∃ x, Q x :=
  h.elim (fun x hx => ⟨x, hmap x hx⟩)

private theorem n06PrincipalOperator_bind_budget
    {X Y : Type*} (P : X → Y → Prop) (Goal : Prop)
    (h : ∃ x y, P x y) (hbind : ∀ x y, P x y → Goal) : Goal :=
  h.elim (fun x hx => hx.elim (fun y hxy => hbind x y hxy))

/-- Realize one actual state after the uniform block budget has been
selected. This helper does not select an order or alter the tail sum. -/
set_option diagnostics true in
private theorem n06PrincipalOperator_realize_state
    (hV : IsVolumeModel T S K V)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (N : ℕ) (A₀ : ℝ) (hA₀ : 0 ≤ A₀)
    (hblocks : n06PrincipalOperatorBlocks hV hI
      (n06PrimitivePrincipalSourceLinear href hcur hI J z hz)
      (A₀ * parameterGrading S N z)) :
    ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ‖Mc‖ ≤ (A₀ * ∑' k : ℤ, n07aAngularTail k) * parameterGrading S N z ∧
      n06PrincipalOperatorRealizes (n06PrimitivePrincipalSource href hcur hI J z hz) Mc := by
  let f : V.level (3 / 4 : ℝ) 0 b →ₗ[ℝ] CanonicalSequence S K :=
    n06PrimitivePrincipalSourceLinear href hcur hI J z hz
  let Q : ∀ m (φ : PolarPoint → ℝ),
      CanonicalTest S K m φ → V.level (3 / 4 : ℝ) 0 b →L[ℝ] ℝ :=
    n06PrimitivePrincipalTestPairing (B := B) href hcur hI z hz
  have hQ (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ)
      (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ) :
      n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ) (f F m) = Q m φ hφ F :=
    n06PrimitivePrincipalSource_pairingCLM href hcur hI J z hz F m φ hφ
  have hρ : 0 ≤ parameterGrading S N z := apply_nonneg _ _
  exact n06PrincipalOperator_map_exists
    (fun Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b =>
      ‖Mc‖ ≤ (A₀ * parameterGrading S N z) * (∑' k : ℤ, n07aAngularTail k) ∧
        n06PrincipalOperatorRealizes f Mc)
    (fun Mc => ‖Mc‖ ≤ (A₀ * ∑' k : ℤ, n07aAngularTail k) * parameterGrading S N z ∧
      n06PrincipalOperatorRealizes (n06PrimitivePrincipalSource href hcur hI J z hz) Mc)
    (n06_canonicalSource_schur
      (T := T) (S := S) (K := K) (V := V) (γ := (3 / 4 : ℝ)) (t := 0) (s := b)
      hV hI f Q hQ (A₀ * parameterGrading S N z) (mul_nonneg hA₀ hρ) hblocks)
    (fun Mc hMc => ⟨hMc.1.trans_eq (by ring), hMc.2⟩)

set_option diagnostics true in
private theorem n06PrincipalOperator_band_budget
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      n06PrincipalOperatorBlockFamily h.2.2.1 href hcur hI J N A := by
  exact n06_primitivePrincipal_band_lift
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
    (K := K) (V := V) (b := b) (B := B) (base := base) (loss := loss) (ε := ε)
    hT hS h href hcur hprincipal hR hAux hI J

set_option diagnostics true in
private theorem n06PrincipalOperator_uniform_realizes
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ n06PrincipalOperatorSourceFamily href hcur hI J N A := by
  exact n06PrincipalOperator_bind_budget
    (fun (N : ℕ) (A : ℝ) => 0 ≤ A ∧
      n06PrincipalOperatorBlockFamily h.2.2.1 href hcur hI J N A)
    (∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ n06PrincipalOperatorSourceFamily href hcur hI J N A)
    (n06PrincipalOperator_band_budget
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B) (base := base) (loss := loss) (ε := ε)
      hT hS h href hcur hprincipal hR hAux hI J)
    (fun N A hA => ⟨N, A * (∑' k : ℤ, n07aAngularTail k),
      mul_nonneg hA.1 (tsum_nonneg n07aAngularTail_nonneg), fun z hz =>
        n06PrincipalOperator_realize_state
          (D := D) (T := T) (S := S) (C := C) (L := L)
          (K := K) (V := V) (b := b) (B := B) (base := base) (ε := ε)
          h.2.2.1 href hcur hI J z hz N A hA.1 (hA.2 z hz)⟩)

set_option diagnostics true in
theorem n06_primitivePrincipal_operator_for_family
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖Mc‖ ≤ A * parameterGrading S N z ∧
        ∀ F, V.forget (3 / 4 : ℝ) 0 b (Mc F) =
          n06PrimitivePrincipalSource href hcur hI J z hz F := by
  exact n06PrincipalOperator_uniform_realizes
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
    (K := K) (V := V) (b := b) (B := B) (base := base) (loss := loss) (ε := ε)
    hT hS h href hcur hprincipal hR hAux hI J

/-- The positive compact-test equation is attached to the fixed source
identity, before it is placed inside the uniform operator existence. -/
set_option diagnostics true in
private theorem n06PrincipalOperator_positive_of_realizes
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hforget : n06PrincipalOperatorRealizes
      (n06PrimitivePrincipalSource href hcur hI J z hz) Mc) :
    n06PrincipalOperatorPositivePairing (C := C) B z Mc := by
  intro F m hm φ hφ
  have hsource : V.forget (3 / 4 : ℝ) 0 b (Mc F) m =
      n06PrimitivePrincipalSource href hcur hI J z hz F m :=
    congrFun (hforget F) m
  rw [hsource]
  calc
    _ = ∫ p, n06InverseCanonicalHeight B F m p *
        n06PrimitivePrincipalTest href hcur hI z hz m φ p ∂canonicalMeasure S K m :=
      n06PrimitivePrincipalSource_pairing href hcur hI J z hz F m hφ
    _ = _ := by
      rw [n06InverseCanonicalHeight_apply]
      apply integral_congr_ae
      filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
      rw [n06PrimitivePrincipalTest_eq_actualCubic h01 h04 href hcur hI z hz hm φ hp]

set_option diagnostics true in
private theorem n06PrincipalOperator_negative_of_realizes
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hforget : n06PrincipalOperatorRealizes
      (n06PrimitivePrincipalSource href hcur hI J z hz) Mc) :
    n06PrincipalOperatorNegative Mc := by
  intro F m hm
  have hsource : V.forget (3 / 4 : ℝ) 0 b (Mc F) m =
      n06PrimitivePrincipalSource href hcur hI J z hz F m :=
    congrFun (hforget F) m
  exact hsource.trans (n06PrimitivePrincipalSource_negative href hcur hI J z hz F m
    (by simp only [hm, Bool.false_eq_true, not_false_eq_true]))

/-- A fixed state's realization is mapped to its physical test properties;
the selected operator and its original norm estimate are retained. -/
set_option diagnostics true in
private theorem n06PrincipalOperator_physical_state
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (N : ℕ) (A : ℝ) (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hstate : ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ‖Mc‖ ≤ A * parameterGrading S N z ∧
      n06PrincipalOperatorRealizes (n06PrimitivePrincipalSource href hcur hI J z hz) Mc) :
    ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ‖Mc‖ ≤ A * parameterGrading S N z ∧
      n06PrincipalOperatorPositivePairing (C := C) B z Mc ∧ n06PrincipalOperatorNegative Mc := by
  exact n06PrincipalOperator_map_exists
    (fun Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b =>
      ‖Mc‖ ≤ A * parameterGrading S N z ∧
      n06PrincipalOperatorRealizes (n06PrimitivePrincipalSource href hcur hI J z hz) Mc)
    (fun Mc => ‖Mc‖ ≤ A * parameterGrading S N z ∧
      n06PrincipalOperatorPositivePairing (C := C) B z Mc ∧ n06PrincipalOperatorNegative Mc)
    hstate (fun Mc hMc => ⟨hMc.1,
      n06PrincipalOperator_positive_of_realizes
        (D := D) (T := T) (S := S) (C := C) (L := L)
        (K := K) (V := V) (b := b) (B := B) (base := base) (loss := loss) (ε := ε)
        h01 h04 href hcur hI J z hz Mc hMc.2,
      n06PrincipalOperator_negative_of_realizes
        (D := D) (T := T) (S := S) (C := C) (L := L)
        (K := K) (V := V) (b := b) (B := B) (base := base) (ε := ε)
        href hcur hI J z hz Mc hMc.2⟩)

set_option diagnostics true in
private theorem n06PrincipalOperator_uniform_physical
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (hmaps : ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ n06PrincipalOperatorSourceFamily href hcur hI J N A) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ n06PrincipalOperatorPhysicalFamily (C := C) B base ε N A := by
  exact n06PrincipalOperator_bind_budget
    (fun (N : ℕ) (A : ℝ) => 0 ≤ A ∧ n06PrincipalOperatorSourceFamily href hcur hI J N A)
    (∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ n06PrincipalOperatorPhysicalFamily (C := C) B base ε N A)
    hmaps (fun N A hA => ⟨N, A, hA.1, fun z hz =>
      n06PrincipalOperator_physical_state
        (D := D) (T := T) (S := S) (C := C) (L := L)
        (K := K) (V := V) (b := b) (B := B) (base := base) (loss := loss) (ε := ε)
        h01 h04 href hcur hI J N A z hz (hA.2 z hz)⟩)

set_option diagnostics true in
theorem n06_primitivePrincipal_operator
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hR : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K) :
    ∃ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∃ Mc : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖Mc‖ ≤ A * parameterGrading S N z ∧
        (∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc F) m p * φ p
            ∂canonicalMeasure S K m) =
            ∫ p, (B.inverse F).val.1.1 m p *
              divergenceOperator
                (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
                  (K.dividedDifference (liftSectorParameter S C z) m).a
                  (K.dividedDifference (liftSectorParameter S C z) m).b
                  (K.dividedDifference (liftSectorParameter S C z) m).c) φ p
                ∂canonicalMeasure S K m) ∧
        (∀ F m, K.positive m = false → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have h05 : N05Properties D T S C K V b B := h.2
  let hI : ∀ m, K.left m < K.right m := fun m => (h04.1.referenceBounds m).2.1
  let J : N06PrimitiveReferenceJetFamily B :=
    n06PrimitiveReferenceJets
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B) (base := base) (loss := loss) (ε := ε)
      hS h01 h03 h04 h05 href hprincipal
  exact n06PrincipalOperator_uniform_physical
    (D := D) (T := T) (S := S) (C := C) (L := L)
    (K := K) (V := V) (b := b) (B := B) (base := base) (loss := loss) (ε := ε)
    h01 h04 href hcur hI J
    (n06PrincipalOperator_uniform_realizes
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B) (base := base) (loss := loss) (ε := ε)
      hT hS h href hcur hprincipal hR hAux hI J)

end ContinuousFlexibility.Analysis
