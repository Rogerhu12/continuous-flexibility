import ContinuousFlexibility.Analysis.N06PrimitivePrincipalReflection
import ContinuousFlexibility.Analysis.N06WeightedHeight
import ContinuousFlexibility.Analysis.N06CubicDifferential

/-!
# The actual principal source and its continuous test functionals

Five genuine weak jets define the source on each positive piece.  Its
compact pairing depends only on the original N05 inverse height.  Test
separation therefore proves linearity without assuming that the chosen
weak derivative representatives depend continuously on the input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Statements CanonicalGeometry
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}

local instance n06PrincipalSourceLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06PrincipalSourceLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _
local instance n06PrincipalSourceUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n06PrincipalSourceUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n06PrincipalSourceGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06PrincipalSourceGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

abbrev N06PrimitiveReferenceJetFamily (B : CanonicalDomainData S K V b) :=
  ∀ (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ), K.positive m = true →
    N06PrimitivePositiveJets (n07aReferenceInverseField (B := B) F m)

def n06PrimitiveReferenceJets
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (href : ReferenceJets D T S C L K) (hprincipal : ReferencePrincipal T S C K) :
    N06PrimitiveReferenceJetFamily B :=
  fun F m hm => Classical.choice
    (n06_primitiveReferenceInverse_positiveJets_nonempty
      hS h01 h03 h04 h05 href hprincipal F m hm)

def n06PrimitivePrincipalTest
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (φ : PolarPoint → ℝ) : PolarPoint → ℝ :=
  if K.positive m = true then
    divergenceOperator
      ⟨((n07aCurrentOpenCoefficient href hcur z hz m (hI m) 0).sub
          (n07aReferenceOpenCoefficient href m (hI m) 0)).value,
        ((n07aCurrentOpenCoefficient href hcur z hz m (hI m) 1).sub
          (n07aReferenceOpenCoefficient href m (hI m) 1)).value,
        ((n07aCurrentOpenCoefficient href hcur z hz m (hI m) 2).sub
          (n07aReferenceOpenCoefficient href m (hI m) 2)).value⟩ φ
  else fun _ => 0

theorem n06PrimitivePrincipalTest_memLp
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    MemLp (n06PrimitivePrincipalTest href hcur hI z hz m φ) 2
      (canonicalMeasure S K m) := by
  by_cases hm : K.positive m = true
  · let a := (n07aCurrentOpenCoefficient href hcur z hz m (hI m) 0).sub
      (n07aReferenceOpenCoefficient href m (hI m) 0)
    let beta := (n07aCurrentOpenCoefficient href hcur z hz m (hI m) 1).sub
      (n07aReferenceOpenCoefficient href m (hI m) 1)
    let c := (n07aCurrentOpenCoefficient href hcur z hz m (hI m) 2).sub
      (n07aReferenceOpenCoefficient href m (hI m) 2)
    rw [n06PrimitivePrincipalTest, if_pos hm]
    exact n07a_canonicalTest_memLp (n07a_canonicalTest_divergence
      ⟨a.value, beta.value, c.value⟩ a.smooth beta.smooth c.smooth
      a.periodic beta.periodic c.periodic hφ)
  · rw [n06PrimitivePrincipalTest, if_neg hm]
    exact MemLp.zero

theorem n06PrimitivePrincipalTest_eq_actualCubic
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    {m : ℕ} (hm : K.positive m = true) (φ : PolarPoint → ℝ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    n06PrimitivePrincipalTest href hcur hI z hz m φ p =
      divergenceOperator
        (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
          (K.dividedDifference (liftSectorParameter S C z) m).a
          (K.dividedDifference (liftSectorParameter S C z) m).b
          (K.dividedDifference (liftSectorParameter S C z) m).c) φ p := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl
  have hs' := h01.2.2.1.liftSectorParameter_sector z
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ canonicalOpen S K m :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hcube := hnear.mono (fun q hq =>
    h04.2.1.2.2.2.2 (liftSectorParameter S C z) hz' hs' m hm q hq)
  rw [n06PrimitivePrincipalTest, if_pos hm]
  apply n06_divergenceOperator_congr_germ φ
  · exact hcube.mono fun _ h => h.1
  · exact hcube.mono fun _ h => h.2.1
  · exact hcube.mono fun _ h => h.2.2

def n06PrimitivePrincipalSource
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) : CanonicalSequence S K :=
  fun m => if hm : K.positive m = true then
    let jets := J F m hm
    n07aRelativePrincipalJet href hcur z hz m (hI m)
      jets.radial jets.angular jets.secondRadial jets.radialAngular jets.angularAngular
  else 0

theorem n06PrimitivePrincipalSource_positive
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.positive m = true) :
    n06PrimitivePrincipalSource href hcur hI J z hz F m =
      n07aRelativePrincipalJet href hcur z hz m (hI m)
        (J F m hm).radial (J F m hm).angular (J F m hm).secondRadial
        (J F m hm).radialAngular (J F m hm).angularAngular := by
  simp only [n06PrimitivePrincipalSource, dif_pos hm]

theorem n06PrimitivePrincipalSource_negative
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.positive m ≠ true) :
    n06PrimitivePrincipalSource href hcur hI J z hz F m = 0 := by
  simp only [n06PrimitivePrincipalSource, dif_neg hm]

theorem n06PrimitivePrincipalSource_pairing
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, n06PrimitivePrincipalSource href hcur hI J z hz F m p * φ p
      ∂canonicalMeasure S K m) =
      ∫ p, n06InverseCanonicalHeight B F m p *
        n06PrimitivePrincipalTest href hcur hI z hz m φ p ∂canonicalMeasure S K m := by
  by_cases hm : K.positive m = true
  · rw [n06PrimitivePrincipalSource_positive href hcur hI J z hz F m hm,
      n06PrimitivePrincipalTest, if_pos hm, n06InverseCanonicalHeight_apply]
    exact (n07aOpenDivergence_distribution _ _ _
      (J F m hm).radial_weak (J F m hm).angular_weak
      (J F m hm).secondRadial_weak (J F m hm).radialAngular_weak
      (J F m hm).angularAngular_weak φ hφ).symm
  · rw [← n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ),
      n06PrimitivePrincipalSource_negative href hcur hI J z hz F m hm, map_zero,
      n06PrimitivePrincipalTest, if_neg hm]
    simp only [mul_zero, integral_zero]

def n06PrimitivePrincipalTestPairing
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ) :
    V.level (3 / 4 : ℝ) 0 b →L[ℝ] ℝ :=
  (n07aCanonicalTestPairing (n06PrimitivePrincipalTest href hcur hI z hz m φ)
    (n06PrimitivePrincipalTest_memLp href hcur hI z hz m hφ)).comp
      ((lp.evalCLM ℝ (fun n => CanonicalL2 S K n) 2 m).comp (n06InverseHeightLp B))

theorem n06PrimitivePrincipalTestPairing_apply
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    n06PrimitivePrincipalTestPairing (B := B) href hcur hI z hz m φ hφ F =
      ∫ p, n06InverseCanonicalHeight B F m p *
        n06PrimitivePrincipalTest href hcur hI z hz m φ p ∂canonicalMeasure S K m := by
  change n07aCanonicalTestPairing (n06PrimitivePrincipalTest href hcur hI z hz m φ)
    (n06PrimitivePrincipalTest_memLp href hcur hI z hz m hφ)
      (n06InverseHeightLp B F m) = _
  rw [n07aCanonicalTestPairing_apply, n06InverseHeightLp_apply,
    n06InverseCanonicalHeight_apply]

theorem n06PrimitivePrincipalSource_pairingCLM
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ)
    (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ) :
    n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ)
      (n06PrimitivePrincipalSource href hcur hI J z hz F m) =
        n06PrimitivePrincipalTestPairing (B := B) href hcur hI z hz m φ hφ F := by
  rw [n07aCanonicalTestPairing_apply, n06PrimitivePrincipalTestPairing_apply]
  exact n06PrimitivePrincipalSource_pairing href hcur hI J z hz F m hφ

def n06PrimitivePrincipalSourceLinear
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) :
    V.level (3 / 4 : ℝ) 0 b →ₗ[ℝ] CanonicalSequence S K where
  toFun := n06PrimitivePrincipalSource href hcur hI J z hz
  map_add' F G := by
    funext m
    apply n06_canonicalL2_test_ext
    intro φ hφ
    change (∫ p, n06PrimitivePrincipalSource href hcur hI J z hz (F + G) m p * φ p
      ∂canonicalMeasure S K m) =
      ∫ p, (n06PrimitivePrincipalSource href hcur hI J z hz F m +
        n06PrimitivePrincipalSource href hcur hI J z hz G m) p * φ p
        ∂canonicalMeasure S K m
    let P := n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ)
    let Q := n06PrimitivePrincipalTestPairing (B := B) href hcur hI z hz m φ hφ
    have hpair (X : V.level (3 / 4 : ℝ) 0 b) :
        P (n06PrimitivePrincipalSource href hcur hI J z hz X m) = Q X :=
      n06PrimitivePrincipalSource_pairingCLM href hcur hI J z hz X m φ hφ
    calc
      _ = P (n06PrimitivePrincipalSource href hcur hI J z hz (F + G) m) :=
        (n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ) _).symm
      _ = Q (F + G) := hpair (F + G)
      _ = Q F + Q G := Q.map_add F G
      _ = P (n06PrimitivePrincipalSource href hcur hI J z hz F m) +
          P (n06PrimitivePrincipalSource href hcur hI J z hz G m) :=
        congrArg₂ (fun x y : ℝ => x + y) (hpair F).symm (hpair G).symm
      _ = P (n06PrimitivePrincipalSource href hcur hI J z hz F m +
          n06PrimitivePrincipalSource href hcur hI J z hz G m) := (P.map_add _ _).symm
      _ = _ := n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ) _
  map_smul' c F := by
    funext m
    apply n06_canonicalL2_test_ext
    intro φ hφ
    change (∫ p, n06PrimitivePrincipalSource href hcur hI J z hz (c • F) m p * φ p
      ∂canonicalMeasure S K m) =
      ∫ p, (c • n06PrimitivePrincipalSource href hcur hI J z hz F m) p * φ p
        ∂canonicalMeasure S K m
    let P := n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ)
    let Q := n06PrimitivePrincipalTestPairing (B := B) href hcur hI z hz m φ hφ
    have hpair (X : V.level (3 / 4 : ℝ) 0 b) :
        P (n06PrimitivePrincipalSource href hcur hI J z hz X m) = Q X :=
      n06PrimitivePrincipalSource_pairingCLM href hcur hI J z hz X m φ hφ
    calc
      _ = P (n06PrimitivePrincipalSource href hcur hI J z hz (c • F) m) :=
        (n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ) _).symm
      _ = Q (c • F) := hpair (c • F)
      _ = c • Q F := Q.map_smul c F
      _ = c • P (n06PrimitivePrincipalSource href hcur hI J z hz F m) :=
        congrArg (fun x : ℝ => c • x) (hpair F).symm
      _ = P (c • n06PrimitivePrincipalSource href hcur hI J z hz F m) :=
        (P.map_smul c _).symm
      _ = _ := n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ) _

theorem n06PrimitivePrincipalSource_reflection
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    n07aAngularReflection m (n06PrimitivePrincipalSource href hcur hI J z hz F m) =
      n06PrimitivePrincipalSource href hcur hI J z hz F m := by
  by_cases hm : K.positive m = true
  · rw [n06PrimitivePrincipalSource_positive href hcur hI J z hz F m hm]
    exact n06_primitivePrincipalJet_reflection hT hS h01 h03 h04 h05
      href hcur z hz F m hm (hI m) (J F m hm)
  · rw [n06PrimitivePrincipalSource_negative href hcur hI J z hz F m hm, map_zero]

end ContinuousFlexibility.Analysis
