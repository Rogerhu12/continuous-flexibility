import ContinuousFlexibility.Analysis.N07bReferenceAngularExpansion
import ContinuousFlexibility.Analysis.N07bFiniteMaterialJetEnergy
import ContinuousFlexibility.Analysis.N07bPiecewiseCanonicalEnergy
import ContinuousFlexibility.Analysis.N07bCanonicalAngularPullback
import ContinuousFlexibility.Analysis.N07bReferenceGeometry
import ContinuousFlexibility.Analysis.N07bReferencePieceRegularity

/-!
# Actual reference bulk forcing in the prescribed canonical source level

Reference and current physical points are compared through their shared
canonical coordinate. The actual reference forcing is differentiated using
the current inverse angular vector, so its square energy uses the current
Jacobian. Finite Cauchy--Schwarz gives one common material-jet majorant,
independent of the piece, whose physical order is `b + 3`.

The coefficient-square hypothesis is the source-independent conclusion of
the primitive geometric estimates. No bound or membership of the reference
forcing is assumed. Closed-piece extensions and symmetries are kept separate
from the energy argument when constructing the prescribed volume-model lift.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

abbrev n07bReferenceBulkIndex (j : ℕ) :=
  n07bReferenceMaterialSeed × n07bAngularChainIndex j

def n07bReferenceBulkRadial (j : ℕ) (i : n07bReferenceBulkIndex j) : ℕ :=
  n07bReferenceSeedRadial i.1 + n07bAngularChainRadial j i.2

def n07bReferenceBulkAngular (j : ℕ) (i : n07bReferenceBulkIndex j) : ℕ :=
  n07bReferenceSeedAngular i.1 + n07bAngularChainAngular j i.2

theorem n07b_referenceBulk_order (j : ℕ) (i : n07bReferenceBulkIndex j) :
    n07bReferenceBulkRadial j i + n07bReferenceBulkAngular j i ≤ 2 + j :=
  n07b_reference_material_expansion_order j i

theorem n07b_referenceBulk_card (j : ℕ) :
    Fintype.card (n07bReferenceBulkIndex j) = 21 * 3 ^ j := by
  rw [Fintype.card_prod, n07b_referenceMaterialSeed_card, n07b_angularChain_card]

/-- The coefficient of the actual reference transition and actual source
factor, after the current inverse angular derivatives. -/
def n07bReferenceBulkCoefficient (D : ReferenceData) (T : MaterialData)
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ) (j : ℕ)
    (i : n07bReferenceBulkIndex j) : PolarPoint → ℝ :=
  n07bReferenceAngularCoefficient T K z m β
    (n07bReferenceDirection (canonicalCurrentPoint C K z m)
      (canonicalReferencePoint C K z m) (1, 0))
    (n07bReferenceDirection (canonicalCurrentPoint C K z m)
      (canonicalReferencePoint C K z m) (0, 1))
    (canonicalReferenceHeightRatio C K z m)
    (n07bReferenceSeedMultiplier D.w (canonicalReferencePoint C K z m)
      (canonicalReferenceSourceFactor C K z m)) j i

/-- The single physical majorant, independent of the atlas and its labels. -/
def n07bReferenceBulkMajorant (T : MaterialData) (β : ℝ) (b : ℕ)
    (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  ∑ j : Fin (b + 1), (Fintype.card (n07bReferenceBulkIndex j.val) : ℝ) *
    n07bFiniteMaterialJetMajorant T β
      (n07bReferenceBulkRadial j.val) (n07bReferenceBulkAngular j.val) f x

def n07bReferenceBulkPathConstant (b : ℕ) : ℝ :=
  ∑ j : Fin (b + 1), (Fintype.card (n07bReferenceBulkIndex j.val) : ℝ) ^ 2

theorem n07bReferenceBulkPathConstant_nonneg (b : ℕ) :
    0 ≤ n07bReferenceBulkPathConstant b :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem n07bReferenceBulkMajorant_nonneg
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (β : ℝ) (b : ℕ) (f : PolarPoint → ℝ) {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) : 0 ≤ n07bReferenceBulkMajorant T β b f x := by
  unfold n07bReferenceBulkMajorant
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (n07bFiniteMaterialJetMajorant_nonneg hT β _ _ f hx))

theorem n07bReferenceBulkMajorant_integrable
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {β : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T β f) (b : ℕ) :
    IntegrableOn (n07bReferenceBulkMajorant T β b f)
      (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) := by
  unfold n07bReferenceBulkMajorant
  exact integrable_finsetSum Finset.univ (fun j _ =>
    (n07bFiniteMaterialJetMajorant_integrable hT hf
      (n07bReferenceBulkRadial j.val) (n07bReferenceBulkAngular j.val)).const_mul _)

/-- Two reference derivatives, `b` current angular derivatives and one
material weight give exactly the physical order `b + 3`. -/
theorem n07bReferenceBulkMajorant_integral_le
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {β : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T β f) (b : ℕ) :
    (∫ x in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi, n07bReferenceBulkMajorant T β b f x) ≤
      n07bReferenceBulkPathConstant b * physicalNorm T β (b + 3) f ^ 2 := by
  classical
  have hi (j : Fin (b + 1)) := n07bFiniteMaterialJetMajorant_integrable hT hf
    (n07bReferenceBulkRadial j.val) (n07bReferenceBulkAngular j.val)
  unfold n07bReferenceBulkMajorant
  rw [integral_finsetSum Finset.univ (fun j _ => (hi j).const_mul _)]
  calc
    _ = ∑ j : Fin (b + 1), (Fintype.card (n07bReferenceBulkIndex j.val) : ℝ) *
        ∫ x in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
          n07bFiniteMaterialJetMajorant T β
            (n07bReferenceBulkRadial j.val) (n07bReferenceBulkAngular j.val) f x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
    _ ≤ ∑ j : Fin (b + 1), (Fintype.card (n07bReferenceBulkIndex j.val) : ℝ) *
        ((Fintype.card (n07bReferenceBulkIndex j.val) : ℝ) *
          physicalNorm T β (b + 3) f ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact n07bFiniteMaterialJetMajorant_integral_le hT hf
        (n07bReferenceBulkRadial j.val) (n07bReferenceBulkAngular j.val) (b + 3)
        (fun i => by have ho := n07b_referenceBulk_order j.val i; omega) (Subset.rfl)
    _ = _ := by
      simp only [n07bReferenceBulkPathConstant, Finset.sum_mul, pow_two, mul_assoc]

section ActualReference

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}
  (hK : N04PartA D S C K base ε)
  (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
  (hsref : stateSector S C.referenceState)
  (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)

include hK href hsref hz hs

/-- The actual piece remainder is the geometric height ratio times the
current field, evaluated through the genuine reference-to-current map. -/
theorem n07bReferencePieceRemainder_eq_transition (m : ℕ) (f : PolarPoint → ℝ)
    {y : PolarPoint} (hy : y ∈ physicalPieceOpen S K (C.referenceState, 0) m) :
    n07bReferencePieceRemainder C K z m f y =
      canonicalReferenceHeightRatio C K z m (canonicalCurrentPoint C K z m y) *
        f (canonicalCurrentPoint C K z m y) := by
  rw [n07bReferencePieceRemainder_eq]
  change (K.height (C.referenceState, 0) m y /
      K.height z m (canonicalCurrentPoint C K z m y)) * f (canonicalCurrentPoint C K z m y) =
    (K.height (C.referenceState, 0) m
        (canonicalReferencePoint C K z m (canonicalCurrentPoint C K z m y)) /
      K.height z m (canonicalCurrentPoint C K z m y)) * f (canonicalCurrentPoint C K z m y)
  rw [n07b_canonicalReferencePoint_currentPoint hK href hsref hz hs m hy]

/-- Interior smoothness needs only the genuine physical height on the
annulus; it does not require any extension through the physical endpoints. -/
theorem n07bReferencePieceCanonicalSource_contDiffOn
    (hgeom : RadialProfileGeometry D) (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) :
    ContDiffOn ℝ ∞ (n07bReferencePieceCanonicalSource D C K z m f)
      (canonicalOpen S K m) := by
  have hU := (hK.domains z hz hs m).1
  have hV := (hK.domains (C.referenceState, 0) href hsref m).1
  have hcore := (hK.domains z hz hs m).2.2.1
  have hc := n07b_canonicalReferenceHeightRatio_contDiffOn hK href hsref hz hs m
  have hτ := n07b_canonicalCurrentPoint_contDiffOn hK href hsref hz hs m
  have hτmap := n07b_canonicalCurrentPoint_mapsTo hK href hsref hz hs m
  have hprod : ContDiffOn ℝ ∞ (fun y =>
      canonicalReferenceHeightRatio C K z m (canonicalCurrentPoint C K z m y) *
        f (canonicalCurrentPoint C K z m y))
      (physicalPieceOpen S K (C.referenceState, 0) m) :=
    (hc.mul (hf.mono hcore)).comp hτ hτmap
  have hrem : ContDiffOn ℝ ∞ (n07bReferencePieceRemainder C K z m f)
      (physicalPieceOpen S K (C.referenceState, 0) m) := by
    intro y hy
    have heq : n07bReferencePieceRemainder C K z m f =ᶠ[𝓝 y]
        (fun q => canonicalReferenceHeightRatio C K z m (canonicalCurrentPoint C K z m q) *
          f (canonicalCurrentPoint C K z m q)) := by
      filter_upwards [hV.mem_nhds hy] with q hq
      exact n07bReferencePieceRemainder_eq_transition hK href hsref hz hs m f hq
    exact ((hprod.contDiffAt (hV.mem_nhds hy)).congr_of_eventuallyEq heq).contDiffWithinAt
  apply n07b_contDiffOn_canonicalSource_of_open hK href hsref m
  intro y hy
  exact (n07b_contDiffAt_referencePDE hgeom
    (hrem.contDiffAt (hV.mem_nhds hy))).contDiffWithinAt

/-- The canonical reference forcing is evaluated at the *current* chart,
and therefore at the reference point with the same canonical coordinate. -/
theorem n07bReferencePieceCanonicalSource_currentPullback (m : ℕ) (f : PolarPoint → ℝ) :
    EqOn (n07bReferencePieceCanonicalSource D C K z m f ∘ K.chart z m)
      (fun x => canonicalReferenceSourceFactor C K z m x *
        radialPDE D.w (fun r θ =>
          canonicalReferenceHeightRatio C K z m (canonicalCurrentPoint C K z m (r, θ)) *
            f (canonicalCurrentPoint C K z m (r, θ)))
          (canonicalReferencePoint C K z m x).1 (canonicalReferencePoint C K z m x).2)
      (physicalPieceOpen S K z m) := by
  have hpde := n07b_radialPDE_eqOn_of_isOpen D.w
    (hK.domains (C.referenceState, 0) href hsref m).1
    (fun y hy => n07bReferencePieceRemainder_eq_transition hK href hsref hz hs m f hy)
  intro x hx
  have hy := n07b_canonicalReferencePoint_mapsTo hK href hsref hz hs m hx
  have hpdePoint := hpde hy
  dsimp only at hpdePoint
  change K.height (C.referenceState, 0) m (canonicalReferencePoint C K z m x) *
      radialPDE D.w (fun r θ => n07bReferencePieceRemainder C K z m f (r, θ))
        (canonicalReferencePoint C K z m x).1 (canonicalReferencePoint C K z m x).2 /
      |planeJacobian (K.chart (C.referenceState, 0) m) (canonicalReferencePoint C K z m x)| = _
  rw [hpdePoint]
  unfold canonicalReferenceSourceFactor
  ring

/-- The actual angular jets of the reference canonical source have the
finite expansion with precisely the coefficients already estimated. -/
theorem n07b_referenceBulk_angularJet_expansion
    (hT : IsMaterialData D T) (hgeom : RadialProfileGeometry D)
    (m : ℕ) (β : ℝ) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (j : ℕ)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) :
    mixedDerivative 0 j (n07bReferencePieceCanonicalSource D C K z m f) (K.chart z m x) =
      T.H x.1 ^ β * ∑ i : n07bReferenceBulkIndex j,
        n07bReferenceBulkCoefficient D T C K z m β j i x *
          mixedDerivative (n07bReferenceBulkRadial j i) (n07bReferenceBulkAngular j i)
            (materialPullback T β f) (n07bMaterialChart T x) := by
  have hjet := n07b_canonicalAngularJet_eq_directionChain hK hz hs m
    (n07bReferencePieceCanonicalSource_contDiffOn hK href hsref hz hs hgeom m hf)
    (n07bReferencePieceCanonicalSource_currentPullback hK href hsref hz hs m f) j hx
  have hΘmap := n07b_canonicalReferencePoint_mapsTo hK href hsref hz hs m
  have hne : ∀ p ∈ physicalPieceOpen S K z m, (canonicalReferencePoint C K z m p).1 ≠ 0 := by
    intro p hp
    have hr := ((hK.domains (C.referenceState, 0) href hsref m).2.2.1 (hΘmap hp)).1
    exact (hgeom.1.trans hr.1).ne'
  exact hjet.trans (n07b_referencePDE_currentAngular_material_expansion
    hT hK hz hs m (hK.domains (C.referenceState, 0) href hsref m).1
    (n07b_canonicalCurrentPoint_contDiffOn hK href hsref hz hs m)
    (n07b_canonicalReferencePoint_contDiffOn hK href hsref hz hs m)
    (n07b_canonicalCurrentPoint_mapsTo hK href hsref hz hs m) hΘmap
    (fun y hy => n07b_canonicalReferencePoint_currentPoint hK href hsref hz hs m hy)
    (fun p hp => n07b_canonicalCurrentPoint_referencePoint hK href hsref hz hs m hp) β
    (n07b_canonicalReferenceHeightRatio_contDiffOn hK href hsref hz hs m) hf
    (n07b_canonicalReferenceSourceFactor_contDiffOn hK href hsref hz hs m)
    hgeom.2.2.1.1 hne j hx)

/-- The exact pointwise density bound. The coefficient hypothesis is
the previously derived geometric estimate, not a forcing estimate. -/
theorem n07b_referenceBulk_density_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (β : ℝ) {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (b m : ℕ) {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) {A : ℝ}
    (hcoeff : ∀ j : Fin (b + 1), ∀ i : n07bReferenceBulkIndex j.val,
      (n07bSourceNormalizer T K z m β x * n07bReferenceBulkCoefficient D T C K z m β j.val i x) ^ 2 ≤
        A * T.M x.1 ^ 2) :
    n07bPiecewiseCanonicalDensity T K z (fun m => n07bReferencePieceCanonicalSource D C K z m f)
      β 0 b m x ≤ A * n07bReferenceBulkMajorant T β b f x := by
  classical
  have hxcore := ((hK.domains z hz hs m).2.2.1 hx).1
  have hsample : 0 < T.H (T.sample (K.cell m)) := by
    simpa only [n07bCanonicalSourceFactor, neg_zero, Real.rpow_zero,
      Real.rpow_one, one_mul] using
        (n07bCanonicalSourceFactor_pos_of_material (K := K) hD hT 1 0 m)
  have hfactor : n07bCanonicalSourceFactor T K β 0 m = T.H (T.sample (K.cell m)) ^ β := by
    simp only [n07bCanonicalSourceFactor, neg_zero, Real.rpow_zero, one_mul]
  unfold n07bPiecewiseCanonicalDensity n07bReferenceBulkMajorant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [n07b_referenceBulk_angularJet_expansion hK href hsref hz hs hT hD.choose_spec.1 m β hf j.val hx]
  have hfin := n07b_finite_materialJet_energy_le_of_normalized hT β
    (n07bReferenceBulkRadial j.val) (n07bReferenceBulkAngular j.val)
    (n07bReferenceBulkCoefficient D T C K z m β j.val) f hxcore hsample
    (fun i => by
      change (n07bSourceNormalizer T K z m β x *
        n07bReferenceBulkCoefficient D T C K z m β j.val i x) ^ 2 ≤ A * T.M x.1 ^ 2
      exact hcoeff j i)
  simpa only [hfactor, n07bMaterialChart, n07bFiniteMaterialJetMajorant,
    mul_assoc, mul_left_comm] using hfin

/-- All actual canonical angular energies are summable, with a bound
by the original physical height norm. Only closed local extensions are
used to obtain the individual L² representatives. -/
theorem n07b_referenceBulk_energy_sum
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (β : ℝ) {f : PolarPoint → ℝ} (hf : HeightMember D T β f) (b : ℕ)
    (e : ℕ → PolarPoint → ℝ)
    (heq : ∀ m, EqOn (n07bReferencePieceCanonicalSource D C K z m f) (e m) (canonicalOpen S K m))
    (he : ∀ m p, p ∈ canonicalClosed S K m → ContDiffAt ℝ ∞ (e m) p)
    {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ m x, x ∈ physicalPieceOpen S K z m →
      ∀ j : Fin (b + 1), ∀ i : n07bReferenceBulkIndex j.val,
        (n07bSourceNormalizer T K z m β x * n07bReferenceBulkCoefficient D T C K z m β j.val i x) ^ 2 ≤
          A * T.M x.1 ^ 2) :
    Summable (n07bPiecewiseCanonicalJetEnergy T K
      (fun m => n07bReferencePieceCanonicalSource D C K z m f) β 0 b) ∧
      (∑' m, n07bPiecewiseCanonicalJetEnergy T K
        (fun m => n07bReferencePieceCanonicalSource D C K z m f) β 0 b m) ≤
          A * n07bReferenceBulkPathConstant b * physicalNorm T β (b + 3) f ^ 2 := by
  let g : ℕ → PolarPoint → ℝ := fun m => n07bReferencePieceCanonicalSource D C K z m f
  let E : PolarPoint → ℝ := fun x => A * n07bReferenceBulkMajorant T β b f x
  have hE : IntegrableOn E (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) :=
    (n07bReferenceBulkMajorant_integrable hT hf b).const_mul A
  have hpiece (m : ℕ) : n07bPiecewiseCanonicalJetEnergy T K g β 0 b m ≤
      ∫ x in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), E x := by
    have hg (j : Fin (b + 1)) : MemLp (mixedDerivative 0 j.val (g m)) 2
        (canonicalMeasure S K m) :=
      n07b_canonical_mixedDerivative_memLp_of_extension m (heq m) (he m) 0 j.val
    have hrow := n07b_piecewiseCanonicalEnergy_physical (T := T) hK hz hs g β 0 b m hg
    rw [hrow.2]
    have hsub : physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi) ⊆
        Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi := by
      intro x hx
      exact ⟨((hK.domains z hz hs m).2.2.1 hx.1).1, hx.2.2⟩
    apply integral_mono_ae hrow.1 (hE.mono_set hsub)
    filter_upwards [ae_restrict_mem ((hK.domains z hz hs m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc))] with x hx
    exact n07b_referenceBulk_density_bound hK href hsref hz hs hD hT β hf.1 b m hx.1
      (hcoeff m x hx.1)
  obtain ⟨hsum, htotal⟩ := n07b_summable_energy_of_piece_integral_bound hK hz hs hE
    (fun m => n07bPiecewiseCanonicalJetEnergy_nonneg T K g β 0 b m) hpiece
  refine ⟨hsum, htotal.trans ?_⟩
  change (∫ x in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
    A * n07bReferenceBulkMajorant T β b f x) ≤ _
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (n07bReferenceBulkMajorant_integral_le hT hf b) hA).trans_eq
    (mul_assoc A (n07bReferenceBulkPathConstant b) (physicalNorm T β (b + 3) f ^ 2)).symm

/-- Agreement on the canonical open piece transfers the exact density
bound to the actual global forcing representative, without any regularity
or symmetry assumption outside that open piece. -/
theorem n07b_referenceBulk_density_bound_of_eqOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (β : ℝ) {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (b m : ℕ) {g : ℕ → PolarPoint → ℝ}
    (hge : EqOn (g m) (n07bReferencePieceCanonicalSource D C K z m f) (canonicalOpen S K m))
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) {A : ℝ}
    (hcoeff : ∀ j : Fin (b + 1), ∀ i : n07bReferenceBulkIndex j.val,
      (n07bSourceNormalizer T K z m β x * n07bReferenceBulkCoefficient D T C K z m β j.val i x) ^ 2 ≤
        A * T.M x.1 ^ 2) :
    n07bPiecewiseCanonicalDensity T K z g β 0 b m x ≤
      A * n07bReferenceBulkMajorant T β b f x := by
  calc
    _ = n07bPiecewiseCanonicalDensity T K z
        (fun m => n07bReferencePieceCanonicalSource D C K z m f) β 0 b m x := by
      unfold n07bPiecewiseCanonicalDensity
      apply Finset.sum_congr rfl
      intro j _
      have hjet := mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) hge 0 j.val
      rw [hjet ((hK.charts z hz hs m).1 hx)]
    _ ≤ _ := n07b_referenceBulk_density_bound hK href hsref hz hs hD hT β hf b m hx hcoeff

/-- The actual global reference bulk forcing belongs to the already
selected volume-model level. Only its canonical germs must agree with the
smooth local pieces; periodicity and reflection are required of `g` itself. -/
theorem n07b_exists_referenceBulkLift
    {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hV : IsVolumeModel T S K V)
    (β : ℝ) {f : PolarPoint → ℝ} (hf : HeightMember D T β f) (b : ℕ)
    (g : ℕ → PolarPoint → ℝ)
    (hge : ∀ m, EqOn (g m) (n07bReferencePieceCanonicalSource D C K z m f) (canonicalOpen S K m))
    (he : ∀ m p, p ∈ canonicalClosed S K m →
      ContDiffAt ℝ ∞ (n07bReferencePieceCanonicalSource D C K z m f) p)
    (hp : ∀ m r, r ∈ Ioo (K.left m) (K.right m) → Function.Periodic
      (fun θ => g m (r, θ)) Real.pi)
    (hreflect : ∀ m, (fun p : PolarPoint => g m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] g m)
    {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ m x, x ∈ physicalPieceOpen S K z m →
      ∀ j : Fin (b + 1), ∀ i : n07bReferenceBulkIndex j.val,
        (n07bSourceNormalizer T K z m β x * n07bReferenceBulkCoefficient D T C K z m β j.val i x) ^ 2 ≤
          A * T.M x.1 ^ 2) :
    ∃ F : V.level β 0 b,
      (∀ m, (V.forget β 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] g m) ∧
      ‖F‖ ^ 2 ≤ A * n07bReferenceBulkPathConstant b * physicalNorm T β (b + 3) f ^ 2 := by
  have hE := (n07bReferenceBulkMajorant_integrable hT hf b).const_mul A
  obtain ⟨F, hforget, hnorm⟩ := n07b_exists_piecewiseCanonicalLift_of_density_bound
    hD hT hV hK hz hs g (fun m => n07bReferencePieceCanonicalSource D C K z m f)
    β 0 b hge he hp hreflect hE
    (fun m x hx => n07b_referenceBulk_density_bound_of_eqOn hK href hsref hz hs
      hD hT β hf.1 b m (hge m) hx.1 (hcoeff m x hx.1))
  refine ⟨F, hforget, hnorm.trans ?_⟩
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (n07bReferenceBulkMajorant_integral_le hT hf b) hA).trans_eq
    (mul_assoc A (n07bReferenceBulkPathConstant b) (physicalNorm T β (b + 3) f ^ 2)).symm

end ActualReference

end ContinuousFlexibility.Analysis
