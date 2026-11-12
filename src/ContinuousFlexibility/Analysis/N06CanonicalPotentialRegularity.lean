import ContinuousFlexibility.Analysis.N06CanonicalPotentialPeriodicity
import ContinuousFlexibility.Analysis.N06CurrentOperatorRegularity
import ContinuousFlexibility.Analysis.N06CurrentOperatorReflection
import ContinuousFlexibility.Analysis.N06FiniteSourceGeometry

/-!
# Smoothness and reflection of the actual current potential

All three qualitative multiplier properties of the genuine K.potential
are derived from the unchanged N01--N04 data: local smoothness, period pi,
and even reflection. The source transform is differentiated only on its
actual open piece, and the corrected physical coefficients are not
assumed to possess additional smoothness.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Local source regularity is enough for the actual source transform. -/
theorem n06_canonicalSource_contDiffOn_piece
    (hA : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (physicalPieceOpen S K z m)) :
    ContDiffOn ℝ ∞ (canonicalSource S K z m f) (canonicalOpen S K m) := by
  obtain ⟨_, hGmap, _, _, hF, hG, hH, hgood⟩ :=
    hA.charts z hz hs m
  have hJ := n06_contDiffOn_planeJacobian (hA.domains z hz hs m).1 hF
  have hJne : ∀ p ∈ physicalPieceOpen S K z m, planeJacobian (K.chart z m) p ≠ 0 :=
    fun p hp => (hgood p hp).2.1
  exact ((hH.mul hf).div (hJ.abs hJne)
    (fun p hp => abs_ne_zero.mpr (hJne p hp))).comp hG hGmap

/-- The genuine potential is smooth on every current canonical open piece. -/
theorem n06_canonicalPotential_contDiffOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    ContDiffOn ℝ ∞ (K.potential z m) (canonicalOpen S K m) := by
  have hA := (n06_N04_qualitative_parts h04).1
  have hB := (n06_N04_qualitative_parts h04).2
  have hLH := n06_correctedHeightDivergence_contDiffOn_piece hT hS h01 h03 hA hz hs m
  have hsrc := n06_canonicalSource_contDiffOn_piece hA hz hs m hLH
  have hconst : ContDiffOn ℝ ∞
      (fun _ : PolarPoint => if K.positive m then -1 else (1 : ℝ))
      (canonicalOpen S K m) := contDiffOn_const
  exact (hconst.mul hsrc).congr
    (fun p hp => canonicalPotential_eq_source_height hB hz hs m hp)

/-- Reflection is needed only on the physical piece of this transform. -/
theorem n06_canonicalSource_evenOn_piece
    (hA : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ q ∈ physicalPieceOpen S K z m, f (q.1, -q.2) = f q)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f (p.1, -p.2) = canonicalSource S K z m f p := by
  have hq := (hA.charts z hz hs m).2.1 hp
  have hsym := hA.reflection z hz hs m _ hq
  have hG := hA.inverseReflection z hz hs m p hp
  change K.height z m (K.inverseChart z m (p.1, -p.2)) *
      f (K.inverseChart z m (p.1, -p.2)) /
      |planeJacobian (K.chart z m) (K.inverseChart z m (p.1, -p.2))| = _
  rw [hG, hsym.2.1, hf _ hq, hsym.2.2]
  rfl

theorem n06_correctedHeightDivergence_evenOn_piece
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K z m) :
    divergenceOperator (L.coefficients z) (K.height z m) (p.1, -p.2) =
      divergenceOperator (L.coefficients z) (K.height z m) p := by
  obtain ⟨η, hη⟩ := n06_exists_heightPair_canonicalHeight_germ hT hS hA hz hs m hp
  have hp' : (p.1, -p.2) ∈ physicalPieceOpen S K z m :=
    ((hA.domains z hz hs m).2.2.2.2.1 p).mpr hp
  have hradial : (K.chart z m (p.1, -p.2)).1 = (K.chart z m p).1 := by
    simpa only [] using congrArg Prod.fst (hA.reflection z hz hs m p hp).1
  exact (n05_divergenceOperator_congr (L.coefficients z)
    (hη _ hp' hradial)).symm.trans
      ((n06_correctedDivergence_heightPair_even hS h03 hz hs η p).trans
        (n05_divergenceOperator_congr (L.coefficients z) (hη p hp rfl)))

/-- Actual N03 signs and actual N04 reflected coordinates force the even
symmetry of the potential, including at reflection fixed points. -/
theorem n06_canonicalPotential_evenOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    K.potential z m (p.1, -p.2) = K.potential z m p := by
  have hA := (n06_N04_qualitative_parts h04).1
  have hB := (n06_N04_qualitative_parts h04).2
  have hp' : (p.1, -p.2) ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  rw [canonicalPotential_eq_source_height hB hz hs m hp',
    canonicalPotential_eq_source_height hB hz hs m hp]
  exact congrArg (fun a : ℝ => (if K.positive m then -1 else (1 : ℝ)) * a)
    (n06_canonicalSource_evenOn_piece hA hz hs m
      (fun q hq => n06_correctedHeightDivergence_evenOn_piece hT hS h03 hA hz hs m hq) hp)

/-- The literal half-period reflection used by the original volume graph. -/
theorem n06_canonicalPotential_reflectionOn
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    K.potential z m (p.1, Real.pi - p.2) = K.potential z m p := by
  have hn : (p.1, -p.2) ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  have ht := n06_canonicalPotential_periodicOn hT hS h03 h04 hz hs m hn
  have he := n06_canonicalPotential_evenOn hT hS h03 h04 hz hs m hp
  have hshift : (p.1, -p.2) + (0, Real.pi) = (p.1, Real.pi - p.2) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
  rw [hshift] at ht
  exact ht.trans he

end ContinuousFlexibility.Statements
