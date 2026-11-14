module

public import ContinuousFlexibility.Analysis.N07bAngularChainExpansion
public import ContinuousFlexibility.Analysis.N07bMaterialJetEnergy
public import ContinuousFlexibility.Analysis.N07bCanonicalSourceLift
public import ContinuousFlexibility.Radial.R11bPartitionSquare

/-!
# A genuine physical majorant for the canonical source energy

The geometry-only coefficient comparison is an explicit hypothesis here.
It is not asserted to follow from the qualitative frozen chart properties.
Once that comparison is available, finite Cauchy--Schwarz and the actual
material jet energies supply an integrable majorant independent of the
piece index. The source loses only one material weight order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The geometric energy multiplier. For positive material heights it is
`ell * |J| * (H / H_m)^(3/2)`. No physical source occurs in this definition. -/
def n07bSourceGeometricWeight {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint) : ℝ :=
  T.ell x.1 * ((n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
    |planeJacobian (K.chart z m) x| * (T.H x.1 ^ (3 / 4 : ℝ)) ^ 2)

/-- The physical density of the full finite canonical source row. -/
def n07bSourceRowDensity {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (f : PolarPoint → ℝ)
    (b m : ℕ) (x : PolarPoint) : ℝ :=
  ∑ j : Fin (b + 1), (n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
    (|planeJacobian (K.chart z m) x| * (n07bPhysicalSourceJet K z m f j.val x) ^ 2)

/-- One common integrable physical density, independent of the piece. -/
def n07bSourceMaterialMajorant (T : MaterialData) (b : ℕ)
    (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  ∑ j : Fin (b + 1), (3 : ℝ) ^ j.val *
    ∑ i : n07bAngularChainIndex j.val,
      n07bMaterialJetEnergyDensity T (3 / 4 : ℝ)
        (n07bAngularChainRadial j.val i) (n07bAngularChainAngular j.val i) 1 f x

/-- The two path counts in the coarse energy bound, equivalently the
finite sum of `9^j` over the retained angular orders. -/
def n07bSourcePathConstant (b : ℕ) : ℝ :=
  ∑ j : Fin (b + 1), (3 : ℝ) ^ j.val * (3 : ℝ) ^ j.val

theorem n07bSourcePathConstant_nonneg (b : ℕ) : 0 ≤ n07bSourcePathConstant b :=
  Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

private theorem finite_weighted_square {ι : Type*} [Fintype ι]
    (c v : ι → ℝ) {ell W M A : ℝ} (hell : 0 < ell) (hW : 0 ≤ W)
    (hc : ∀ i, ell * W * c i ^ 2 ≤ A * M ^ 2) :
    W * (∑ i, c i * v i) ^ 2 ≤
      A * (Fintype.card ι : ℝ) * ∑ i, (M * v i) ^ 2 / ell := by
  classical
  have hcs := ContinuousFlexibility.Radial.r11b_finset_sum_square_le
    Finset.univ (fun i => c i * v i) (B := Fintype.card ι) (by simp)
  have hterm (i : ι) : W * (c i * v i) ^ 2 ≤ A * ((M * v i) ^ 2 / ell) := by
    have hi : W * c i ^ 2 ≤ A * M ^ 2 / ell :=
      (le_div_iff₀ hell).mpr (by nlinarith only [hc i])
    calc
      _ = (W * c i ^ 2) * v i ^ 2 := by ring
      _ ≤ (A * M ^ 2 / ell) * v i ^ 2 := mul_le_mul_of_nonneg_right hi (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ W * ((Fintype.card ι : ℝ) * ∑ i, (c i * v i) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs hW
    _ = (Fintype.card ι : ℝ) * ∑ i, W * (c i * v i) ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, A * ((M * v i) ^ 2 / ell) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem n07bSourceMaterialMajorant_nonneg
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (b : ℕ) (f : PolarPoint → ℝ) {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) :
    0 ≤ n07bSourceMaterialMajorant T b f x := by
  unfold n07bSourceMaterialMajorant
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (Finset.sum_nonneg (fun i _ =>
      n07bMaterialJetEnergyDensity_nonneg hT (3 / 4 : ℝ) _ _ 1 f hx))

theorem n07bSourceMaterialMajorant_integrable
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : HeightMember D T (3 / 4 : ℝ) f) (b : ℕ) :
    IntegrableOn (n07bSourceMaterialMajorant T b f)
      (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) := by
  unfold n07bSourceMaterialMajorant
  apply integrable_finsetSum
  intro j _
  exact (integrable_finsetSum Finset.univ (fun i _ =>
    n07bMaterialJetEnergyDensity_integrable hT hf
      (n07bAngularChainRadial j.val i) (n07bAngularChainAngular j.val i) 1)).const_mul
        ((3 : ℝ) ^ j.val)

/-- The path count affects only a finite constant. Exactly one material
weight is used, so the physical norm order is `b + 1`. -/
theorem n07bSourceMaterialMajorant_integral_le
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : HeightMember D T (3 / 4 : ℝ) f) (b : ℕ) :
    (∫ x in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi, n07bSourceMaterialMajorant T b f x) ≤
      n07bSourcePathConstant b * physicalNorm T (3 / 4 : ℝ) (b + 1) f ^ 2 := by
  classical
  have hi (j : Fin (b + 1)) (i : n07bAngularChainIndex j.val) :=
    n07bMaterialJetEnergyDensity_integrable hT hf
      (n07bAngularChainRadial j.val i) (n07bAngularChainAngular j.val i) 1
  have hrow (j : Fin (b + 1)) :=
    integrable_finsetSum Finset.univ (fun i _ => hi j i)
  change (∫ x in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
    ∑ j : Fin (b + 1), (3 : ℝ) ^ j.val * ∑ i : n07bAngularChainIndex j.val,
      n07bMaterialJetEnergyDensity T (3 / 4 : ℝ)
        (n07bAngularChainRadial j.val i) (n07bAngularChainAngular j.val i) 1 f x) ≤ _
  rw [integral_finsetSum Finset.univ (fun j _ => (hrow j).const_mul ((3 : ℝ) ^ j.val))]
  calc
    _ = ∑ j : Fin (b + 1), (3 : ℝ) ^ j.val * ∑ i : n07bAngularChainIndex j.val,
        ∫ x in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
          n07bMaterialJetEnergyDensity T (3 / 4 : ℝ)
            (n07bAngularChainRadial j.val i) (n07bAngularChainAngular j.val i) 1 f x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi j i)]
    _ ≤ ∑ j : Fin (b + 1), (3 : ℝ) ^ j.val * ∑ _i : n07bAngularChainIndex j.val,
        physicalNorm T (3 / 4 : ℝ) (b + 1) f ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      apply Finset.sum_le_sum
      intro i _
      exact n07bMaterialJetEnergyDensity_integral_le hT hf _ _ 1 (b + 1)
        (by have ho := n07b_angularChain_order j.val i; omega)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        n07b_angularChain_card, Nat.cast_pow, Nat.cast_ofNat,
        n07bSourcePathConstant, Finset.sum_mul, mul_assoc]

/-- Pure geometric coefficient domination gives the physical row bound.
This is explicitly conditional on the coefficient comparison. -/
theorem n07b_sourceBound_row_pointwise
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (b m : ℕ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K z m) {A : ℝ}
    (hcoeff : ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
      n07bSourceGeometricWeight T K z m x *
        n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤
          A * T.M x.1 ^ 2) :
    n07bSourceRowDensity T K z f b m x ≤ A * n07bSourceMaterialMajorant T b f x := by
  classical
  have hxcore : x.1 ∈ Ioo D.a D.b := ((hK.domains z hz hs m).2.2.1 hx).1
  unfold n07bSourceRowDensity n07bSourceMaterialMajorant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let W : ℝ := (n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
    |planeJacobian (K.chart z m) x| * (T.H x.1 ^ (3 / 4 : ℝ)) ^ 2
  have hW : 0 ≤ W :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _)) (sq_nonneg _)
  have hc (i : n07bAngularChainIndex j.val) : T.ell x.1 * W *
      n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤ A * T.M x.1 ^ 2 :=
    hcoeff j i
  have hfin := finite_weighted_square
    (fun i => n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x)
    (fun i => mixedDerivative (n07bAngularChainRadial j.val i) (n07bAngularChainAngular j.val i)
      (materialPullback T (3 / 4 : ℝ) f) (n07bMaterialChart T x)) (hT.2.1 x.1 hxcore).1 hW hc
  calc
    _ = W * (∑ i : n07bAngularChainIndex j.val,
        n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x *
          mixedDerivative (n07bAngularChainRadial j.val i) (n07bAngularChainAngular j.val i)
            (materialPullback T (3 / 4 : ℝ) f) (n07bMaterialChart T x)) ^ 2 := by
      rw [n07b_physicalSourceJet_material_expansion hT hK hz hs m (3 / 4 : ℝ) hf j.val hx]
      dsimp only [W]
      ring
    _ ≤ _ := by
      simpa only [n07b_angularChain_card, Nat.cast_pow, Nat.cast_ofNat,
        n07bMaterialJetEnergyDensity, n07bMaterialChart, pow_one, mul_assoc] using hfin

end ContinuousFlexibility.Analysis
