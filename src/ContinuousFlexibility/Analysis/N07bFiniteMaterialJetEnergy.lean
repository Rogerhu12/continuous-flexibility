module

public import ContinuousFlexibility.Analysis.N07bMaterialJetEnergy
public import ContinuousFlexibility.Radial.R11bPartitionSquare
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Energy of an arbitrary finite material-jet expansion

The pointwise estimate uses arbitrary actual coefficients and arbitrary
finite jet orders. It has no atlas index or fixed piece as an argument.
Its physical majorant is a finite sum of genuine material-jet energy
densities, integrable on every subdomain of the physical core cylinder.
No membership of the expanded expression is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Weighted finite Cauchy--Schwarz, with one common coefficient-square
bound. Positivity is required only of the actual density denominator. -/
theorem n07b_finite_weighted_square_le {ι : Type*} [Fintype ι]
    (c v : ι → ℝ) {ell W M A : ℝ} (hell : 0 < ell) (hW : 0 ≤ W)
    (hc : ∀ i, ell * W * c i ^ 2 ≤ A * M ^ 2) :
    W * (∑ i, c i * v i) ^ 2 ≤
      (Fintype.card ι : ℝ) * A * ∑ i, (M * v i) ^ 2 / ell := by
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

/-- The actual material-jet bound with an arbitrary sampled height and
actual Jacobian value. The coefficient hypothesis is precisely the
normalized squared coefficient, with the same density `ell * |J|`. -/
theorem n07b_finite_materialJet_energy_le
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {ι : Type*} [Fintype ι] (β : ℝ) (a b : ι → ℕ)
    (c : ι → PolarPoint → ℝ) (f : PolarPoint → ℝ)
    {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) {Hsample J A : ℝ}
    (hHsample : 0 < Hsample)
    (hc : ∀ i, (T.ell x.1 * |J|) * ((T.H x.1 / Hsample) ^ β) ^ 2 * c i x ^ 2 ≤
      A * T.M x.1 ^ 2) :
    (Hsample ^ β)⁻¹ ^ 2 * |J| *
        (T.H x.1 ^ β * ∑ i, c i x * mixedDerivative (a i) (b i)
          (materialPullback T β f) (T.rho x.1, x.2)) ^ 2 ≤
      (Fintype.card ι : ℝ) * A *
        ∑ i, n07bMaterialJetEnergyDensity T β (a i) (b i) 1 f x := by
  classical
  let W : ℝ := (Hsample ^ β)⁻¹ ^ 2 * |J| * (T.H x.1 ^ β) ^ 2
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _)) (sq_nonneg _)
  have hratio : (T.H x.1 / Hsample) ^ β = T.H x.1 ^ β * (Hsample ^ β)⁻¹ := by
    rw [Real.div_rpow (hT.2.1 x.1 hx).2.1.le hHsample.le, div_eq_mul_inv]
  have hweight : T.ell x.1 * W = (T.ell x.1 * |J|) * ((T.H x.1 / Hsample) ^ β) ^ 2 := by
    rw [hratio, mul_pow]
    dsimp only [W]
    ring
  have hfin := n07b_finite_weighted_square_le (fun i => c i x)
    (fun i => mixedDerivative (a i) (b i) (materialPullback T β f) (T.rho x.1, x.2))
    (hT.2.1 x.1 hx).1 hW (fun i => by rw [hweight]; exact hc i)
  calc
    _ = W * (∑ i, c i x * mixedDerivative (a i) (b i)
        (materialPullback T β f) (T.rho x.1, x.2)) ^ 2 := by
      dsimp only [W]
      ring
    _ ≤ _ := by
      simpa only [n07bMaterialJetEnergyDensity, pow_one] using hfin

/-- The identical estimate with the normalized coefficient written as an
actual square; this is the form supplied by normalized direction paths. -/
theorem n07b_finite_materialJet_energy_le_of_normalized
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {ι : Type*} [Fintype ι] (β : ℝ) (a b : ι → ℕ)
    (c : ι → PolarPoint → ℝ) (f : PolarPoint → ℝ)
    {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) {Hsample J A : ℝ}
    (hHsample : 0 < Hsample)
    (hc : ∀ i, (Real.sqrt (T.ell x.1 * |J|) * (T.H x.1 / Hsample) ^ β * c i x) ^ 2 ≤
      A * T.M x.1 ^ 2) :
    (Hsample ^ β)⁻¹ ^ 2 * |J| *
        (T.H x.1 ^ β * ∑ i, c i x * mixedDerivative (a i) (b i)
          (materialPullback T β f) (T.rho x.1, x.2)) ^ 2 ≤
      (Fintype.card ι : ℝ) * A *
        ∑ i, n07bMaterialJetEnergyDensity T β (a i) (b i) 1 f x := by
  apply n07b_finite_materialJet_energy_le hT β a b c f hx hHsample
  intro i
  simpa only [mul_pow, Real.sq_sqrt
    (mul_nonneg (hT.2.1 x.1 hx).1.le (abs_nonneg J))] using hc i

/-- The actual finite majorant, independent of all expansion coefficients. -/
def n07bFiniteMaterialJetMajorant {ι : Type*} [Fintype ι]
    (T : MaterialData) (β : ℝ) (a b : ι → ℕ) (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  ∑ i, n07bMaterialJetEnergyDensity T β (a i) (b i) 1 f x

theorem n07bFiniteMaterialJetMajorant_nonneg
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {ι : Type*} [Fintype ι] (β : ℝ) (a b : ι → ℕ) (f : PolarPoint → ℝ)
    {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) :
    0 ≤ n07bFiniteMaterialJetMajorant T β a b f x :=
  Finset.sum_nonneg (fun i _ => n07bMaterialJetEnergyDensity_nonneg hT β (a i) (b i) 1 f hx)

theorem n07bFiniteMaterialJetMajorant_integrable
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {ι : Type*} [Fintype ι] {β : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T β f) (a b : ι → ℕ) :
    IntegrableOn (n07bFiniteMaterialJetMajorant T β a b f)
      (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) := by
  change IntegrableOn (fun x => ∑ i, n07bMaterialJetEnergyDensity T β (a i) (b i) 1 f x) _
  exact integrable_finsetSum Finset.univ (fun i _ => n07bMaterialJetEnergyDensity_integrable hT hf (a i) (b i) 1)

/-- No fixed atlas domain is needed: any physical subdomain inherits the
integrable finite material-jet majorant. -/
theorem n07bFiniteMaterialJetMajorant_integrableOn
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {ι : Type*} [Fintype ι] {β : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T β f) (a b : ι → ℕ) {U : Set PolarPoint}
    (hU : U ⊆ Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) :
    IntegrableOn (n07bFiniteMaterialJetMajorant T β a b f) U :=
  (n07bFiniteMaterialJetMajorant_integrable hT hf a b).mono_set hU

/-- The finite majorant is bounded by the original physical seminorm on
every physical subdomain, at exactly the required material jet order. -/
theorem n07bFiniteMaterialJetMajorant_integral_le
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {ι : Type*} [Fintype ι] {β : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T β f) (a b : ι → ℕ) (s : ℕ)
    (horder : ∀ i, a i + b i + 1 ≤ s) {U : Set PolarPoint}
    (hU : U ⊆ Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) :
    (∫ x in U, n07bFiniteMaterialJetMajorant T β a b f x) ≤
      (Fintype.card ι : ℝ) * physicalNorm T β s f ^ 2 := by
  classical
  have hi := n07bFiniteMaterialJetMajorant_integrable hT hf a b
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi)]
      n07bFiniteMaterialJetMajorant T β a b f := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with x hx
    exact n07bFiniteMaterialJetMajorant_nonneg hT β a b f hx.1
  apply (setIntegral_mono_set hi hnonneg (Filter.Eventually.of_forall (fun x hx => hU hx))).trans
  change (∫ x in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
    ∑ i, n07bMaterialJetEnergyDensity T β (a i) (b i) 1 f x) ≤ _
  rw [integral_finsetSum Finset.univ
    (fun i _ => n07bMaterialJetEnergyDensity_integrable hT hf (a i) (b i) 1)]
  calc
    _ ≤ ∑ _i : ι, physicalNorm T β s f ^ 2 := Finset.sum_le_sum
      (fun i _ => n07bMaterialJetEnergyDensity_integral_le hT hf (a i) (b i) 1 s (horder i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end ContinuousFlexibility.Analysis
