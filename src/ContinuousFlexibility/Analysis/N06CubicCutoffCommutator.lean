import ContinuousFlexibility.Analysis.N06CubicCutoffJets
import ContinuousFlexibility.Analysis.N06CubicDifferential
import ContinuousFlexibility.Radial.RadialHeight

/-!
# The genuine cubic cutoff commutator

The first identity applies the product rule to both actual fluxes of the
symmetric divergence operator. Its cubic specialization uses only local
first derivatives of the divided coefficients. The weighted cutoff
estimate therefore controls the error without extending those
coefficients through either endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The actual radial-cutoff identity, including both mixed channels. -/
theorem n06_divergence_radialCutoff_commutator
    {L : SymmetricCoefficients} {φ : PolarPoint → ℝ} {χ : ℝ → ℝ} {p : PolarPoint}
    (ha : DifferentiableAt ℝ L.a p) (hb : DifferentiableAt ℝ L.b p)
    (hc : DifferentiableAt ℝ L.c p) (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ) :
    divergenceOperator L (fun q => χ q.1 * φ q) p - χ p.1 * divergenceOperator L φ p =
      deriv (deriv χ) p.1 * L.a p * φ p +
      deriv χ p.1 * ((radialPartial L.a p + angularPartial L.b p) * φ p +
        2 * L.a p * radialPartial φ p + 2 * L.b p * angularPartial φ p) := by
  let X := radialHeightField χ
  let Y := radialHeightField (deriv χ)
  let R : PolarPoint → ℝ := fun q => L.a q * radialPartial φ q + L.b q * angularPartial φ q
  let T : PolarPoint → ℝ := fun q => L.b q * radialPartial φ q + L.c q * angularPartial φ q
  have hχ₁ : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hX : ContDiff ℝ ∞ X := contDiff_radialHeightField hχ
  have hY : ContDiff ℝ ∞ Y := contDiff_radialHeightField hχ₁
  have hφr := contDiff_cylinder_radialPartial hφ
  have hφt := contDiff_cylinder_angularPartial hφ
  have hXp (q : PolarPoint) : radialPartial X q = Y q :=
    radialPartial_radialHeightField (hχ.differentiable (by simp) q.1)
  have hXt (q : PolarPoint) : angularPartial X q = 0 :=
    angularPartial_radialHeightField (hχ.differentiable (by simp) q.1)
  have hYp : radialPartial Y p = deriv (deriv χ) p.1 :=
    radialPartial_radialHeightField (hχ₁.differentiable (by simp) p.1)
  have hYt : angularPartial Y p = 0 :=
    angularPartial_radialHeightField (hχ₁.differentiable (by simp) p.1)
  have hgr : radialPartial (fun q => X q * φ q) =
      fun q => Y q * φ q + X q * radialPartial φ q := by
    funext q
    rw [radialPartial_mul (hX.differentiable (by simp) q) (hφ.differentiable (by simp) q), hXp]
  have hgt : angularPartial (fun q => X q * φ q) =
      fun q => X q * angularPartial φ q := by
    funext q
    rw [angularPartial_mul (hX.differentiable (by simp) q) (hφ.differentiable (by simp) q),
      hXt, zero_mul, zero_add]
  have hR : (fun q => L.a q * radialPartial (fun z => X z * φ z) q +
      L.b q * angularPartial (fun z => X z * φ z) q) =
      fun q => X q * R q + Y q * (L.a q * φ q) := by
    rw [hgr, hgt]
    funext q
    dsimp only [R]
    ring
  have hT : (fun q => L.b q * radialPartial (fun z => X z * φ z) q +
      L.c q * angularPartial (fun z => X z * φ z) q) =
      fun q => X q * T q + Y q * (L.b q * φ q) := by
    rw [hgr, hgt]
    funext q
    dsimp only [T]
    ring
  have hRd : DifferentiableAt ℝ R p :=
    (ha.mul (hφr.differentiable (by simp) p)).add
      (hb.mul (hφt.differentiable (by simp) p))
  have hTd : DifferentiableAt ℝ T p :=
    (hb.mul (hφr.differentiable (by simp) p)).add
      (hc.mul (hφt.differentiable (by simp) p))
  have hXd := hX.differentiable (by simp) p
  have hYd := hY.differentiable (by simp) p
  have hφd := hφ.differentiable (by simp) p
  have haφ : DifferentiableAt ℝ (fun q => L.a q * φ q) p := ha.mul hφd
  have hbφ : DifferentiableAt ℝ (fun q => L.b q * φ q) p := hb.mul hφd
  have hXR : DifferentiableAt ℝ (fun q => X q * R q) p := hXd.mul hRd
  have hXT : DifferentiableAt ℝ (fun q => X q * T q) p := hXd.mul hTd
  have hYaφ : DifferentiableAt ℝ (fun q => Y q * (L.a q * φ q)) p := hYd.mul haφ
  have hYbφ : DifferentiableAt ℝ (fun q => Y q * (L.b q * φ q)) p := hYd.mul hbφ
  change radialPartial (fun q => L.a q * radialPartial (fun z => X z * φ z) q +
      L.b q * angularPartial (fun z => X z * φ z) q) p +
    angularPartial (fun q => L.b q * radialPartial (fun z => X z * φ z) q +
      L.c q * angularPartial (fun z => X z * φ z) q) p -
      X p * (radialPartial R p + angularPartial T p) = _
  rw [hR, hT, radialPartial_add hXR hYaφ,
    angularPartial_add hXT hYbφ,
    radialPartial_mul hXd hRd, radialPartial_mul hYd haφ,
    angularPartial_mul hXd hTd, angularPartial_mul hYd hbφ,
    radialPartial_mul ha hφd, angularPartial_mul hb hφd, hXp, hXt, hYp, hYt]
  dsimp only [X, Y, R, T, radialHeightField]
  ring

private theorem cubic_normal_drift {d : ℝ → ℝ} {A B : PolarPoint → ℝ} {p : PolarPoint}
    (hd : DifferentiableAt ℝ d p.1) (hA : DifferentiableAt ℝ A p)
    (hB : DifferentiableAt ℝ B p) :
    radialPartial (fun q => d q.1 ^ 3 * A q) p +
      angularPartial (fun q => d q.1 ^ 3 * B q) p =
      d p.1 ^ 2 * (3 * deriv d p.1 * A p + d p.1 * radialPartial A p +
        d p.1 * angularPartial B p) := by
  have hd₃ : DifferentiableAt ℝ (fun q : PolarPoint => d q.1 ^ 3) p :=
    (hd.pow 3).comp p differentiableAt_fst
  have hr : radialPartial (fun q : PolarPoint => d q.1 ^ 3) p =
      3 * d p.1 ^ 2 * deriv d p.1 := by
    calc
      _ = deriv (fun y => d y ^ 3) p.1 := radialPartial_radialHeightField (hd.pow 3)
      _ = _ := by
        have hpow := (hd.hasDerivAt.pow 3).deriv
        have heq : (d ^ 3 : ℝ → ℝ) = fun y => d y ^ 3 := by
          funext y
          rfl
        rw [heq] at hpow
        simpa only [Nat.cast_ofNat, Nat.reduceSub, smul_eq_mul] using hpow
  have ht : angularPartial (fun q : PolarPoint => d q.1 ^ 3) p = 0 :=
    angularPartial_radialHeightField (hd.pow 3)
  rw [radialPartial_mul hd₃ hA, angularPartial_mul hd₃ hB, hr, ht]
  ring

/-- The cubic commutator is a sum of exactly the four terms whose radial
weights absorb the cutoff derivatives. -/
theorem n06_cubic_radialCutoff_commutator
    {A B C φ : PolarPoint → ℝ} {χ : ℝ → ℝ} {p : PolarPoint}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p) (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ) :
    divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C)
        (fun q => χ q.1 * φ q) p -
      χ p.1 * divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p =
      (cylinderWeight p.1 ^ 3 * deriv (deriv χ) p.1) * A p * φ p +
      (cylinderWeight p.1 ^ 2 * deriv χ p.1) *
        (3 * (1 - 2 * p.1) * A p + cylinderWeight p.1 * radialPartial A p +
          cylinderWeight p.1 * angularPartial B p) * φ p +
      2 * (cylinderWeight p.1 ^ 3 * deriv χ p.1) * A p * radialPartial φ p +
      2 * (cylinderWeight p.1 ^ 3 * deriv χ p.1) * B p * angularPartial φ p := by
  have hd := (cylinderWeight_hasDerivAt p.1).differentiableAt
  have hd₃ : DifferentiableAt ℝ (fun q : PolarPoint => cylinderWeight q.1 ^ 3) p :=
    (hd.pow 3).comp p differentiableAt_fst
  rw [n06_divergence_radialCutoff_commutator (hd₃.mul hA) (hd₃.mul hB) (hd₃.mul hC) hφ hχ]
  change deriv (deriv χ) p.1 * (cylinderWeight p.1 ^ 3 * A p) * φ p +
    deriv χ p.1 * ((radialPartial (fun q => cylinderWeight q.1 ^ 3 * A q) p +
      angularPartial (fun q => cylinderWeight q.1 ^ 3 * B q) p) * φ p +
        2 * (cylinderWeight p.1 ^ 3 * A p) * radialPartial φ p +
        2 * (cylinderWeight p.1 ^ 3 * B p) * angularPartial φ p) = _
  rw [cubic_normal_drift hd hA hB, (cylinderWeight_hasDerivAt p.1).deriv]
  ring

private theorem abs_triple_le {x y z X Y Z : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hx : |x| ≤ X) (hy : |y| ≤ Y) (hz : |z| ≤ Z) :
    |x * y * z| ≤ X * Y * Z := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) hX) hz
    (abs_nonneg _) (mul_nonneg hX hY)

private theorem abs_four_le (x y z w : ℝ) :
    |x + y + z + w| ≤ |x| + |y| + |z| + |w| :=
  (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)

/-- A pointwise bound using only first divided-coefficient jets and the
three first test jets. No coefficient extension is assumed. -/
theorem n06_cubic_radialCutoff_error_abs_le
    {A B C φ : PolarPoint → ℝ} {χ : ℝ → ℝ} {p : PolarPoint} {δ J ε : ℝ}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hC : DifferentiableAt ℝ C p) (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    (hp : p.1 ∈ Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) (hJ : 0 ≤ J) (hε : 0 ≤ ε)
    (hA₀ : |A p| ≤ δ) (hB₀ : |B p| ≤ δ)
    (hAr : |radialPartial A p| ≤ δ) (hBt : |angularPartial B p| ≤ δ)
    (hφ₀ : |φ p| ≤ J) (hφr : |radialPartial φ p| ≤ J) (hφt : |angularPartial φ p| ≤ J)
    (hχ₁ : |cylinderWeight p.1 ^ 2 * deriv χ p.1| ≤ ε)
    (hχ₂ : |cylinderWeight p.1 ^ 3 * deriv (deriv χ) p.1| ≤ ε) :
    |divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C)
        (fun q => χ q.1 * φ q) p -
      χ p.1 * divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p| ≤ 10 * ε * δ * J := by
  have hd := cylinderWeight_nonneg hp
  have hd₁ := cylinderWeight_le_one hp
  have he : |1 - 2 * p.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hχ₃ : |cylinderWeight p.1 ^ 3 * deriv χ p.1| ≤ ε := by
    calc
      _ = |cylinderWeight p.1 * (cylinderWeight p.1 ^ 2 * deriv χ p.1)| :=
        congrArg abs (by ring)
      _ = cylinderWeight p.1 * |cylinderWeight p.1 ^ 2 * deriv χ p.1| := by
        rw [abs_mul, abs_of_nonneg hd]
      _ ≤ 1 * ε := mul_le_mul hd₁ hχ₁ (abs_nonneg _) zero_le_one
      _ = ε := one_mul _
  have hfirst := n06_cubic_firstOrder_abs hd hd₁ he hA₀ hAr hBt
  have h₁ := abs_triple_le hε hδ hχ₂ hA₀ hφ₀
  have h₂ := abs_triple_le hε (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hδ) hχ₁ hfirst hφ₀
  have h₃ : |2 * (cylinderWeight p.1 ^ 3 * deriv χ p.1) * A p * radialPartial φ p| ≤
      2 * (ε * δ * J) := by
    rw [show 2 * (cylinderWeight p.1 ^ 3 * deriv χ p.1) * A p * radialPartial φ p =
      2 * ((cylinderWeight p.1 ^ 3 * deriv χ p.1) * A p * radialPartial φ p) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_triple_le hε hδ hχ₃ hA₀ hφr) (by norm_num)
  have h₄ : |2 * (cylinderWeight p.1 ^ 3 * deriv χ p.1) * B p * angularPartial φ p| ≤
      2 * (ε * δ * J) := by
    rw [show 2 * (cylinderWeight p.1 ^ 3 * deriv χ p.1) * B p * angularPartial φ p =
      2 * ((cylinderWeight p.1 ^ 3 * deriv χ p.1) * B p * angularPartial φ p) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_triple_le hε hδ hχ₃ hB₀ hφt) (by norm_num)
  rw [n06_cubic_radialCutoff_commutator hA hB hC hφ hχ]
  exact (abs_four_le _ _ _ _).trans
    ((add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄).trans_eq (by ring))

end ContinuousFlexibility.Analysis
