import ContinuousFlexibility.Analysis.ActualNegativeReferenceInverseMaterialJets
import ContinuousFlexibility.Analysis.ActualNegativeReferenceGeometryFields

/-!
# Actual height-profile products on the original negative half

All powers use the stored height, and composition uses the stored inverse.
The physical profile or its reciprocal is estimated at the actual point
before transport to the original half sample. The optical host is separate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

private theorem negativeGeometry_profile_prefix
    {D : ReferenceData} (hD : RadialProfileGeometry D) (N : ℕ) :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ q, q ≤ N → ∀ r ∈ Icc D.a D.b,
      |iteratedDeriv q D.w r| ≤ P := by
  classical
  have hb (q : Fin (N + 1)) : ∃ A : ℝ, ∀ r ∈ Icc D.a D.b,
      ‖iteratedDeriv q.val D.w r‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedDeriv q.val hD.2.2.1.1 (by simp)).continuousOn
  choose A hA using hb
  refine ⟨1 + ∑ q : Fin (N + 1), |A q|,
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _), ?_⟩
  intro q hq r hr
  let j : Fin (N + 1) := ⟨q, by omega⟩
  have hj : |iteratedDeriv q D.w r| ≤ A j := by
    simpa only [Real.norm_eq_abs] using hA j r hr
  exact ((hj.trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun q : Fin (N + 1) => |A q|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j))).trans
      (le_add_of_nonneg_left zero_le_one)

/-- One material scale works before the real height power, the choice of
profile or reciprocal, and the finite order. Both the physical product
and its composition with the actual inverse use the same half sample. -/
theorem n04bActualTypedAtlas_reference_half_heightProfile_material_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (hK₀ : 0 < K₀) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let cut := n04bActualReferenceCut hN
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ γ : ℝ, ∀ inverse : Bool, ∀ N : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ r ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
          min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) →
      let f := fun r : ℝ => K.height (C.referenceState, 0) k (r, 0) ^ γ *
        (if inverse then (D.w r)⁻¹ else D.w r)
      let χ := fun ξ : ℝ => (K.inverseChart (C.referenceState, 0) k (ξ, 0)).1
      (∀ r ∈ Ioo (n04bNegativeLeft C cut (m, side))
          (n04bNegativeRight C cut (m, side)), ∀ q, q ≤ N →
        |iteratedDeriv q f r| ≤ B * (C0 * T.E0 (T.sample (K.cell k))) ^ B) ∧
      ∀ ξ ∈ Ioo (K.left k) (K.right k), ∀ q, q ≤ N →
        |iteratedDeriv q (f ∘ χ) ξ| ≤ B * (C0 * T.E0 (T.sample (K.cell k))) ^ B := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let cut := n04bActualReferenceCut hN
  have hD := n04b_profileGeometry_of_through03 hN
  obtain ⟨CH, hCH, hfloorH, hheight⟩ :=
    n04bActualTypedAtlas_reference_half_height_physical_power_material_jets hT hS hN hfield e hK₀
  obtain ⟨CI, hCI, hfloorI, BI, hBI, hinverse⟩ :=
    n04bActualTypedAtlas_reference_half_inverse_material_jets hT hS hN hfield e hK₀
  let C0 : ℝ := CH + CI
  have hC0 : 1 ≤ C0 := by dsimp only [C0]; linarith only [hCH, hCI]
  have hCH0 : CH ≤ C0 := le_add_of_nonneg_right (zero_le_one.trans hCI)
  have hCI0 : CI ≤ C0 := le_add_of_nonneg_left (zero_le_one.trans hCH)
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorH j).trans (mul_le_mul_of_nonneg_right hCH0
      (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT j)).2.2.1.le)
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro γ inverse N
  obtain ⟨BH, hBH, hHjets⟩ := hheight γ
  obtain ⟨P, hP, hwjets⟩ := negativeGeometry_profile_prefix hD N
  obtain ⟨Ki, Pi, hKi, hPi, hiPoint⟩ := material_inverseProfile_finite_point_jets hT hN.1.1.1.1 N
  obtain ⟨Ks, Ps, hKs, hPs, hiSample⟩ :=
    n04bActualTypedAtlas_negative_material_sample_weights hT hS hN hfield e 0 0 Pi hPi
  obtain ⟨CP, hCP, hprod⟩ := referencePotential_product_envelope N
  obtain ⟨CC, hCC, hcomp⟩ := referencePotential_composition_envelope N
  let total : ℝ := ∑ q : Fin (N + 1), (BH q.val + BI q.val)
  have htotal : 0 ≤ total := Finset.sum_nonneg fun q _ =>
    add_nonneg (zero_le_one.trans (hBH q.val)) (zero_le_one.trans (hBI q.val))
  have hKiKs : 0 < Ki * Ks := mul_pos hKi hKs
  let A : ℝ := 1 + P + Ki * Ks + Ps + total
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hP, hKiKs, hPs, htotal]
  have hPA : P ≤ A := by dsimp only [A]; linarith only [hKiKs, hPs, htotal]
  have hKiA : Ki * Ks ≤ A := by dsimp only [A]; linarith only [hP, hPs, htotal]
  have hPsA : Ps ≤ A := by dsimp only [A]; linarith only [hP, hKiKs, htotal]
  have hprefix (q : ℕ) (hq : q ≤ N) : BH q ≤ A ∧ BI q ≤ A := by
    have hh : BH q + BI q ≤ total := Finset.single_le_sum
      (fun t _ => add_nonneg (zero_le_one.trans (hBH t.val)) (zero_le_one.trans (hBI t.val)))
      (Finset.mem_univ (⟨q, by omega⟩ : Fin (N + 1)))
    dsimp only [A]
    constructor <;> linarith only [hh, hP, hKiKs, hPs, hBH q, hBI q]
  let CN : ℝ := 1 + CP + CC * CP
  have hCCP : 0 ≤ CC * CP := mul_nonneg (zero_le_one.trans hCC) (zero_le_one.trans hCP)
  have hCN : 1 ≤ CN := by dsimp only [CN]; linarith only [hCP, hCCP]
  have hCPCN : CP ≤ CN := by dsimp only [CN]; linarith only [hCCP]
  have hCCPCN : CC * CP ≤ CN := by dsimp only [CN]; linarith only [hCP]
  let coefficient : ℝ := CN * A ^ (N + 2)
  let exponent : ℝ := A * ((N + 2 : ℕ) : ℝ)
  have hc : 0 ≤ coefficient := mul_nonneg (zero_le_one.trans hCN) (pow_nonneg (zero_le_one.trans hA) _)
  have he : 0 ≤ exponent := mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg _)
  let B : ℝ := 1 + coefficient + exponent
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hc, he]
  have hcB : coefficient ≤ B := by dsimp only [B]; linarith only [he]
  have heB : exponent ≤ B := by dsimp only [B]; linarith only [hc]
  refine ⟨B, hB, ?_⟩
  intro k m side hk j hhost hoptical
  have hek : e.symm (.inl (m, side)) = k := by rw [← hk, e.symm_apply_apply]
  subst k
  let i := e.symm (.inl (m, side))
  have hi : e i = .inl (m, side) := e.apply_symm_apply _
  let I := Ioo (n04bNegativeLeft C cut (m, side)) (n04bNegativeRight C cut (m, side))
  let J := Ioo (K.left i) (K.right i)
  let H := fun r : ℝ => K.height (C.referenceState, 0) i (r, 0)
  let χ := fun ξ : ℝ => (K.inverseChart (C.referenceState, 0) i (ξ, 0)).1
  let w := fun r : ℝ => if inverse then (D.w r)⁻¹ else D.w r
  let f := fun r : ℝ => H r ^ γ * w r
  have hgeometry := n04Coordinates_actual_reference_negative_scalar_inverse hT hS hN hfield e m side
  have hHs : ContDiffOn ℝ ∞ H I := hgeometry.2.1
  have hχs : ContDiffOn ℝ ∞ χ J := hgeometry.2.2.1
  have hmap : MapsTo χ J I := hgeometry.2.2.2.1
  let E := T.E0 (T.sample (K.cell i))
  let W := C0 * E
  have hE : 0 < E := (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT (K.cell i))).2.2.1
  have hW : 1 ≤ W := hfloor (K.cell i)
  have hEW : E ≤ W := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC0 hE.le
  let M : ℝ := A * W ^ A
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hW (zero_le_one.trans hA))
  have hpack {a p V : ℝ} (hV : 0 ≤ V) (hVW : V ≤ W) (hp : 0 ≤ p)
      (haA : a ≤ A) (hpA : p ≤ A) : a * V ^ p ≤ M :=
    mul_le_mul haA ((Real.rpow_le_rpow hV hVW hp).trans
      (Real.rpow_le_rpow_of_exponent_le hW hpA))
      (Real.rpow_nonneg hV _) (zero_le_one.trans hA)
  have hpoint (r : ℝ) (hr : r ∈ I) : ContDiffAt ℝ ∞ f r ∧
      ∀ q, q ≤ N → |iteratedDeriv q f r| ≤ CP * M * M := by
    have hrwhole := n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) (m, side) hr
    have hcomponent := n01Properties_negativeRadialComponent hN.1.1 m
    have hcore : r ∈ radialCore D :=
      ⟨hcomponent.1.trans hrwhole.1, hrwhole.2.trans hcomponent.2.2.1⟩
    have hHpos : 0 < H r := (hgeometry.2.2.2.2.2.2.1 r hr).1
    have hwpos : 0 < D.w r := hD.2.2.2.2.1 r hcore
    have hHsmooth : ContDiffAt ℝ ∞ (fun t => H t ^ γ) r :=
      (hHs.contDiffAt (isOpen_Ioo.mem_nhds hr)).rpow_const_of_ne hHpos.ne'
    have hwsmooth : ContDiffAt ℝ ∞ w r := by
      cases inverse
      · exact hD.2.2.1.1.contDiffAt
      · exact hD.2.2.1.1.contDiffAt.inv hwpos.ne'
    have hHbound (q : ℕ) (hq : q ≤ N) : |iteratedDeriv q (fun t => H t ^ γ) r| ≤ M :=
      (hHjets i m side hi j hhost hoptical r hr 0 q).trans
        (hpack (mul_nonneg (zero_le_one.trans hCH) hE.le)
          (mul_le_mul_of_nonneg_right hCH0 hE.le) (zero_le_one.trans (hBH q))
          (hprefix q hq).1 (hprefix q hq).1)
    have hwbound (q : ℕ) (hq : q ≤ N) : |iteratedDeriv q w r| ≤ M := by
      cases inverse with
      | false =>
          exact (hwjets q hq r ⟨hcore.1.le, hcore.2.le⟩).trans
            (hPA.trans (le_mul_of_one_le_right (zero_le_one.trans hA)
              (Real.one_le_rpow hW (zero_le_one.trans hA))))
      | true =>
          have hs : T.E0 r ^ Pi ≤ Ks * E ^ Ps := by
            simpa only [Real.rpow_zero, one_mul] using hiSample i m side hi r ⟨hrwhole.1.le, hrwhole.2.le⟩
          have hb : |iteratedDeriv q (fun t => (D.w t)⁻¹) r| ≤ (Ki * Ks) * E ^ Ps :=
            (hiPoint r hcore q hq).trans ((mul_le_mul_of_nonneg_left hs hKi.le).trans_eq (by ring))
          exact hb.trans (hpack hE.le hEW hPs hKiA hPsA)
    exact ⟨hHsmooth.mul hwsmooth,
      hprod (zero_le_one.trans hM) (zero_le_one.trans hM)
        (fun t => H t ^ γ) w r hHsmooth hwsmooth hHbound hwbound⟩
  have hfinal : CN * M ^ (N + 2) ≤ B * W ^ B := by
    calc
      _ = coefficient * W ^ exponent := by
        dsimp only [M, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hW) A (N + 2)]
        ring
      _ ≤ B * W ^ B := mul_le_mul hcB (Real.rpow_le_rpow_of_exponent_le hW heB)
        (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hB)
  have hphysical : ∀ r ∈ I, ∀ q, q ≤ N → |iteratedDeriv q f r| ≤ B * W ^ B := by
    intro r hr q hq
    apply ((hpoint r hr).2 q hq).trans
    calc
      _ = CP * M ^ 2 := by ring
      _ ≤ CN * M ^ (N + 2) := mul_le_mul hCPCN (pow_le_pow_right₀ hM (by omega))
        (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hCN)
      _ ≤ _ := hfinal
  refine ⟨hphysical, ?_⟩
  intro ξ hξ q hq
  have hχbound (a : ℕ) (ha : 1 ≤ a) (haN : a ≤ N) : |iteratedDeriv a χ ξ| ≤ M := by
    have hb := hinverse i m side hi j hhost hoptical ξ hξ (a - 1)
    rw [Nat.sub_add_cancel ha] at hb
    exact hb.trans (hpack (mul_nonneg (zero_le_one.trans hCI) hE.le)
      (mul_le_mul_of_nonneg_right hCI0 hE.le) (zero_le_one.trans (hBI (a - 1)))
      (hprefix (a - 1) (by omega)).2 (hprefix (a - 1) (by omega)).2)
  have hb := hcomp (mul_nonneg (mul_nonneg (zero_le_one.trans hCP)
      (zero_le_one.trans hM)) (zero_le_one.trans hM)) hM f χ ξ
    (hpoint (χ ξ) (hmap hξ)).1 (hχs.contDiffAt (isOpen_Ioo.mem_nhds hξ))
    (hpoint (χ ξ) (hmap hξ)).2 hχbound q hq
  apply hb.trans
  calc
    _ = (CC * CP) * M ^ (N + 2) := by rw [pow_add, pow_two]; ring
    _ ≤ CN * M ^ (N + 2) := mul_le_mul_of_nonneg_right hCCPCN (pow_nonneg (zero_le_one.trans hM) _)
    _ ≤ _ := hfinal

end ContinuousFlexibility.Analysis
