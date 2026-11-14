module

public import ContinuousFlexibility.Analysis.N05CanonicalPhysicalChange
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise

/-!
# Actual angular jets of controlled reference sources

The radial reference chart leaves the angular variable unchanged. Thus
every actual angular source jet is the physical angular jet multiplied
by the actual radial height/Jacobian factor. Compactness and periodicity
bound the physical jets; the original coordinate bounds control the
factor. No canonical jet bound is added as a hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators Topology

set_option backward.isDefEq.respectTransparency false

theorem n06_smooth_periodic_angularJets_bounded
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi)) (l r : ℝ) (b : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ j, j ≤ b → ∀ p : PolarPoint,
      p.1 ∈ Icc l r → |mixedDerivative 0 j f p| ≤ B := by
  classical
  have hcompact : IsCompact (Icc l r ×ˢ Icc (0 : ℝ) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound : ∀ j : Fin (b + 1), ∃ C : ℝ,
      ∀ p ∈ Icc l r ×ˢ Icc (0 : ℝ) Real.pi,
        |mixedDerivative 0 j.val f p| ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hcompact.bddAbove_image
      (contDiff_mixedDerivative hf 0 j.val).continuous.abs.continuousOn
    exact ⟨C, fun p hp => hC ⟨p, hp, rfl⟩⟩
  choose c hc using hbound
  let B : ℝ := 1 + ∑ j : Fin (b + 1), |c j|
  have hsum : 0 ≤ ∑ j : Fin (b + 1), |c j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨B, by dsimp only [B]; linarith, ?_⟩
  intro j hj p hpr
  let j' : Fin (b + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hperiod : Function.Periodic (fun θ => mixedDerivative 0 j f (p.1, θ)) Real.pi := by
    intro θ
    exact mixedDerivative_angular_periodic (fun r θ => by
      simpa only [Prod.mk_add_mk, add_zero] using hp (r, θ)) 0 j p.1 θ
  obtain ⟨θ, hθ, heq⟩ := hperiod.exists_mem_Ico₀ Real.pi_pos p.2
  have hc' : |mixedDerivative 0 j f (p.1, θ)| ≤ c j' :=
    hc j' (p.1, θ) ⟨hpr, ⟨hθ.1, hθ.2.le⟩⟩
  have hterm : |c j'| ≤ ∑ i : Fin (b + 1), |c i| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ j')
  calc
    |mixedDerivative 0 j f p| = |mixedDerivative 0 j f (p.1, θ)| := by rw [heq]
    _ ≤ c j' := hc'
    _ ≤ |c j'| := le_abs_self _
    _ ≤ B := by dsimp only [B]; linarith

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- Angular differentiation uses the genuine inverse chart. Its radial
coordinate is fixed along each canonical circle by the actual inverse
identities, rather than by a separate proposed inverse formula. -/
theorem n06_controlledReferenceSource_angularJet
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (f : PolarPoint → ℝ) (m j : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    let x := K.inverseChart (C.referenceState, 0) m p
    mixedDerivative 0 j (canonicalSource S K (C.referenceState, 0) m f) p =
      (K.height (C.referenceState, 0) m (x.1, 0) /
        |deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) x.1|) *
        mixedDerivative 0 j f (x.1, p.2) := by
  have h01 := h.1.1.1
  have hA := h.2.2.2.2.1.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hcharts := hA.charts (C.referenceState, 0) href hs m
  rw [hA.referenceDomain m] at hcharts
  obtain ⟨hΦ, hΨ, hleft, hright, _⟩ := hcharts
  let x := K.inverseChart (C.referenceState, 0) m p
  have hx : x ∈ referencePhysicalPieceOpen S K m := hΨ hp
  have hradial : (K.chart (C.referenceState, 0) m (x.1, 0)).1 = p.1 := by
    have he := congrArg (fun q : PolarPoint => q.1) (hright p hp)
    rw [(hcoordinates.1 m x hx).1] at he
    exact he
  have hinverse (θ : ℝ) :
      K.inverseChart (C.referenceState, 0) m (p.1, θ) = (x.1, θ) := by
    have hq : (x.1, θ) ∈ referencePhysicalPieceOpen S K m := ⟨hx.1, mem_univ θ⟩
    have he : K.chart (C.referenceState, 0) m (x.1, θ) = (p.1, θ) := by
      rw [(hcoordinates.1 m (x.1, θ) hq).1, hradial]
    simpa only [he] using hleft (x.1, θ) hq
  have hsource :
      (fun θ => canonicalSource S K (C.referenceState, 0) m f (p.1, θ)) =
      fun θ => (K.height (C.referenceState, 0) m (x.1, 0) /
          |deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) x.1|) *
        f (x.1, θ) := by
    funext θ
    have hq : (x.1, θ) ∈ referencePhysicalPieceOpen S K m := ⟨hx.1, mem_univ θ⟩
    dsimp only [canonicalSource]
    rw [hinverse θ, (hcoordinates.1 m (x.1, θ) hq).2,
      n05_reference_planeJacobian_radial h hcoordinates m hq]
    ring
  change iteratedDeriv j
    (fun θ => canonicalSource S K (C.referenceState, 0) m f (p.1, θ)) p.2 = _
  rw [hsource, iteratedDeriv_const_mul_field]
  rfl

/-- The actual coordinate estimate gives the coefficient in the source
jet bound. It is independent of the angular jet order and of the source. -/
theorem n06_controlledReferenceSource_angularJet_bound
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : PolarPoint → ℝ, ∀ b : ℕ, ∀ B : ℝ,
      0 ≤ B →
      (∀ j, j ≤ b → ∀ p : PolarPoint, p.1 ∈ Ioo D.a D.b →
        |mixedDerivative 0 j f p| ≤ B) →
      ∀ m j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative 0 j (canonicalSource S K (C.referenceState, 0) m f) p| ≤
          (A * radialE (D.cellIndex (K.cell m)) ^ A) ^ 2 * B := by
  have hcoordinates' := hcoordinates
  obtain ⟨_, A, hA, _, _, hbounds⟩ := hcoordinates'
  refine ⟨A, hA, ?_⟩
  intro f b B hB hf m j hj p hp
  have h01 := h.1.1.1
  have hA := h.2.2.2.2.1.1
  have hpieces := hA.referenceBounds
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  let x := K.inverseChart (C.referenceState, 0) m p
  have hx : x ∈ referencePhysicalPieceOpen S K m := by
    have hxActual := (hA.charts (C.referenceState, 0) href hs m).2.1 hp
    simpa only [hA.referenceDomain m] using hxActual
  have hcoeff := hbounds m x.1 hx.1
  let E : ℝ := A * radialE (D.cellIndex (K.cell m)) ^ A
  have hheight : |K.height (C.referenceState, 0) m (x.1, 0)| ≤ E := by
    dsimp only [E]
    linarith [abs_nonneg ((K.height (C.referenceState, 0) m (x.1, 0))⁻¹),
      abs_nonneg (deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) x.1),
      abs_nonneg (deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) x.1),
      abs_nonneg ((deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) x.1)⁻¹)]
  have hinv : |(deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) x.1)⁻¹| ≤ E := by
    dsimp only [E]
    linarith [abs_nonneg (K.height (C.referenceState, 0) m (x.1, 0)),
      abs_nonneg ((K.height (C.referenceState, 0) m (x.1, 0))⁻¹),
      abs_nonneg (deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) x.1),
      abs_nonneg (deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) x.1)]
  have hE : 0 ≤ E := (abs_nonneg _).trans hheight
  rw [n06_controlledReferenceSource_angularJet h hcoordinates f m j hp, abs_mul]
  have hfactor : abs (K.height (C.referenceState, 0) m (x.1, 0) /
      |deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) x.1|) ≤ E ^ 2 := by
    rw [abs_div, abs_abs, div_eq_mul_inv, ← abs_inv]
    simpa only [pow_two] using mul_le_mul hheight hinv (abs_nonneg _) hE
  exact mul_le_mul hfactor (hf j hj (x.1, p.2) ((hpieces m).2.2 hx.1))
    (abs_nonneg _) (sq_nonneg E)

end ContinuousFlexibility.Statements
