module

public import ContinuousFlexibility.Analysis.CanonicalClosedSymmetry

/-!
# Each true cut meets each fundamental reflection axis once

Closed inverse symmetry identifies both physical axis fibers with their
canonical counterparts. This conclusion concerns the whole actual cut
curve, even if the curve is not a graph over the physical angle. It
provides the precise single exceptional radius when extending identities
on a reflection axis from the two open halves.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

def canonicalAxisAngle (halfAxis : Bool) : ℝ :=
  if halfAxis then Real.pi / 2 else 0

theorem canonicalCutPoint_axis_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalReferenceCutPairs S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (halfAxis : Bool) (θ : ℝ) :
    (canonicalCutPoint S K z m θ).2 = canonicalAxisAngle halfAxis ↔
      θ = canonicalAxisAngle halfAxis := by
  obtain ⟨_, _, _, _, _, hρ, hleft, _, hright, _⟩ := hcut m
  have hq : (K.cutRadius m, θ) ∈ canonicalClosed S K (K.cutPair m).1 := by
    refine ⟨?_, mem_univ _⟩
    rw [hleft, hright]
    exact ⟨hρ.le, le_rfl⟩
  cases halfAxis
  · simpa only [canonicalCutPoint, canonicalAxisAngle, Bool.false_eq_true, ↓reduceIte]
      using canonicalInverse_zero_axis_iff hA hz hs (K.cutPair m).1 hq
  · simpa only [canonicalCutPoint, canonicalAxisAngle, ↓reduceIte]
      using canonicalInverse_half_pi_axis_iff hA hz hs (K.cutPair m).1 hq

theorem mem_canonicalCut_on_axis_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalReferenceCutPairs S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (halfAxis : Bool) (r : ℝ) :
    (r, canonicalAxisAngle halfAxis) ∈ Set.range (canonicalCutPoint S K z m) ↔
      r = (canonicalCutPoint S K z m (canonicalAxisAngle halfAxis)).1 := by
  constructor
  · rintro ⟨θ, hθ⟩
    have ha : θ = canonicalAxisAngle halfAxis :=
      (canonicalCutPoint_axis_iff hA hcut hz hs m halfAxis θ).mp
        (congrArg Prod.snd hθ)
    subst θ
    exact (congrArg Prod.fst hθ).symm
  · intro hr
    refine ⟨canonicalAxisAngle halfAxis, ?_⟩
    exact Prod.ext hr.symm
      ((canonicalCutPoint_axis_iff hA hcut hz hs m halfAxis _).mpr rfl)

theorem canonicalCutPoint_period_add
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalReferenceCutPairs S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    canonicalCutPoint S K z m (θ + Real.pi) =
      canonicalCutPoint S K z m θ + (0, Real.pi) := by
  obtain ⟨_, _, _, _, _, hρ, hleft, _, hright, _⟩ := hcut m
  have hq : (K.cutRadius m, θ) ∈ canonicalClosed S K (K.cutPair m).1 := by
    refine ⟨?_, mem_univ _⟩
    rw [hleft, hright]
    exact ⟨hρ.le, le_rfl⟩
  simpa only [canonicalCutPoint, Prod.mk_add_mk, add_zero] using
    canonicalInverse_periodic_on_closed hA hz hs (K.cutPair m).1 hq

private theorem curveLift_int_period
    {Γ : ℝ → PolarPoint} {P : ℝ}
    (hperiod : ∀ t, Γ (t + P) = Γ t + (0, P)) (t : ℝ) (n : ℤ) :
    Γ (t + (n : ℝ) * P) = Γ t + (0, (n : ℝ) * P) := by
  have hp : Function.Periodic (fun θ => Γ θ - (0, θ)) P := by
    intro θ
    change Γ (θ + P) - (0, θ + P) = Γ θ - (0, θ)
    rw [hperiod]
    apply Prod.ext
    · simp only [Prod.fst_sub, Prod.fst_add, sub_zero, add_zero]
    · simp only [Prod.snd_sub, Prod.snd_add]
      ring
  have he : Γ (t + (n : ℝ) * P) - (0, t + (n : ℝ) * P) =
      Γ t - (0, t) := hp.int_mul n t
  apply Prod.ext
  · simpa only [Prod.fst_sub, Prod.fst_add, sub_zero, add_zero] using congrArg Prod.fst he
  · have hangle := congrArg Prod.snd he
    simp only [Prod.snd_sub, Prod.snd_add] at hangle ⊢
    linarith only [hangle]

/-- A zero of sin(2θ) belongs to one of the two fundamental axes after
an integer π translation. -/
theorem exists_axisAngle_int_translate_of_sin_two_eq_zero
    {θ : ℝ} (hθ : Real.sin (2 * θ) = 0) :
    ∃ side : Bool, ∃ n : ℤ, θ = canonicalAxisAngle side + (n : ℝ) * Real.pi := by
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hθ
  rcases Int.emod_two_eq_zero_or_one k with heven | hodd
  · have hki : k = 2 * (k / 2) := by omega
    have hkr : (k : ℝ) = 2 * ((k / 2 : ℤ) : ℝ) := by exact_mod_cast hki
    refine ⟨false, k / 2, ?_⟩
    simp only [canonicalAxisAngle, Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [hkr] at hk
    linarith only [hk]
  · have hki : k = 2 * (k / 2) + 1 := by omega
    have hkr : (k : ℝ) = 2 * ((k / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast hki
    refine ⟨true, k / 2, ?_⟩
    simp only [canonicalAxisAngle, ↓reduceIte]
    rw [hkr] at hk
    linarith only [hk]

theorem canonicalCutPoint_radial_eq_of_axis_translate
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalReferenceCutPairs S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (n : ℤ) (θ : ℝ)
    (hang : (canonicalCutPoint S K z m θ).2 =
      canonicalAxisAngle side + (n : ℝ) * Real.pi) :
    (canonicalCutPoint S K z m θ).1 =
      (canonicalCutPoint S K z m (canonicalAxisAngle side)).1 := by
  have he := curveLift_int_period (canonicalCutPoint_period_add hA hcut hz hs m)
    (θ - (n : ℝ) * Real.pi) n
  rw [sub_add_cancel] at he
  have hnear : (canonicalCutPoint S K z m (θ - (n : ℝ) * Real.pi)).2 =
      canonicalAxisAngle side := by
    have hangle := congrArg Prod.snd he
    simp only [Prod.snd_add] at hangle
    linarith only [hangle, hang]
  have hθ := (canonicalCutPoint_axis_iff hA hcut hz hs m side _).mp hnear
  have hr := congrArg Prod.fst he
  simpa only [Prod.fst_add, add_zero, hθ] using hr

/-- Every lifted reflection-axis point on the cut has one of two fixed
physical radii. Characteristic paths need not cross the cut finitely often. -/
theorem canonicalCut_axis_radial_cases
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalReferenceCutPairs S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ Set.range (canonicalCutPoint S K z m))
    (haxis : Real.sin (2 * p.2) = 0) :
    p.1 = (canonicalCutPoint S K z m 0).1 ∨
      p.1 = (canonicalCutPoint S K z m (Real.pi / 2)).1 := by
  obtain ⟨θ, rfl⟩ := hp
  obtain ⟨side, n, hn⟩ := exists_axisAngle_int_translate_of_sin_two_eq_zero haxis
  have hr := canonicalCutPoint_radial_eq_of_axis_translate hA hcut hz hs m side n θ hn
  cases side
  · exact Or.inl (by simpa only [canonicalAxisAngle, Bool.false_eq_true, ↓reduceIte] using hr)
  · exact Or.inr (by simpa only [canonicalAxisAngle, ↓reduceIte] using hr)

end ContinuousFlexibility.Analysis
