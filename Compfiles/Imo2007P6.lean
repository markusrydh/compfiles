/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh, Codex
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2007, Problem 6

Let n be a positive integer. Consider
  S = {(x, y, z) : x, y, z ∈ {0, 1, ... , n}, x + y + z > 0}
as a set of (n + 1)³ - 1 points in three-dimensional space. Determine the smallest possible
number of planes, the union of which contains S but does not include (0, 0, 0).
-/

namespace Imo2007P6

abbrev Point := EuclideanSpace ℝ (Fin 3)
abbrev Plane := AffineSubspace ℝ Point
def IsPlane (P : Plane) : Prop := Module.finrank ℝ P.direction = 2

def S (n : ℕ) : Set Point :=
    { p | ∃ x y z : Fin (n + 1), x.val + y.val + z.val > 0 ∧ p = !₂[(x : ℝ), (y : ℝ), (z : ℝ)] }

def IsAdmissible (n : ℕ) (T : Finset Plane) : Prop :=
  (∀ p ∈ S n, ∃ P ∈ T, p ∈ P) ∧
  (∀ P ∈ T, IsPlane P ∧ !₂[0, 0, 0] ∉ P)

determine solution_value (n : ℕ+) : ℕ := 3 * n

snip begin

def coordSum : Point →ₗ[ℝ] ℝ where
  toFun p := p 0 + p 1 + p 2
  map_add' p q := by simp [add_assoc, add_left_comm]
  map_smul' r p := by simp [mul_add, add_assoc]

def planeXYZ (c : ℝ) : AffineSubspace ℝ Point where
  carrier := {p | coordSum p = c}
  smul_vsub_vadd_mem := by aesop

lemma planeXYZ_inj : Function.Injective planeXYZ := by
  intro c d h
  let p := !₂[c, 0, 0]
  have hcsum : coordSum p = c := by simp [p, coordSum]
  have hc : p ∈ planeXYZ c := hcsum
  have hd : p ∈ planeXYZ d := by simpa [h] using hc
  have hdsum : coordSum p = d := hd
  simpa [p, coordSum] using hdsum

@[simp]
lemma planeXYZ_mem {a : ℝ} : !₂[a, 0, 0] ∈ planeXYZ a := by
  change coordSum !₂[(a : ℝ), 0, 0] = a
  simp [coordSum]

lemma planeXYZ_direction (a : ℝ) : (planeXYZ a).direction = LinearMap.ker coordSum := by
  have hnonempty : (planeXYZ a : Set Point).Nonempty := ⟨!₂[(a : ℝ), 0, 0], by simp⟩
  ext v
  rw [AffineSubspace.mem_direction_iff_eq_vsub hnonempty, LinearMap.mem_ker]
  constructor
  · rintro ⟨p1, hp1, p2, hp2, rfl⟩
    simp [show coordSum p1 = a by exact hp1, show coordSum p2 = a by exact hp2]
  · intro hv
    refine ⟨v + !₂[(a : ℝ), 0, 0], ?_, !₂[(a : ℝ), 0, 0], by simp, by simp⟩
    have hv' : v 0 + v 1 + v 2 = 0 := hv
    change coordSum (v + !₂[(a : ℝ), 0, 0] : Point) = a
    simp [coordSum]
    linarith

lemma isPlane_planeXYZ (a : ℝ) : IsPlane (planeXYZ a) := by
  have hrange : LinearMap.range coordSum = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    exact ⟨!₂[r, 0, 0], by simp [coordSum]⟩
  have hrank_range : Module.finrank ℝ (LinearMap.range coordSum) = 1 := by
    rw [hrange, finrank_top, Module.finrank_self]
  have hfin := coordSum.finrank_range_add_finrank_ker
  rw [hrank_range, finrank_euclideanSpace_fin] at hfin
  rw [IsPlane, planeXYZ_direction]
  linarith

lemma origin_not_mem_planeXYZ {a : ℝ} (ha : a ≠ 0) : !₂[0, 0, 0] ∉ planeXYZ a :=
  fun hzero ↦ ha (by simpa [planeXYZ, coordSum] using hzero.symm)

lemma solution_example (n : ℕ+) : ∃ T : Finset Plane, IsAdmissible n T ∧ T.card = 3 * n := by
  let T : Finset Plane := ((Finset.Icc 1 (3 * n.val)).map ⟨Nat.cast, Nat.cast_injective⟩).map ⟨planeXYZ, planeXYZ_inj⟩
  use T
  have hcover : ∀ p ∈ S n, ∃ P ∈ T, p ∈ P := by
    intro p hp
    use planeXYZ (coordSum p)
    constructor
    · have hcoordsum : coordSum p ∈ ((Finset.Icc 1 (3 * n.val)).map ⟨Nat.cast, Nat.cast_injective⟩) := by
        rcases hp with ⟨x, y, z, hxyz, rfl⟩
        let k : ℕ := x.val + y.val + z.val
        simp [Finset.mem_map, Finset.mem_Icc, coordSum]
        exact ⟨k, by lia, by simp [k, add_assoc, add_left_comm, add_comm]⟩
      exact (Finset.mem_map_mk planeXYZ planeXYZ_inj).mpr hcoordsum
    · exact (AffineSubspace.mem_coe ℝ Point p (planeXYZ (coordSum p))).mp rfl
  have hplanes : ∀ P ∈ T, IsPlane P ∧ !₂[0, 0, 0] ∉ P := by
    intro P hP
    simp [T] at hP
    obtain ⟨a, ha, h⟩ := hP
    have ha_ne_zero : (a : ℝ) ≠ 0 := by grind only [Nat.cast_ne_zero]
    constructor <;> rw [← h]
    · exact isPlane_planeXYZ a
    · exact origin_not_mem_planeXYZ ha_ne_zero
  exact ⟨⟨hcover, hplanes⟩, by aesop⟩

def S' (n : ℕ) : Fin 3 → Finset ℝ := fun _ ↦ (Finset.range (n + 1)).map ⟨Nat.cast, Nat.cast_injective⟩

lemma S'_mem_S_of_ne_zero {n : ℕ} {x : Fin 3 → ℝ} : x ≠ 0 → (∀ i, x i ∈ S' n i) → !₂[x 0, x 1, x 2] ∈ S n := by
  intro hx hx_mem_S'
  simp [S'] at hx_mem_S'
  rcases hx_mem_S' 0 with ⟨x0, hx0_le, hx0_eq⟩
  rcases hx_mem_S' 1 with ⟨x1, hx1_le, hx1_eq⟩
  rcases hx_mem_S' 2 with ⟨x2, hx2_le, hx2_eq⟩
  refine ⟨⟨x0, Nat.lt_succ_of_le hx0_le⟩, ⟨x1, Nat.lt_succ_of_le hx1_le⟩,
    ⟨x2, Nat.lt_succ_of_le hx2_le⟩, ?_, ?_⟩
  · by_contra hsum
    simp at hsum
    have hx0_zero : x0 = 0 := by lia
    have hx1_zero : x1 = 0 := by lia
    have hx2_zero : x2 = 0 := by lia
    apply hx
    ext i
    fin_cases i <;> simp [← hx0_eq, ← hx1_eq, ← hx2_eq, hx0_zero, hx1_zero, hx2_zero]
  · simp [hx0_eq, hx1_eq, hx2_eq]

def IsZeroExceptOrigin (S : Fin 3 → Finset ℝ) (P : MvPolynomial (Fin 3) ℝ) : Prop :=
    (∀ x ≠ 0, (∀ i : Fin 3, x i ∈ S i) → P.eval x = 0) ∧ P.eval 0 ≠ 0

lemma poly_totalDegree_eq_one' (a : Fin 3 → ℝ) (ha : a ≠ 0) :
    (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i).totalDegree = 1 := by
  have h_a_ne_zero : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := h_a_ne_zero
  apply le_antisymm
  · refine (MvPolynomial.totalDegree_finset_sum Finset.univ
      (fun i => MvPolynomial.C (a i) * MvPolynomial.X i)).trans ?_
    apply Finset.sup_le
    intro j hj
    simpa [← MvPolynomial.smul_eq_C_mul] using MvPolynomial.totalDegree_smul_le (a j) (MvPolynomial.X (R := ℝ) j)
  · have hcoeff_ne : MvPolynomial.coeff (Finsupp.single i 1)
        (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j : MvPolynomial (Fin 3) ℝ) ≠ 0 := by
      simpa [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul] using hi
    have hmem : Finsupp.single i 1 ∈
        (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j : MvPolynomial (Fin 3) ℝ).support := by
      rwa [MvPolynomial.mem_support_iff]
    simpa [Finsupp.degree_single] using MvPolynomial.le_totalDegree hmem

lemma poly_totalDegree_eq_one (a : Fin 3 → ℝ) (c : ℝ) (ha : a ≠ 0) :
    (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i + MvPolynomial.C c).totalDegree = 1 := by
  set P₁ := ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i
  set P₂ := MvPolynomial.C (σ := Fin 3) c
  have hP₁_totalDegree : P₁.totalDegree = 1 := poly_totalDegree_eq_one' a ha
  have hP₂_totalDegree : P₂.totalDegree = 0 := by simp [P₂]
  have h : P₂.totalDegree < P₁.totalDegree := by lia
  simpa [P₁, P₂, hP₁_totalDegree] using MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt h

lemma exists_poly_of_Plane {t : Plane} (ht : IsPlane t ∧ !₂[0, 0, 0] ∉ t) :
    ∃ P : MvPolynomial (Fin 3) ℝ, P.totalDegree = 1 ∧ P.eval 0 ≠ 0 ∧ ∀ x ∈ t, P.eval x = 0 := by
  have : Module.finrank ℝ t.directionᗮ = 1 := by
    have h₁ : Module.finrank ℝ Point = 3 := finrank_euclideanSpace_fin
    rw [← Submodule.finrank_add_finrank_orthogonal t.direction, ht.1] at h₁
    linarith
  have htnorm_ne_bot : t.directionᗮ ≠ ⊥ := by
    intro hbot
    have hfin0 : Module.finrank ℝ t.directionᗮ = 0 := by simp [hbot]
    linarith
  obtain ⟨a, ha, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot htnorm_ne_bot

  let L : Point →ₗ[ℝ] ℝ := innerSL ℝ a
  have hL_ne : L ≠ 0 := by
    intro hL
    have happly := congrArg (fun (L : Point →ₗ[ℝ] ℝ) => L a) hL
    simp [L] at happly
    exact ha_ne happly
  have hker : LinearMap.ker L = t.direction := by
    have hdir_le_ker : t.direction ≤ LinearMap.ker L := by
      intro i hi
      simp [L]
      exact inner_eq_zero_symm.mp (ha i hi)
    have hfin : Module.finrank ℝ t.direction = Module.finrank ℝ (LinearMap.ker L) := by
      have hker_add_one := Module.Dual.finrank_ker_add_one_of_ne_zero (f := L) hL_ne
      have hpoint : Module.finrank ℝ Point = 3 := finrank_euclideanSpace_fin
      have htdir : Module.finrank ℝ t.direction = 2 := ht.1
      rw [hpoint] at hker_add_one
      linarith
    exact (Submodule.eq_of_le_of_finrank_eq hdir_le_ker hfin).symm

  have hnonempty : (t : Set Point).Nonempty := by
    have := ht.1
    unfold IsPlane at this
    have hfin : 0 < Module.finrank ℝ t.direction := by simp [this]
    have ht_ne_bot : t ≠ ⊥ := by
      intro ht_eq_bot
      have : Module.finrank ℝ (⊥ : AffineSubspace ℝ Point).direction = 0 := by simp
      rw [← ht_eq_bot] at this
      linarith [ht.1]
    exact (AffineSubspace.nonempty_iff_ne_bot t).mpr ht_ne_bot
  obtain ⟨p₀, hp₀⟩ := hnonempty

  let P := (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i) + MvPolynomial.C (-(L p₀))
  use P
  have hPdeg : P.totalDegree = 1 := poly_totalDegree_eq_one a (-L p₀) (ne_of_apply_ne (WithLp.toLp 2) (ha_ne))
  have hPorigin : P.eval 0 ≠ 0 := by
    have hzero_not_mem_t : 0 ∉ t := by
      have : (0 : Point) = !₂[0, 0, 0] := by ext i; fin_cases i <;> simp
      simp [this, ht.2]
    have hp₀_ne_zero : p₀ ≠ 0 := ne_of_mem_of_not_mem hp₀ hzero_not_mem_t
    simp [P]
    by_contra hLp₀_eq_zero
    have hp₀_mem_t_direction : p₀ ∈ t.direction := by simpa [hker] using LinearMap.mem_ker.mpr hLp₀_eq_zero
    have hneg_p₀_mem_t_direction : -p₀ ∈ t.direction := Submodule.neg_mem (AffineSubspace.direction t) hp₀_mem_t_direction
    have hzero_mem_t : (0 : Point) ∈ t := by
      have hp₀' : p₀ ∈ t := (AffineSubspace.mem_coe ℝ Point p₀ t).mp hp₀
      rw [show 0 = -p₀ +ᵥ p₀ by simp]
      exact AffineSubspace.vadd_mem_of_mem_direction hneg_p₀_mem_t_direction hp₀'
    exact hzero_not_mem_t hzero_mem_t
  have hPzeros : ∀ p ∈ t, P.eval p = 0 := by
    intro p hp
    have h : p -ᵥ p₀ ∈ t.direction := AffineSubspace.vsub_mem_direction hp hp₀
    replace h : L (p -ᵥ p₀) = 0 := by
      rw [← hker] at h
      exact LinearMap.mem_ker.mp h
    replace h : L p = L p₀ := LinearMap.sub_mem_ker_iff.mp h
    have hPL : ∀ x, P.eval x.ofLp = L x - L p₀ := by
      exact fun p ↦ by simp [P, MvPolynomial.eval_add, MvPolynomial.eval_C, sub_eq_add_neg, L, inner, mul_comm]
    simp [hPL p, h]
  exact ⟨hPdeg, hPorigin, hPzeros⟩

lemma ne_zero {x : Fin 3 → ℝ} {P : MvPolynomial (Fin 3) ℝ} : P.eval x ≠ 0 → P ≠ 0 :=
  fun h ↦ Ne.symm (ne_of_apply_ne ⇑(MvPolynomial.eval x) fun a ↦ h (Eq.symm a))

noncomputable instance : DecidableEq Plane := Classical.decEq _

lemma exists_poly_of_FinsetPlane {T : Finset Plane} (hT : ∀ t ∈ T, IsPlane t ∧ !₂[0, 0, 0] ∉ t) :
    ∃ P : MvPolynomial (Fin 3) ℝ, P.totalDegree = T.card ∧ P.eval 0 ≠ 0 ∧ ∀ x, (∃ t ∈ T, x ∈ t) → P.eval x = 0 := by
  induction T using Finset.induction_on with
  | empty => use 1 ; split_ands <;> simp
  | insert t T ht_not_mem_T hT' =>
    rcases exists_poly_of_Plane (hT t (Finset.mem_insert_self t T)) with ⟨Q, hQdeg, hQorigin, hQzeros⟩
    rcases hT' (fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)) with ⟨R, hRdeg, hRorigin, hRzeros⟩
    use Q * R
    split_ands
    · rw [MvPolynomial.totalDegree_mul_of_isDomain (ne_zero hQorigin) (ne_zero hRorigin), hQdeg, hRdeg,
        Finset.card_insert_of_notMem ht_not_mem_T, add_comm]
    · aesop
    · intro x hx_ex_mem
      obtain ⟨r, hr, hx_mem_r⟩ := hx_ex_mem
      by_cases hcase : r = t
      · simp [hQzeros x (by rwa [←hcase])]
      · simp [hRzeros x ⟨r, by simpa [Or.resolve_left, hcase] using hr, hx_mem_r⟩]

lemma exists_poly_of_IsAdmissible {n : ℕ} {T : Finset Plane} (hT : IsAdmissible n T) :
    ∃ P : MvPolynomial (Fin 3) ℝ, P.totalDegree = T.card ∧ IsZeroExceptOrigin (S' n) P := by
  rcases exists_poly_of_FinsetPlane hT.2 with ⟨P, hPdeg, hPorigin, hPzero⟩
  use P
  unfold IsZeroExceptOrigin
  have : ∀ (x : Fin 3 → ℝ), x ≠ 0 → (∀ (i : Fin 3), x i ∈ S' n i) → (MvPolynomial.eval x) P = 0 := by
    intro x hx hx_mem_S'
    let x' := !₂[x 0, x 1, x 2]
    rw [Eq.symm (WeierstrassCurve.Jacobian.fin3_def x), hPzero x' (hT.1 x' (S'_mem_S_of_ne_zero hx hx_mem_S'))]
  exact ⟨hPdeg, this, hPorigin⟩

noncomputable def rootFactor (i : Fin 3) (x : ℝ) := MvPolynomial.X i - MvPolynomial.C x
noncomputable def rootsInCoord (S : Fin 3 → Finset ℝ) (i : Fin 3) := ∏ x ∈ S i, rootFactor i x
noncomputable def PolyFromRoots (S : Fin 3 → Finset ℝ) := ∏ i : Fin 3, rootsInCoord S i

@[simp]
lemma coeff_rootFactor (i : Fin 3) (y : ℝ) :
    MvPolynomial.coeff (Finsupp.single i 1) (rootFactor i y) = 1 := by
  simp [rootFactor, MvPolynomial.coeff_sub, MvPolynomial.coeff_C]
  intro h
  simpa using (DFunLike.congr (x := i) h rfl)

@[simp]
lemma totalDegree_rootFactor (i : Fin 3) (y : ℝ) : (rootFactor i y).totalDegree = 1 := by
  apply le_antisymm
  · simpa [rootFactor] using MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X i) y
  · simpa using MvPolynomial.le_totalDegree (show Finsupp.single i 1 ∈ (rootFactor i y).support by simp)

lemma rootFactor_ne_zero (i : Fin 3) (y : ℝ) : rootFactor i y ≠ 0 :=
  fun hzero ↦ by simpa [hzero] using (coeff_rootFactor i y)

@[simp]
lemma totalDegree_finset_prod_of_isDomain {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → MvPolynomial (Fin 3) ℝ} :
    (∀ i ∈ s, f i ≠ 0) → (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  refine Finset.induction_on s (fun hf ↦ by simp) ?_
  intro i T hiT hT hf
  have hT_degree := hT (fun j hj => hf j (Finset.mem_insert_of_mem hj))
  rw [Finset.prod_insert hiT, Finset.sum_insert hiT]
  rw [MvPolynomial.totalDegree_mul_of_isDomain (hf i (Finset.mem_insert_self i T)), hT_degree]
  · exact (Finset.prod_ne_zero_iff).mpr fun j hj => hf j (Finset.mem_insert_of_mem hj)

lemma totalDegree_rootsInCoord (S : Fin 3 → Finset ℝ) (i : Fin 3) :
    (rootsInCoord S i).totalDegree = (S i).card := by
  simp [rootsInCoord, rootFactor_ne_zero]

lemma rootsInCoord_ne_zero (S : Fin 3 → Finset ℝ) (i : Fin 3) : rootsInCoord S i ≠ 0 :=
    (Finset.prod_ne_zero_iff).mpr (fun z _ => rootFactor_ne_zero i z)

lemma totalDegree {S : Fin 3 → Finset ℝ} {A : MvPolynomial (Fin 3) ℝ} :
    A = PolyFromRoots S → A.totalDegree = ∑ i, (S i).card :=
  fun hA ↦ by simp [hA, PolyFromRoots, totalDegree_rootsInCoord, rootsInCoord_ne_zero]

lemma coeff_rootFactor_mul_top {p : MvPolynomial (Fin 3) ℝ} {t : Fin 3 →₀ ℕ}
    {i : Fin 3} {y : ℝ} (hpdeg : p.totalDegree = t.degree) (hpcoeff : p.coeff t = 1) :
    (rootFactor i y * p).coeff (t + Finsupp.single i 1) = 1 := by
  have hC : MvPolynomial.coeff (t + Finsupp.single i 1) (MvPolynomial.C y * p) = 0 := by
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_eq_zero_of_totalDegree_lt, mul_zero]
    · rw [hpdeg, ← Finsupp.degree_apply, map_add, Finsupp.degree_single]
      lia
  simp [rootFactor, sub_mul, MvPolynomial.coeff_sub, MvPolynomial.coeff_X_mul', ↓reduceIte, hpcoeff, hC, sub_zero]

lemma coeff_rootFactorFinset_mul_top (s : Finset ℝ) (i : Fin 3)
    {p : MvPolynomial (Fin 3) ℝ} {t : Fin 3 →₀ ℕ}
    (hpdeg : p.totalDegree = t.degree) (hpcoeff : p.coeff t = 1) :
    ((∏ y ∈ s, rootFactor i y) * p).coeff (t + Finsupp.single i s.card) = 1 := by
  induction s using Finset.induction_on with
  | empty => simp [hpcoeff]
  | insert y T hyT hT =>
      have hprevdeg : ((∏ y ∈ T, rootFactor i y) * p).totalDegree =
          (t + Finsupp.single i T.card).degree := by
        have hpne : p ≠ 0 := fun hp ↦ by simp [hp] at hpcoeff
        have hprod_ne : (∏ y ∈ T, rootFactor i y) ≠ 0 :=
          (Finset.prod_ne_zero_iff).mpr (fun z _ => rootFactor_ne_zero i z)
        rw [MvPolynomial.totalDegree_mul_of_isDomain hprod_ne hpne]
        rw [totalDegree_finset_prod_of_isDomain (fun z _ => rootFactor_ne_zero i z)]
        simp [hpdeg, map_add, Finsupp.degree_single]
        lia
      rw [Finset.prod_insert hyT, Finset.card_insert_of_notMem hyT, mul_assoc]
      convert coeff_rootFactor_mul_top hprevdeg hT using 2
      ext j
      simp [add_assoc]

lemma coeff_rootsInCoordFinset_top (S : Fin 3 → Finset ℝ) (U : Finset (Fin 3)) :
    (∏ i ∈ U, rootsInCoord S i).coeff (∑ i ∈ U, Finsupp.single i (S i).card) = 1 := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert i T hiT hT =>
      rw [Finset.prod_insert hiT, Finset.sum_insert hiT]
      have hprevdeg : (∏ i ∈ T, rootsInCoord S i).totalDegree =
          (∑ i ∈ T, Finsupp.single i (S i).card).degree := by
        rw [totalDegree_finset_prod_of_isDomain (fun j _ => rootsInCoord_ne_zero S j)]
        simp [totalDegree_rootsInCoord]
      rw [rootsInCoord]
      convert coeff_rootFactorFinset_mul_top (S i) i hprevdeg hT using 2
      ext j
      simp
      lia

lemma coeff_card {S : Fin 3 → Finset ℝ} {A : MvPolynomial (Fin 3) ℝ}
    {t : Fin 3 →₀ ℕ} (hA : A = PolyFromRoots S) (ht : ∀ i, t i = (S i).card) :
    A.coeff t = 1 := by
  rw [hA, PolyFromRoots]
  convert coeff_rootsInCoordFinset_top S Finset.univ using 2
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three, ht]

lemma eval_rootsInCoord_eq_zero {S : Fin 3 → Finset ℝ} {x : Fin 3 → ℝ} {i : Fin 3} (hi : x i ∈ S i) :
    (rootsInCoord S i).eval x = 0 := by
  simpa [rootsInCoord] using (Finset.prod_eq_zero hi (by simp [rootFactor]))

lemma zeros {S : Fin 3 → Finset ℝ} {A : MvPolynomial (Fin 3) ℝ} : A = PolyFromRoots S →
    ∀ x, (∃ i, x i ∈ S i) → A.eval x = 0 := by
  intro hA x hx
  rcases hx with ⟨i, hi⟩
  simpa [hA, PolyFromRoots] using (Finset.prod_eq_zero (Finset.mem_univ i) (eval_rootsInCoord_eq_zero hi))

lemma min_total_degree {n : ℕ} {B : MvPolynomial (Fin 3) ℝ}
    (h : IsZeroExceptOrigin (S' n) B) :
    3 * n ≤ B.totalDegree := by
  by_contra h_deg_less
  simp at h_deg_less

  let S'' : Fin 3 → Finset ℝ := fun _ ↦ (Finset.Icc 1 n).map ⟨Nat.cast, Nat.cast_injective⟩
  let A := PolyFromRoots S''
  let α := (A.eval 0)/(B.eval 0)
  let P := A - α • B
  let t : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![n, n, n]
  have ht_degree : t.degree = 3 * n := by
    have : ∀ x, ![n, n, n] x = n := fun x ↦ by fin_cases x <;> simp
    simp [t, Finsupp.equivFunOnFinite_symm_eq_sum, this]

  have hP_coeff : P.coeff t = 1 := by
    have h₁ : A.coeff t = 1 := by
      apply coeff_card (A := A) rfl
      intro i
      fin_cases i <;> simp [t, S'']
    have h₂ : B.coeff t = 0 := by
      rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
      · rwa [←Finsupp.degree_apply, ht_degree]
    have : P.coeff t = A.coeff t - α * B.coeff t := rfl
    simp [this, h₁, h₂]

  have hP_deg : P.totalDegree = t.degree := by
    have h₁ : P.totalDegree = 3 * n := by
      have h_lt : P.totalDegree ≤ 3 * n := by
        have : max A.totalDegree (α • B).totalDegree = 3 * n := by
          simp [totalDegree (A := A) rfl, S'']
          calc
            (α • B).totalDegree ≤ B.totalDegree := MvPolynomial.totalDegree_smul_le α B
            _ ≤ 3 * n := le_of_lt h_deg_less
        simp [P]
        rw [← this]
        apply MvPolynomial.totalDegree_sub
      have h : P.coeff t ≠ 0 → t.degree ≤ P.totalDegree := by
        grind only [Finsupp.degree_apply, MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
      have h_gt := h (ne_zero_of_eq_one hP_coeff)
      rw [ht_degree] at h_gt
      exact Nat.le_antisymm h_lt h_gt
    rwa [← ht_degree] at h₁

  have htS : ∀ i : Fin 3, t i < (S' n i).card := fun i ↦ by fin_cases i <;> simp [S', t]
  rcases (MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero P t (ne_zero_of_eq_one hP_coeff) hP_deg (S' n) htS) with ⟨s, hs_mem_S', hP_eval_s_ne_zero⟩

  have hP_zero : ∀ x, (∀ i : Fin 3, x i ∈ S' n i) → P.eval x = 0 := by
    intro x hx
    unfold P α
    rw [MvPolynomial.eval_sub, MvPolynomial.smul_eval]
    by_cases hx' : x = 0
    · rw [hx', div_mul_cancel₀ (A.eval 0) h.2]
      simp
    · simp [h.1 x hx' hx]
      have : ∃ i, x i ∈ S'' i := by
        have : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx'
        obtain ⟨j, hj⟩ := this
        use j
        have := hx j
        simp [S'']
        simp [S'] at this
        obtain ⟨a, ha⟩ := this
        use a
        rw [← ha.2] at hj
        have ha_ne_zero : a ≠ 0 := by aesop
        have ha_ge_one : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha_ne_zero
        exact ⟨⟨ha_ge_one, ha.1⟩, ha.2⟩
      exact (zeros rfl) x this

  exact hP_eval_s_ne_zero (hP_zero s hs_mem_S')

lemma solution_lowerBounds (n : ℕ+) : solution_value n ∈ lowerBounds {k | ∃ T, IsAdmissible (↑n) T ∧ T.card = k} := by
  simp [mem_lowerBounds, solution_value]
  intro T hT
  rcases (exists_poly_of_IsAdmissible hT) with ⟨B, hB_deg, hB_zero⟩
  rw [← hB_deg]
  apply min_total_degree hB_zero

snip end

problem imo2007_p6 (n : ℕ+) :
    IsLeast { k | ∃ T : Finset Plane, IsAdmissible n T ∧ T.card = k } (solution_value n) := ⟨solution_example n, solution_lowerBounds n⟩

end Imo2007P6
