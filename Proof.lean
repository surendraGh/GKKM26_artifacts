-- Copy & Paste in https://live.lean-lang.org/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Basic.Real.Basic

open BigOperators

namespace Rounding2

notation "ℝ^[" d "]" => Fin d → ℝ

/-- The property `isRoundingScheme d k γ f` for a function `f : ℝ^[d] → ℝ^[d]`:
1. The distance in ℓ_∞ norm between `f z` and `z` is at most 1.
2. For any point `z`, the image of the ℓ_∞ ball of radius `γ` around `z` under `f`
   has cardinality at most `k`. -/
def isRoundingScheme (d : ℕ) (k : ℕ) (γ : ℝ) (f : ℝ^[d] → ℝ^[d]) : Prop :=
  (∀ z : ℝ^[d], ∀ i : Fin d, |f z i - z i| ≤ 1) ∧
  (∀ z : ℝ^[d], ∃ s : Finset (ℝ^[d]),
    (∀ y : ℝ^[d], (∀ i : Fin d, |y i - z i| ≤ γ) → f y ∈ s) ∧ s.card ≤ k)

/-- Natural-number ceiling division ⌈d/l⌉₊ -/
def cdiv (d l : ℕ) : ℕ := (d + l - 1) / l

/-- Round a real number to the nearest integer, rounding half up. -/
noncomputable def round (x : ℝ) : ℤ := ⌊x + 1/2⌋

/-- For any real number `x`, rounding `x` gives an integer. -/
theorem round_is_int (x : ℝ) : ∃ (n : ℤ), (round x : ℝ) = n :=
  ⟨round x, rfl⟩

/-- The potential function Φ_a(x) which sums the fractional parts of the shifted coordinates. -/
noncomputable def Phi (d : ℕ) (x : ℝ^[d]) (a : Fin d) : ℝ :=
  ∑ i : Fin d, Int.fract (x i - (a.val : ℝ) / d)

/-- A helper function to find the argmin of a function over a List classically. -/
noncomputable def listArgmin {α : Type*} (g : α → ℝ) : List α → α → α
  | [], acc => acc
  | x :: xs, acc => if g x < g acc then listArgmin g xs x else listArgmin g xs acc

/-- Find the argmin of a function over Fin d, breaking ties by choosing the smallest index. -/
noncomputable def argmin (d : ℕ) (g : Fin d → ℝ) (default : Fin d) : Fin d :=
  listArgmin g (List.finRange d) default

/-- The shift A(x) minimizing Phi_a(x) over all a ∈ [d].
    Ties are broken by choosing the smallest such a. -/
noncomputable def A (d : ℕ) (hd : 0 < d) (x : ℝ^[d]) : Fin d :=
  argmin d (fun a => Phi d x a) ⟨0, hd⟩

/-- The integer coordinate label Z(x)_i = ⌊x_i - A(x)/d⌋. -/
noncomputable def Z (d : ℕ) (hd : 0 < d) (x : ℝ^[d]) (i : Fin d) : ℤ :=
  ⌊x i - (A d hd x).val / (d : ℝ)⌋

/-- The rounding function f(x)_i = Z(x)_i + A(x)/d. -/
noncomputable def f_round (d : ℕ) (hd : 0 < d) (x : ℝ^[d]) : ℝ^[d] :=
  fun i => (Z d hd x i : ℝ) + (A d hd x).val / (d : ℝ)

/-- Cube membership (RS1): every coordinate `x_i` is close to `f_round(x)_i`. -/
lemma f_round_rs1 (d : ℕ) (hd : 0 < d) (x : ℝ^[d]) (i : Fin d) :
    f_round d hd x i ≤ x i ∧ x i < f_round d hd x i + 1 := by
  dsimp [f_round, Z]
  have h1 := Int.floor_le (x i - (A d hd x).val / (d : ℝ))
  have h2 := Int.lt_floor_add_one (x i - (A d hd x).val / (d : ℝ))
  constructor
  · linarith
  · linarith

/-- Helper lemma: listArgmin is always at least as good as the accumulator. -/
lemma listArgmin_le_acc {α : Type*} (g : α → ℝ) (l : List α) (acc : α) :
    g (listArgmin g l acc) ≤ g acc := by
  induction l generalizing acc with
  | nil =>
    dsimp [listArgmin]
    exact le_rfl
  | cons y ys ih =>
    dsimp [listArgmin]
    split_ifs with h
    · have h1 := ih y
      linarith
    · have h2 := ih acc
      exact h2

/-- Helper lemma: listArgmin is at least as good as any element in the list. -/
lemma listArgmin_le {α : Type*} (g : α → ℝ) (l : List α) (acc : α) (b : α) (hb : b ∈ l) :
    g (listArgmin g l acc) ≤ g b := by
  induction l generalizing acc with
  | nil =>
    contradiction
  | cons y ys ih =>
    dsimp [listArgmin]
    split_ifs with h
    · rcases List.mem_cons.mp hb with rfl | hb_in
      · exact listArgmin_le_acc g ys b
      · exact ih y hb_in
    · rcases List.mem_cons.mp hb with rfl | hb_in
      · have h1 := listArgmin_le_acc g ys acc
        linarith
      · exact ih acc hb_in

/-- A minimizes the potential function Phi. -/
lemma A_is_minimizer (d : ℕ) (hd : 0 < d) (x : ℝ^[d]) (b : Fin d) :
    Phi d x (A d hd x) ≤ Phi d x b := by
  dsimp [A, argmin]
  apply listArgmin_le (fun a => Phi d x a) (List.finRange d) ⟨0, hd⟩ b
  exact List.mem_finRange b

/-- Helper lemma: floor of (y + m/d) is either 1 (if y ≥ 1 - m/d) or 0. -/
lemma floor_add_cases (y : ℝ) (hy : 0 ≤ y ∧ y < 1) (m d : ℕ) (hd : 0 < d) (hm : m ≤ d) :
    ⌊y + (m : ℝ) / (d : ℝ)⌋ = if 1 - (m : ℝ) / (d : ℝ) ≤ y then 1 else 0 := by
  have hd_real : 0 < (d : ℝ) := by exact_mod_cast hd
  have hm_real : (m : ℝ) ≤ (d : ℝ) := by exact_mod_cast hm
  have h_div_ge : 0 ≤ (m : ℝ) / (d : ℝ) := by positivity
  have h_div_le : (m : ℝ) / (d : ℝ) ≤ 1 := by
    exact (div_le_one₀ hd_real).mpr hm_real
  split_ifs with h
  · apply Int.floor_eq_iff.mpr
    constructor
    · linarith
    · linarith
  · apply Int.floor_eq_iff.mpr
    constructor
    · linarith
    · linarith

/-- Helper lemma: difference of fract (y + m/d) and y. -/
lemma fract_add_diff (y : ℝ) (hy : 0 ≤ y ∧ y < 1) (m d : ℕ) (hd : 0 < d) (hm : m ≤ d) :
    Int.fract (y + (m : ℝ) / (d : ℝ)) - y = (m : ℝ) / (d : ℝ) -
      (if 1 - (m : ℝ) / (d : ℝ) ≤ y then 1 else 0) := by
  have h_floor := floor_add_cases y hy m d hd hm
  rw [← Int.self_sub_floor, h_floor]
  split_ifs with h <;> linarith

/-- Helper lemma: fract of shifted coordinates. -/
lemma fract_shift_diff (x : ℝ) (d : ℕ) (hd : 0 < d) (m : ℕ) (hm : m ≤ d) (a b : Fin d)
    (h_diff : b.val = (a.val + d - m) % d) :
    Int.fract (x - b.val / (d : ℝ)) =
      Int.fract (Int.fract (x - a.val / (d : ℝ)) + (m : ℝ) / (d : ℝ)) := by
  let q : ℤ := ((a.val + d - m) / d : ℕ)
  have h_div : (a.val : ℤ) + (d : ℤ) - (m : ℤ) = (d : ℤ) * q + (b.val : ℤ) := by
    let X := a.val + d - m
    have h_alg : X = d * (X / d) + b.val := by
      have h_div_mod := (Nat.div_add_mod X d).symm
      rw [h_diff]
      exact h_div_mod
    have h_alg_z : (X : ℤ) = (d : ℤ) * ((X / d : ℕ) : ℤ) + (b.val : ℤ) := by
      exact_mod_cast h_alg
    dsimp [q, X] at *
    omega
  have h_lh : Int.fract (x - b.val / (d : ℝ)) =
      Int.fract (x - a.val / (d : ℝ) + (m : ℝ) / (d : ℝ)) := by
    have h_eq : x - b.val / (d : ℝ) =
        (x - a.val / (d : ℝ) + (m : ℝ) / (d : ℝ)) + (q - 1 : ℤ) := by
      have hd_real : (d : ℝ) ≠ 0 := by positivity
      have h_div_real : (a.val : ℝ) + (d : ℝ) - (m : ℝ) = (d : ℝ) * (q : ℝ) + (b.val : ℝ) := by
        exact_mod_cast h_div
      push_cast
      field_simp
      linarith
    rw [h_eq]
    exact Int.fract_add_intCast _ _
  have h_rh : Int.fract (Int.fract (x - a.val / (d : ℝ)) + (m : ℝ) / (d : ℝ)) =
      Int.fract (x - a.val / (d : ℝ) + (m : ℝ) / (d : ℝ)) := by
    let z := x - a.val / d
    let y := (m : ℝ) / d
    have h_fract_def : Int.fract z = z - (⌊z⌋ : ℤ) := (Int.self_sub_floor _).symm
    have h_eq2 : Int.fract z + y = (z + y) + (-⌊z⌋ : ℤ) := by
      rw [h_fract_def]
      push_cast
      ring
    rw [h_eq2, Int.fract_add_intCast]
  rw [h_lh, h_rh]

/-- The difference in the potential function Phi between the minimizer a and shift b. -/
lemma Phi_diff (d : ℕ) (hd : 0 < d) (x : ℝ^[d]) (m : ℕ) (hm : m ≤ d) (a b : Fin d)
    (h_diff : b.val = (a.val + d - m) % d) :
    Phi d x b - Phi d x a = (m : ℝ) -
      ((Finset.filter (fun i =>
        1 - (m : ℝ) / d ≤ Int.fract (x i - a.val / (d : ℝ))) Finset.univ).card : ℝ) := by
  dsimp [Phi]
  rw [← Finset.sum_sub_distrib]
  have h_sum : ∑ i : Fin d, (Int.fract (x i - b.val / (d : ℝ)) -
      Int.fract (x i - a.val / (d : ℝ))) =
      ∑ i : Fin d, ((m : ℝ) / (d : ℝ) -
        (if 1 - (m : ℝ) / (d : ℝ) ≤ Int.fract (x i - a.val / (d : ℝ)) then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    have h_shift := fract_shift_diff (x i) d hd m hm a b h_diff
    rw [h_shift]
    have h_y_prop : 0 ≤ Int.fract (x i - a.val / (d : ℝ)) ∧
        Int.fract (x i - a.val / (d : ℝ)) < 1 := by
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    exact fract_add_diff (Int.fract (x i - a.val / (d : ℝ))) h_y_prop m d hd hm
  rw [h_sum]
  rw [Finset.sum_sub_distrib]
  have h_sum_const : ∑ _ : Fin d, (m : ℝ) / (d : ℝ) = (m : ℝ) := by
    simp
    have hd_real : (d : ℝ) ≠ 0 := by positivity
    field_simp
  rw [h_sum_const]
  simp only [Finset.sum_boole]

/-- Upper-boundary sparsity (RS2): coordinates with large fractional parts are sparse. -/
lemma f_round_rs2 (d : ℕ) (hd : 0 < d) (x : ℝ^[d]) (m : ℕ) (hm : m ≤ d) :
    (Finset.filter (fun i =>
      1 - (m : ℝ) / d ≤ Int.fract (x i - (A d hd x).val / (d : ℝ))) Finset.univ).card ≤ m := by
  let a := A d hd x
  have hd_pos : d > 0 := hd
  let b : Fin d := ⟨(a.val + d - m) % d, Nat.mod_lt _ hd_pos⟩
  have h_diff : b.val = (a.val + d - m) % d := rfl
  have h_min := A_is_minimizer d hd x b
  have h_diff_val := Phi_diff d hd x m hm a b h_diff
  have h_real : ((Finset.filter (fun i =>
      1 - (m : ℝ) / d ≤ Int.fract (x i - (A d hd x).val / (d : ℝ)))
        Finset.univ).card : ℝ) ≤ (m : ℝ) := by
    linarith
  exact_mod_cast h_real

/-- Helper lemma: fractional part bound for crossing coordinates. -/
lemma crossing_coord_bound (y : ℝ) (l d : ℕ) (hl : 3 ≤ l) (hd : 0 < d) (a : Fin d) (z : ℝ) (n : ℤ)
    (hyz : |y - z| ≤ 2 / (l : ℝ)) (_hn : n = ⌊z - 2 / (l : ℝ) - a.val / (d : ℝ)⌋)
    (h_cross : z + 2 / (l : ℝ) - a.val / (d : ℝ) ≥ (n : ℝ) + 1)
    (h_floor : ⌊y - a.val / (d : ℝ)⌋ = n) :
    Int.fract (y - a.val / (d : ℝ)) ≥ 1 - (cdiv (4 * d) l : ℝ) / (d : ℝ) := by
  let u := y - (a.val : ℝ) / (d : ℝ)
  have hu_fract : Int.fract u = u - (n : ℝ) := by
    rw [← Int.self_sub_floor u, h_floor]
  rw [hu_fract]
  have h_cdiv_mul : (cdiv (4 * d) l : ℝ) * (l : ℝ) ≥ 4 * (d : ℝ) := by
    have h_div_alg : (4 * d + l - 1) / l * l + (4 * d + l - 1) % l = 4 * d + l - 1 := by
      rw [mul_comm]
      exact Nat.div_add_mod (4 * d + l - 1) l
    have h_mod_lt : (4 * d + l - 1) % l < l := Nat.mod_lt (4 * d + l - 1) (by omega)
    have h_mod_le : (4 * d + l - 1) % l ≤ l - 1 := by omega
    have h_nat : (cdiv (4 * d) l) * l ≥ 4 * d := by
      dsimp [cdiv]
      omega
    exact_mod_cast h_nat
  have h_div_ge : ((cdiv (4 * d) l : ℝ) / (d : ℝ)) ≥ 4 / (l : ℝ) := by
    have hd_real : (d : ℝ) > 0 := by positivity
    have hl_real : (l : ℝ) > 0 := by positivity
    field_simp at h_cdiv_mul ⊢
    linarith
  have h_bound : u - (n : ℝ) ≥ 1 - 4 / (l : ℝ) := by
    have hy_ge : y ≥ z - 2 / (l : ℝ) := by linarith [abs_le.mp hyz]
    have hu_ge : u ≥ z - 2 / (l : ℝ) - a.val / (d : ℝ) := by
      dsimp [u]
      linarith
    have h_L : z - 2 / (l : ℝ) - (a.val : ℝ) / (d : ℝ) =
        (z + 2 / (l : ℝ) - (a.val : ℝ) / (d : ℝ)) - 4 / (l : ℝ) := by ring
    linarith
  linarith

/-- Helper lemma: Z_y coordinate floor belongs to {n, n + 1} for l ≥ 5. -/
lemma Z_y_in_set (y z : ℝ) (l d : ℕ) (hl : 5 ≤ l) (hd : 0 < d) (a : Fin d) (n : ℤ)
    (hyz : |y - z| ≤ 2 / (l : ℝ)) (hn : n = ⌊z - 2 / (l : ℝ) - a.val / (d : ℝ)⌋) :
    ⌊y - a.val / (d : ℝ)⌋ = n ∨ ⌊y - a.val / (d : ℝ)⌋ = n + 1 := by
  let u := y - (a.val : ℝ) / (d : ℝ)
  have _hd_real : (d : ℝ) > 0 := by positivity
  have _hl_real : (l : ℝ) > 0 := by positivity
  have h_floor_L : z - 2 / (l : ℝ) - a.val / (d : ℝ) ≥ (n : ℝ) := by
    rw [hn]
    exact Int.floor_le _
  have h_floor_L_lt : z - 2 / (l : ℝ) - a.val / (d : ℝ) < (n : ℝ) + 1 := by
    rw [hn]
    exact Int.lt_floor_add_one _
  have hy_ge : y ≥ z - 2 / (l : ℝ) := by linarith [abs_le.mp hyz]
  have hy_le : y ≤ z + 2 / (l : ℝ) := by linarith [abs_le.mp hyz]
  have h_l_bound : 2 / (l : ℝ) ≤ 2 / 5 := by
    have hl_real : (l : ℝ) ≥ 5 := by exact_mod_cast hl
    have : (5 : ℝ) > 0 := by positivity
    exact div_le_div_of_nonneg_left (by positivity) this hl_real
  have hu_ge : u ≥ (n : ℝ) := by
    dsimp [u]
    linarith
  have hu_lt : u < (n : ℝ) + 2 := by
    dsimp [u]
    linarith
  have h_cases : (n : ℝ) ≤ u ∧ u < (n : ℝ) + 1 ∨ ((n : ℝ) + 1) ≤ u ∧ u < (n : ℝ) + 2 := by
    rcases lt_or_ge u (n + 1) with h | h
    · left; exact ⟨hu_ge, h⟩
    · right; exact ⟨h, hu_lt⟩
  rcases h_cases with h | h
  · left
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  · right
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith

/-- Helper lemma: Z_y coordinate floor is n if not crossing. -/
lemma Z_y_eq_n_of_not_crossing (y z : ℝ) (l d : ℕ) (_hl : 3 ≤ l) (_hd : 0 < d) (a : Fin d) (n : ℤ)
    (hyz : |y - z| ≤ 2 / (l : ℝ)) (hn : n = ⌊z - 2 / (l : ℝ) - a.val / (d : ℝ)⌋)
    (h_not_cross : z + 2 / (l : ℝ) - a.val / (d : ℝ) < (n : ℝ) + 1) :
    ⌊y - a.val / (d : ℝ)⌋ = n := by
  let u := y - (a.val : ℝ) / (d : ℝ)
  have hy_ge : y ≥ z - 2 / (l : ℝ) := by linarith [abs_le.mp hyz]
  have hy_le : y ≤ z + 2 / (l : ℝ) := by linarith [abs_le.mp hyz]
  have h_floor_L : z - 2 / (l : ℝ) - a.val / (d : ℝ) ≥ (n : ℝ) := by
    rw [hn]
    exact Int.floor_le _
  have hu_ge : u ≥ (n : ℝ) := by
    dsimp [u]
    linarith
  have hu_lt : u < (n : ℝ) + 1 := by
    dsimp [u]
    linarith
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

/-- Helper lemma: cardinality of subsets of size ≤ M. -/
lemma subsets_M_card_le (d M : ℕ) :
    (Finset.filter (fun S : Finset (Fin d) => S.card ≤ M)
      Finset.univ.powerset).card ≤
      ∑ j ∈ Finset.range (M + 1), Nat.choose d j := by
  let f_part (j : ℕ) : Finset (Finset (Fin d)) := Finset.powersetCard j Finset.univ
  let S_union : Finset (Finset (Fin d)) := Finset.biUnion (Finset.range (M + 1)) f_part
  have h_subset : Finset.filter (fun S : Finset (Fin d) => S.card ≤ M)
      Finset.univ.powerset ⊆ S_union := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    rw [Finset.mem_biUnion]
    use S.card
    constructor
    · rw [Finset.mem_range]
      omega
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ S, rfl⟩
  have h_card_le : (Finset.filter (fun S : Finset (Fin d) => S.card ≤ M)
      Finset.univ.powerset).card ≤ S_union.card := Finset.card_le_card h_subset
  have h_biUnion_le := Finset.card_biUnion_le (s := Finset.range (M + 1)) (t := f_part)
  have h_sum_eq : ∑ j ∈ Finset.range (M + 1), (f_part j).card =
      ∑ j ∈ Finset.range (M + 1), Nat.choose d j := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f_part]
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [h_sum_eq] at h_biUnion_le
  exact Nat.le_trans h_card_le h_biUnion_le

/-- Helper lemma: for a fixed choice of the shift selector `a`,
the number of possible floor vectors `Z` is bounded for `l ≥ 3`. -/
lemma exact_counting_fixed_a (d : ℕ) (hd : 0 < d) (a : Fin d) (z : ℝ^[d]) (l : ℕ)
    (hl : 5 ≤ l) (hld : l ≤ d) :
    ∃ s : Finset (Fin d → ℤ),
      (∀ y : ℝ^[d], (∀ i : Fin d, |y i - z i| ≤ 2 / (l : ℝ)) →
        A d hd y = a →
        (fun i => ⌊y i - a.val / (d : ℝ)⌋) ∈ s) ∧
      s.card ≤ ∑ j ∈ Finset.range (cdiv (4 * d) l + 1), Nat.choose d j := by
  classical
  let M := cdiv (4 * d) l
  let L (i : Fin d) : ℝ := z i - 2 / (l : ℝ) - a.val / (d : ℝ)
  let U (i : Fin d) : ℝ := z i + 2 / (l : ℝ) - a.val / (d : ℝ)
  let n (i : Fin d) : ℤ := ⌊L i⌋
  let crossing (i : Fin d) : Prop := U i ≥ (n i : ℝ) + 1
  have _inst_crossing : DecidablePred crossing := fun i => by dsimp [crossing]; infer_instance
  let reconstruct (S : Finset (Fin d)) (i : Fin d) : ℤ :=
    if crossing i then (if i ∈ S then n i else n i + 1) else n i
  let subsets_M : Finset (Finset (Fin d)) :=
    Finset.filter (fun S => S.card ≤ M) Finset.univ.powerset
  let s : Finset (Fin d → ℤ) := Finset.image reconstruct subsets_M
  use s
  constructor
  · intro y hy hy_a
    let S_y : Finset (Fin d) :=
      Finset.filter (fun i => crossing i ∧ ⌊y i - a.val / (d : ℝ)⌋ = n i) Finset.univ
    have h_S_card : S_y.card ≤ M := by
      have hd_ge : 5 ≤ d := by omega
      have h_M_le : M ≤ d := by
        dsimp [M, cdiv]
        have hl_ge : 4 * d + l - 1 ≤ l * d := by
          have : 4 ≤ l := by omega
          have : 4 * d ≤ l * d := Nat.mul_le_mul_right d (by omega)
          have h_mul : (l - 4) * 5 ≤ (l - 4) * d := Nat.mul_le_mul_left (l - 4) hd_ge
          have h_dist : (l - 4) * d = l * d - 4 * d := Nat.sub_mul l 4 d
          omega
        apply Nat.div_le_of_le_mul
        exact hl_ge
      have h_subset : S_y ⊆ Finset.filter (fun i =>
          1 - (M : ℝ) / (d : ℝ) ≤ Int.fract (y i - a.val / (d : ℝ))) Finset.univ := by
        intro i hi
        rw [Finset.mem_filter] at hi
        have h_cross := hi.2.1
        have h_floor := hi.2.2
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ i, ?_⟩
        have hy_dist := hy i
        exact crossing_coord_bound (y i) l d (by omega) hd a (z i) (n i) hy_dist rfl h_cross h_floor
      have h_card_le := Finset.card_le_card h_subset
      have h_rs2 := f_round_rs2 d hd y M h_M_le
      rw [← hy_a] at h_card_le
      exact Nat.le_trans h_card_le h_rs2
    have h_S_mem : S_y ∈ subsets_M := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ S_y, h_S_card⟩
    rw [Finset.mem_image]
    use S_y
    constructor
    · exact h_S_mem
    · ext i
      dsimp [reconstruct, S_y] at *
      split_ifs with h_cross h_in
      · rw [Finset.mem_filter] at h_in
        exact h_in.2.2.symm
      · have h_in_set := Z_y_in_set (y i) (z i) l d hl hd a (n i) (hy i) rfl
        have h_neq : ⌊y i - a.val / (d : ℝ)⌋ ≠ n i := by
          intro h_eq
          have h_mem : i ∈ Finset.filter (fun i =>
            crossing i ∧ ⌊y i - a.val / (d : ℝ)⌋ = n i) Finset.univ := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ i, h_cross, h_eq⟩
          exact h_in h_mem
        rcases h_in_set with h_eq | h_eq
        · contradiction
        · exact h_eq.symm
      · have h_nc : z i + 2 / (l : ℝ) - a.val / (d : ℝ) < (n i : ℝ) + 1 := by
          dsimp [crossing] at h_cross
          linarith
        exact (Z_y_eq_n_of_not_crossing (y i) (z i) l d (by omega) hd a (n i) (hy i) rfl h_nc).symm
  · exact Nat.le_trans Finset.card_image_le (subsets_M_card_le d M)

/-- Exact counting bound for scales `l ≥ 5`. -/
lemma exact_counting (d : ℕ) (hd : 0 < d) (l : ℕ) (hl : 5 ≤ l) (hld : l ≤ d) (z : ℝ^[d]) :
    ∃ s : Finset (ℝ^[d]),
      (∀ y : ℝ^[d], (∀ i : Fin d, |y i - z i| ≤ 2 / (l : ℝ)) → f_round d hd y ∈ s) ∧
      s.card ≤ d * ∑ j ∈ Finset.range (cdiv (4 * d) l + 1), Nat.choose d j := by
  classical
  have h_fixed : ∀ a : Fin d, ∃ s : Finset (Fin d → ℤ),
      (∀ y : ℝ^[d], (∀ i : Fin d, |y i - z i| ≤ 2 / (l : ℝ)) →
        A d hd y = a →
        (fun i => ⌊y i - a.val / (d : ℝ)⌋) ∈ s) ∧
      s.card ≤ ∑ j ∈ Finset.range (cdiv (4 * d) l + 1), Nat.choose d j :=
    fun a => exact_counting_fixed_a d hd a z l hl hld
  choose s_fixed hs_fixed using h_fixed
  let f_shift (a : Fin d) (Z : Fin d → ℤ) (i : Fin d) : ℝ :=
    (Z i : ℝ) + (a.val : ℝ) / (d : ℝ)
  let s : Finset (ℝ^[d]) :=
    Finset.biUnion Finset.univ (fun a => Finset.image (f_shift a) (s_fixed a))
  use s
  constructor
  · intro y hy
    let a := A d hd y
    have h_in := (hs_fixed a).1 y hy rfl
    rw [Finset.mem_biUnion]
    use a
    constructor
    · exact Finset.mem_univ a
    · rw [Finset.mem_image]
      use Z d hd y
      constructor
      · exact h_in
      · ext i
        dsimp [f_round, f_shift, Z]
  · have h_card_le := Finset.card_biUnion_le (s := Finset.univ (α := Fin d))
      (t := fun a => Finset.image (f_shift a) (s_fixed a))
    have h_sum_le : ∑ a : Fin d, (Finset.image (f_shift a) (s_fixed a)).card ≤
        d * ∑ j ∈ Finset.range (cdiv (4 * d) l + 1), Nat.choose d j := by
      have h_sum_le_const : ∑ a : Fin d, (Finset.image (f_shift a) (s_fixed a)).card ≤
          ∑ a : Fin d, ∑ j ∈ Finset.range (cdiv (4 * d) l + 1), Nat.choose d j := by
        apply Finset.sum_le_sum
        intro a _
        have h_img := Finset.card_image_le (f := f_shift a) (s := s_fixed a)
        have h_card := (hs_fixed a).2
        omega
      have h_sum_const : ∑ a : Fin d, ∑ j ∈ Finset.range (cdiv (4 * d) l + 1),
          Nat.choose d j = d * ∑ j ∈ Finset.range (cdiv (4 * d) l + 1), Nat.choose d j := by simp
      exact Nat.le_trans h_sum_le_const h_sum_const.le
    exact Nat.le_trans h_card_le h_sum_le

/-- Helper lemma: for any coordinate, the floor is bounded in a set of size ≤ 5. -/
lemma Z_coordinate_bound (w : ℝ) (l : ℕ) (hl : 1 ≤ l) :
    ∃ s : Finset ℤ,
      (∀ x : ℝ, |x - w| ≤ 2 / (l : ℝ) → ⌊x⌋ ∈ s) ∧
      s.card ≤ 5 := by
  let s : Finset ℤ := {⌊w⌋ - 2, ⌊w⌋ - 1, ⌊w⌋, ⌊w⌋ + 1, ⌊w⌋ + 2}
  use s
  constructor
  · intro x hx
    have h_le_2 : 2 / (l : ℝ) ≤ 2 := by
      have : 1 ≤ (l : ℝ) := by exact_mod_cast hl
      have : 0 < (l : ℝ) := by positivity
      rw [div_le_iff₀ this]
      linarith
    rw [abs_le] at hx
    have h_x_ge : x ≥ w - (2 : ℤ) := by push_cast; linarith
    have h_x_le : x ≤ w + (2 : ℤ) := by push_cast; linarith
    have h_floor_ge : ⌊x⌋ ≥ ⌊w - (2 : ℤ)⌋ := Int.floor_mono h_x_ge
    have h_floor_le : ⌊x⌋ ≤ ⌊w + (2 : ℤ)⌋ := Int.floor_mono h_x_le
    have h_floor_sub : ⌊w - (2 : ℤ)⌋ = ⌊w⌋ - 2 := by
      exact Int.floor_sub_intCast w 2
    have h_floor_add : ⌊w + (2 : ℤ)⌋ = ⌊w⌋ + 2 := by
      exact Int.floor_add_intCast w 2
    rw [h_floor_sub] at h_floor_ge
    rw [h_floor_add] at h_floor_le
    simp [s]
    omega
  · dsimp [s]
    have h1 : ({⌊w⌋ - 2, ⌊w⌋ - 1, ⌊w⌋, ⌊w⌋ + 1, ⌊w⌋ + 2} : Finset ℤ).card ≤ 5 := by
      apply (Finset.card_insert_le _ _).trans
      apply Nat.succ_le_succ
      apply (Finset.card_insert_le _ _).trans
      apply Nat.succ_le_succ
      apply (Finset.card_insert_le _ _).trans
      apply Nat.succ_le_succ
      apply (Finset.card_insert_le _ _).trans
      apply Nat.succ_le_succ
      simp
    omega

/-- Helper lemma: for a fixed choice of the shift selector `a`,
the number of possible floor vectors `Z` is at most `5^d`. -/
lemma coarse_counting_fixed_a (d : ℕ) (_hd : 0 < d) (a : Fin d) (z : ℝ^[d]) (l : ℕ)
    (hl1 : 1 ≤ l) (_hl2 : l ≤ 4) :
    ∃ s : Finset (Fin d → ℤ),
      (∀ y : ℝ^[d], (∀ i : Fin d, |y i - z i| ≤ 2 / (l : ℝ)) →
        (fun i => ⌊y i - a.val / (d : ℝ)⌋) ∈ s) ∧
      s.card ≤ 5 ^ d := by
  classical
  have h_coord : ∀ i : Fin d, ∃ s : Finset ℤ,
      (∀ x : ℝ, |x - (z i - a.val / d)| ≤ 2 / (l : ℝ) → ⌊x⌋ ∈ s) ∧
      s.card ≤ 5 := fun i => Z_coordinate_bound (z i - a.val / d) l hl1
  choose s_coord hs_coord using h_coord
  let s : Finset (Fin d → ℤ) := Fintype.piFinset s_coord
  use s
  constructor
  · intro y hy
    rw [Fintype.mem_piFinset]
    intro i
    apply (hs_coord i).1 (y i - a.val / d)
    have h_eq : (y i - a.val / d) - (z i - a.val / d) = y i - z i := by ring
    rw [h_eq]
    exact hy i
  · rw [Fintype.card_piFinset]
    have h_prod : ∏ i : Fin d, (s_coord i).card ≤ ∏ i : Fin d, 5 :=
      Finset.prod_le_prod' (fun i _ => (hs_coord i).2)
    have h_prod_const : ∏ i : Fin d, 5 = 5 ^ d := by
      simp
    exact Nat.le_trans h_prod (by rw [h_prod_const])

/-- Coarse counting bound for scales `l ≤ 4`. -/
lemma coarse_counting (d : ℕ) (hd : 0 < d) (l : ℕ) (hl1 : 1 ≤ l) (hl2 : l ≤ 4) (z : ℝ^[d]) :
    ∃ s : Finset (ℝ^[d]),
      (∀ y : ℝ^[d], (∀ i : Fin d, |y i - z i| ≤ 2 / (l : ℝ)) → f_round d hd y ∈ s) ∧
      s.card ≤ d * 5 ^ d := by
  classical
  have h_fixed : ∀ a : Fin d, ∃ s : Finset (Fin d → ℤ),
      (∀ y : ℝ^[d], (∀ i : Fin d, |y i - z i| ≤ 2 / (l : ℝ)) →
        (fun i => ⌊y i - a.val / (d : ℝ)⌋) ∈ s) ∧
      s.card ≤ 5 ^ d := fun a => coarse_counting_fixed_a d hd a z l hl1 hl2
  choose s_fixed hs_fixed using h_fixed
  let f_shift (a : Fin d) (Z : Fin d → ℤ) (i : Fin d) : ℝ :=
    (Z i : ℝ) + (a.val : ℝ) / (d : ℝ)
  let s : Finset (ℝ^[d]) :=
    Finset.biUnion Finset.univ (fun a => Finset.image (f_shift a) (s_fixed a))
  use s
  constructor
  · intro y hy
    let a := A d hd y
    have h_in := (hs_fixed a).1 y hy
    rw [Finset.mem_biUnion]
    use a
    constructor
    · exact Finset.mem_univ a
    · rw [Finset.mem_image]
      use Z d hd y
      constructor
      · exact h_in
      · ext i
        dsimp [f_round, f_shift, Z]
  · have h_card_le := Finset.card_biUnion_le (s := Finset.univ (α := Fin d))
      (t := fun a => Finset.image (f_shift a) (s_fixed a))
    have h_sum_le : ∑ a : Fin d, (Finset.image (f_shift a) (s_fixed a)).card ≤ d * 5 ^ d := by
      have h_sum_le_const : ∑ a : Fin d, (Finset.image (f_shift a) (s_fixed a)).card ≤
          ∑ a : Fin d, 5 ^ d := by
        apply Finset.sum_le_sum
        intro a _
        have h_img := Finset.card_image_le (f := f_shift a) (s := s_fixed a)
        have h_card := (hs_fixed a).2
        omega
      have h_sum_const : ∑ a : Fin d, 5 ^ d = d * 5 ^ d := by simp
      exact Nat.le_trans h_sum_le_const h_sum_const.le
    exact Nat.le_trans h_card_le h_sum_le

/-- Lemma 5.2 from the blueprint: q * l ≤ (l + 1) ^ q for l ≥ 1 and q ≥ 1. -/
lemma lemma_5_2 (q l : ℕ) (hl : 1 ≤ l) (hq : 1 ≤ q) :
    q * l ≤ (l + 1) ^ q := by
  induction q, hq using Nat.le_induction with
  | base =>
    simp
  | succ q hq' ih =>
    have h1 : (q + 1) * l = q * l + l := by ring
    have h2 : (l + 1) ^ (q + 1) = (l + 1) ^ q * (l + 1) := by ring
    have h3 : (l + 1) ^ q * (l + 1) = (l + 1) ^ q * l + (l + 1) ^ q := by ring
    rw [h1, h2, h3]
    have h_pow_pos : 0 < (l + 1) ^ q := by positivity
    have h_le : (l + 1) ^ q ≤ (l + 1) ^ q * l := by
      have h_mul := Nat.mul_le_mul_left ((l + 1) ^ q) hl
      rwa [mul_one] at h_mul
    have h_term1 : q * l ≤ (l + 1) ^ q * l := Nat.le_trans ih h_le
    have h_term2 : l ≤ (l + 1) ^ q := by
      have h_base : l ≤ l + 1 := by omega
      have hq_ne : q ≠ 0 := by omega
      have h_exp : l + 1 ≤ (l + 1) ^ q := Nat.le_self_pow hq_ne (l + 1)
      exact Nat.le_trans h_base h_exp
    omega

/-- A helper lemma showing that d ≤ l * cdiv d l. -/
lemma d_le_l_mul_cdiv (d l : ℕ) (hl : 1 ≤ l) :
    d ≤ l * cdiv d l := by
  by_cases hd : d = 0
  · subst hd; simp
  · have h_div : 0 < l := hl
    have h_lt : d - 1 < l * cdiv d l := by
      dsimp [cdiv]
      rw [mul_comm]
      rw [← Nat.div_lt_iff_lt_mul h_div]
      have h_add : d + l - 1 = (d - 1) + l := by omega
      rw [h_add, Nat.add_div_right _ h_div]
      exact Nat.lt_succ_self _
    omega

/-- Lemma 5.2 (d version) from the blueprint: d ≤ (l + 1) ^ (cdiv d l) for l ≥ 1. -/
lemma lemma_5_2_d (d l : ℕ) (hl : 1 ≤ l) :
    d ≤ (l + 1) ^ (cdiv d l) := by
  by_cases hd : d = 0
  · subst hd
    positivity
  · have hq : 1 ≤ cdiv d l := by
      dsimp [cdiv]
      have h_div : 0 < l := hl
      rw [Nat.one_le_div_iff h_div]
      omega
    have h_ineq := lemma_5_2 (cdiv d l) l hl hq
    have h_d := d_le_l_mul_cdiv d l hl
    rw [mul_comm] at h_ineq
    exact Nat.le_trans h_d h_ineq

/-- Helper lemma: 2q + 1 ≤ 3^q for q ≥ 1. -/
lemma lemma_2q_add_one_le_pow (q : ℕ) (hq : 1 ≤ q) : 2 * q + 1 ≤ 3 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ q hq' ih =>
    have h1 : 2 * (q + 1) + 1 = 2 * q + 1 + 2 := by ring
    have h2 : 3 ^ (q + 1) = 3 * 3 ^ q := by ring
    have h3 : 3 * 3 ^ q = 3 ^ q + 2 * 3 ^ q := by ring
    rw [h1, h2, h3]
    have h4 : 2 ≤ 2 * 3 ^ q := by
      have : 1 ≤ 3 ^ q := by omega
      omega
    omega

/-- Helper lemma: 4q + 1 ≤ 5^q for q ≥ 1. -/
lemma lemma_4q_add_one_le_pow (q : ℕ) (hq : 1 ≤ q) : 4 * q + 1 ≤ 5 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ q hq' ih =>
    have h1 : 4 * (q + 1) + 1 = 4 * q + 1 + 4 := by ring
    have h2 : 5 ^ (q + 1) = 5 * 5 ^ q := by ring
    have h3 : 5 * 5 ^ q = 5 ^ q + 4 * 5 ^ q := by ring
    rw [h1, h2, h3]
    have h4 : 4 ≤ 4 * 5 ^ q := by
      have : 1 ≤ 5 ^ q := by omega
      omega
    omega

lemma choose_mul_le_choose_mul (q l : ℕ) (j : ℕ) :
    Nat.choose (q * l) j ≤ Nat.choose (q + j) j * l ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h_pos : 0 < j + 1 := by omega
    have h_le : Nat.choose (q * l) (j + 1) * (j + 1) ≤
        (Nat.choose (q + j + 1) (j + 1) * l ^ (j + 1)) * (j + 1) := by
      rw [Nat.choose_succ_right_eq]
      have h_succ : (q + j + 1) * Nat.choose (q + j) j =
          Nat.choose (q + j + 1) (j + 1) * (j + 1) := by
        exact Nat.add_one_mul_choose_eq (q + j) j
      have h_rhs_eq : (Nat.choose (q + j + 1) (j + 1) * l ^ (j + 1)) * (j + 1) =
          (Nat.choose (q + j) j * l ^ j) * ((q + j + 1) * l) := by
        rw [mul_assoc (Nat.choose (q + j + 1) (j + 1)), mul_comm (l ^ (j + 1)), ← mul_assoc]
        rw [← h_succ]
        rw [pow_succ]
        ring
      rw [h_rhs_eq]
      have h_factor : q * l - j ≤ (q + j + 1) * l := by
        have h1 : q * l - j ≤ q * l := Nat.sub_le (q * l) j
        have h2 : q * l ≤ (q + j + 1) * l := by
          have : q ≤ q + j + 1 := by omega
          exact Nat.mul_le_mul_right l this
        omega
      exact Nat.mul_le_mul ih h_factor
    rwa [mul_le_mul_iff_left₀ h_pos] at h_le

/-- Helper lemma: single choose term is bounded by block count formula. -/
lemma choose_le_block_count (d l q j : ℕ) (_hl : 5 ≤ l) (hdq : d ≤ q * l) (hj : j ≤ 4 * q) :
    Nat.choose d j ≤ 32 ^ q * l ^ j := by
  have h_choose_le : Nat.choose d j ≤ Nat.choose (q * l) j :=
    Nat.choose_le_choose j hdq
  have h_block := choose_mul_le_choose_mul q l j
  have h_coeff : Nat.choose (q + j) j ≤ 32 ^ q := by
    have h_choose_le_pow : Nat.choose (q + j) j ≤ 2 ^ (q + j) := Nat.choose_le_two_pow (q + j) j
    have h_exp : q + j ≤ 5 * q := by omega
    have h_pow_mono : 2 ^ (q + j) ≤ 2 ^ (5 * q) := Nat.pow_le_pow_right (by omega) h_exp
    have h_pow_32 : 2 ^ (5 * q) = 32 ^ q := by
      rw [pow_mul]
      rfl
    rw [← h_pow_32]
    exact Nat.le_trans h_choose_le_pow h_pow_mono
  have h_mul := Nat.mul_le_mul_right (l ^ j) h_coeff
  exact Nat.le_trans h_choose_le (Nat.le_trans h_block h_mul)

/-- Helper lemma: choose sum bounded by block count formula. -/
lemma lemma_5_1_helper (d l q : ℕ) (hl : 5 ≤ l) (hdq : d ≤ q * l) :
    ∑ j ∈ Finset.range (4 * q + 1), Nat.choose d j ≤ (4 * q + 1) * 32 ^ q * l ^ (4 * q) := by
  have h_terms : ∀ j ∈ Finset.range (4 * q + 1), Nat.choose d j ≤ 32 ^ q * l ^ (4 * q) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj_le : j ≤ 4 * q := by omega
    have h_choose := choose_le_block_count d l q j hl hdq hj_le
    have h_l_mono : l ^ j ≤ l ^ (4 * q) := Nat.pow_le_pow_right (by omega) hj_le
    have h_mul := Nat.mul_le_mul_left (32 ^ q) h_l_mono
    exact Nat.le_trans h_choose h_mul
  have h_sum := Finset.sum_le_card_nsmul (s := Finset.range (4 * q + 1))
    (f := fun j => Nat.choose d j) (32 ^ q * l ^ (4 * q)) h_terms
  simp only [Finset.card_range, nsmul_eq_mul] at h_sum
  push_cast at h_sum
  rw [← mul_assoc] at h_sum
  exact h_sum

/-- Lemma 5.1 from the blueprint: sum of choose is bounded by (l+1)^(7 * cdiv d l). -/
lemma lemma_5_1 (d l : ℕ) (hl : 5 ≤ l) (hld : l ≤ d) :
    ∑ j ∈ Finset.range (4 * cdiv d l + 1), Nat.choose d j ≤ (l + 1) ^ (7 * cdiv d l) := by
  let q := cdiv d l
  have hdq : d ≤ q * l := by
    rw [mul_comm]
    exact d_le_l_mul_cdiv d l (by omega)
  have h_help := lemma_5_1_helper d l q hl hdq
  have h_q_pos : 1 ≤ q := by
    dsimp [q, cdiv]
    have : 0 < l := by omega
    rw [Nat.one_le_div_iff this]
    omega
  have h1 := lemma_4q_add_one_le_pow q h_q_pos
  have h1_l : 5 ^ q ≤ (l + 1) ^ q := by
    apply Nat.pow_le_pow_left
    omega
  have h_part1 : 4 * q + 1 ≤ (l + 1) ^ q := Nat.le_trans h1 h1_l
  have h_part2 : 32 ^ q ≤ (l + 1) ^ (2 * q) := by
    have h_base : 32 ≤ (l + 1) ^ 2 := by
      have : 6 ≤ l + 1 := by omega
      have h_sq : 36 ≤ (l + 1) ^ 2 := by
        have : 6 ^ 2 ≤ (l + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        exact this
      omega
    have h_pow := Nat.pow_le_pow_left h_base q
    rw [← pow_mul] at h_pow
    exact h_pow
  have h_part3 : l ^ (4 * q) ≤ (l + 1) ^ (4 * q) := by
    apply Nat.pow_le_pow_left
    omega
  have h_mul1 := Nat.mul_le_mul h_part1 h_part2
  have h_mul2 := Nat.mul_le_mul h_mul1 h_part3
  have h_eq : (l + 1) ^ q * (l + 1) ^ (2 * q) * (l + 1) ^ (4 * q) = (l + 1) ^ (7 * q) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  rw [h_eq] at h_mul2
  exact Nat.le_trans h_help h_mul2

/-- Helper lemma for arithmetic_bound when l = 1. -/
lemma lemma_l1 (d : ℕ) : d * 5 ^ d ≤ 256 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : (d + 1) * 5 ^ (d + 1) = 5 * (d * 5 ^ d) + 5 * 5 ^ d := by ring
    have h2 : 256 ^ (d + 1) = 256 * 256 ^ d := by ring
    rw [h1, h2]
    have h_pow : 5 ^ d ≤ 256 ^ d := Nat.pow_le_pow_left (by omega) d
    omega

/-- The combined arithmetic bound showing that the count is bounded by the power bound. -/
lemma arithmetic_bound (d : ℕ) (l : ℕ) (hl : 1 ≤ l) (hld : l ≤ d) :
    (if 5 ≤ l then
      d * ∑ j ∈ Finset.range (4 * cdiv d l + 1), Nat.choose d j
     else
      d * 5 ^ d) ≤ (l + 1) ^ (8 * cdiv d l) := by
  split_ifs with hl3
  · have h_5_2 := lemma_5_2_d d l (by omega)
    have h_5_1 := lemma_5_1 d l hl3 hld
    have h_mul := Nat.mul_le_mul h_5_2 h_5_1
    have h_pow_add : (l + 1) ^ (cdiv d l) * (l + 1) ^ (7 * cdiv d l) =
        (l + 1) ^ (8 * cdiv d l) := by
      rw [← pow_add]
      ring_nf
    rw [h_pow_add] at h_mul
    exact h_mul
  · have hl_cases : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by omega
    rcases hl_cases with rfl | rfl | rfl | rfl
    · have hc1 : cdiv d 1 = d := by
        dsimp [cdiv]
        omega
      rw [hc1]
      have h_pow_16 : 2 ^ (8 * d) = 256 ^ d := by
        rw [pow_mul]
        rfl
      rw [h_pow_16]
      exact lemma_l1 d
    · have h_5_2 := lemma_5_2_d d 2 (by omega)
      have h_pow_25 : 5 ^ d ≤ 25 ^ (cdiv d 2) := by
        have h_le : d ≤ 2 * cdiv d 2 := d_le_l_mul_cdiv d 2 (by omega)
        have h_pow : 5 ^ d ≤ 5 ^ (2 * cdiv d 2) := Nat.pow_le_pow_right (by omega) h_le
        have h_eq : 5 ^ (2 * cdiv d 2) = 25 ^ (cdiv d 2) := by rw [pow_mul]; rfl
        rwa [h_eq] at h_pow
      have h_mul := Nat.mul_le_mul h_5_2 h_pow_25
      have h_pow_add : 3 ^ (cdiv d 2) * 25 ^ (cdiv d 2) = 75 ^ (cdiv d 2) := by
        rw [← mul_pow]
        rfl
      rw [h_pow_add] at h_mul
      have h_pow_16 : 3 ^ (8 * cdiv d 2) = 6561 ^ (cdiv d 2) := by
        rw [pow_mul]
        rfl
      rw [h_pow_16]
      have h_base_le : 75 ≤ 6561 := by omega
      have h_pow_mono := Nat.pow_le_pow_left h_base_le (cdiv d 2)
      exact Nat.le_trans h_mul h_pow_mono
    · have h_5_2 := lemma_5_2_d d 3 (by omega)
      have h_pow_125 : 5 ^ d ≤ 125 ^ (cdiv d 3) := by
        have h_le : d ≤ 3 * cdiv d 3 := d_le_l_mul_cdiv d 3 (by omega)
        have h_pow : 5 ^ d ≤ 5 ^ (3 * cdiv d 3) := Nat.pow_le_pow_right (by omega) h_le
        have h_eq : 5 ^ (3 * cdiv d 3) = 125 ^ (cdiv d 3) := by rw [pow_mul]; rfl
        rwa [h_eq] at h_pow
      have h_mul := Nat.mul_le_mul h_5_2 h_pow_125
      have h_pow_add : 4 ^ (cdiv d 3) * 125 ^ (cdiv d 3) = 500 ^ (cdiv d 3) := by
        rw [← mul_pow]
        rfl
      rw [h_pow_add] at h_mul
      have h_pow_16 : 4 ^ (8 * cdiv d 3) = 65536 ^ (cdiv d 3) := by
        rw [pow_mul]
        rfl
      rw [h_pow_16]
      have h_base_le : 500 ≤ 65536 := by omega
      have h_pow_mono := Nat.pow_le_pow_left h_base_le (cdiv d 3)
      exact Nat.le_trans h_mul h_pow_mono
    · have h_5_2 := lemma_5_2_d d 4 (by omega)
      have h_pow_625 : 5 ^ d ≤ 625 ^ (cdiv d 4) := by
        have h_le : d ≤ 4 * cdiv d 4 := d_le_l_mul_cdiv d 4 (by omega)
        have h_pow : 5 ^ d ≤ 5 ^ (4 * cdiv d 4) := Nat.pow_le_pow_right (by omega) h_le
        have h_eq : 5 ^ (4 * cdiv d 4) = 625 ^ (cdiv d 4) := by rw [pow_mul]; rfl
        rwa [h_eq] at h_pow
      have h_mul := Nat.mul_le_mul h_5_2 h_pow_625
      have h_pow_add : 5 ^ (cdiv d 4) * 625 ^ (cdiv d 4) = 3125 ^ (cdiv d 4) := by
        rw [← mul_pow]
        rfl
      rw [h_pow_add] at h_mul
      have h_pow_16 : 5 ^ (8 * cdiv d 4) = 390625 ^ (cdiv d 4) := by
        rw [pow_mul]
        rfl
      rw [h_pow_16]
      have h_base_le : 3125 ≤ 390625 := by omega
      have h_pow_mono := Nat.pow_le_pow_left h_base_le (cdiv d 4)
      exact Nat.le_trans h_mul h_pow_mono

/-- Helper lemma: cdiv (2 * d) l ≤ 2 * cdiv d l for l ≥ 3. -/
lemma cdiv_two_d_le_two_cdiv (d l : ℕ) (hl : 3 ≤ l) :
    cdiv (2 * d) l ≤ 2 * cdiv d l := by
  dsimp [cdiv]
  have h_div : 0 < l := by linarith
  rw [Nat.div_le_iff_le_mul_add_pred h_div]
  have h_mul : l * (2 * ((d + l - 1) / l)) = 2 * (l * ((d + l - 1) / l)) := by ring
  rw [h_mul]
  have h_div_mod : d + l - 1 = l * ((d + l - 1) / l) + (d + l - 1) % l := by
    exact (Nat.div_add_mod (d + l - 1) l).symm
  have h_mod_lt : (d + l - 1) % l < l := Nat.mod_lt (d + l - 1) h_div
  omega

/-- Helper lemma: cdiv (4 * d) l ≤ 4 * cdiv d l for l ≥ 5. -/
lemma cdiv_four_d_le_four_cdiv (d l : ℕ) (hl : 5 ≤ l) :
    cdiv (4 * d) l ≤ 4 * cdiv d l := by
  dsimp [cdiv]
  have h_div : 0 < l := by linarith
  rw [Nat.div_le_iff_le_mul_add_pred h_div]
  have h_mul : l * (4 * ((d + l - 1) / l)) = 4 * (l * ((d + l - 1) / l)) := by ring
  rw [h_mul]
  have h_div_mod : d + l - 1 = l * ((d + l - 1) / l) + (d + l - 1) % l := by
    exact (Nat.div_add_mod (d + l - 1) l).symm
  have h_mod_lt : (d + l - 1) % l < l := Nat.mod_lt (d + l - 1) h_div
  omega

/-- Helper lemma: monotonicity of sum of binomial coefficients. -/
lemma sum_range_mono (d : ℕ) (a b : ℕ) (hab : a ≤ b) :
    d * ∑ j ∈ Finset.range (a + 1), Nat.choose d j ≤
      d * ∑ j ∈ Finset.range (b + 1), Nat.choose d j := by
  have h_sub : Finset.range (a + 1) ⊆ Finset.range (b + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have h_sum : ∑ j ∈ Finset.range (a + 1), Nat.choose d j ≤
      ∑ j ∈ Finset.range (b + 1), Nat.choose d j :=
    Finset.sum_le_sum_of_subset h_sub
  exact Nat.mul_le_mul_left d h_sum

/-- The main theorem stating that `f_round` is a rounding scheme at all scales:
For any integer `l` with `1 ≤ l ≤ d`, if we set the scale `γ = 1 / l`
(so the ball of radius `γ` has radius `1 / l`), the number of rounded
values in the ball is at most `(l + 1) ^ (8 * cdiv d l)`. -/
theorem f_round_is_rounding_scheme (d : ℕ) (hd : 0 < d) (l : ℕ) (hl : 1 ≤ l) (hld : l ≤ d) :
  isRoundingScheme d ((l + 1) ^ (8 * cdiv d l)) (1 / (l : ℝ)) (f_round d hd) := by
  constructor
  · intro z i
    have h := f_round_rs1 d hd z i
    rw [abs_le]
    constructor
    · linarith
    · linarith
  · intro z
    have h_scale : (1 : ℝ) / (l : ℝ) ≤ 2 / (l : ℝ) := by
      have : (0 : ℝ) ≤ 1 / (l : ℝ) := by positivity
      linarith [show 2 / (l : ℝ) = 1 / (l : ℝ) + 1 / (l : ℝ) by ring]
    by_cases hl3 : 5 ≤ l
    · obtain ⟨s, hs1, hs2⟩ := exact_counting d hd l hl3 hld z
      use s
      constructor
      · intro y hy
        exact hs1 y (fun i => le_trans (hy i) h_scale)
      · have h_cdiv := cdiv_four_d_le_four_cdiv d l hl3
        have h_sum := sum_range_mono d (cdiv (4 * d) l) (4 * cdiv d l) h_cdiv
        have h_arith := arithmetic_bound d l hl hld
        split_ifs at h_arith
        exact Nat.le_trans hs2 (Nat.le_trans h_sum h_arith)
    · have hl2 : l ≤ 4 := by omega
      obtain ⟨s, hs1, hs2⟩ := coarse_counting d hd l hl hl2 z
      use s
      constructor
      · intro y hy
        exact hs1 y (fun i => le_trans (hy i) h_scale)
      · have h_arith := arithmetic_bound d l hl hld
        split_ifs at h_arith
        exact Nat.le_trans hs2 h_arith

end Rounding2
