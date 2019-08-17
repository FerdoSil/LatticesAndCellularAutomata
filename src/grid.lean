import utils
import data.vector data.list data.int.basic tactic.omega

open utils

section grids

class relative_grid (α : Type*) :=
  (carrier : Type)
  (rows    : α → ℕ)
  (cols    : α → ℕ)
  (unempty : Πg, rows g * cols g > 0)
  (data    : Πg, bounded 0 (rows g) → bounded 0 (cols g) → carrier)

class grid (α : Type*) extends relative_grid α :=
  (bl : α → point)

section grid_defs

variables {α : Type*} [grid α] (g : α)

open grid relative_grid

notation `|`:max x `|`:0 := int.nat_abs x

def size := rows g * cols g

attribute [simp]
lemma size_eq_rows_mul_cols : size g = rows g * cols g := rfl

def tr (bl : point) (r c : ℕ) : point :=
  ⟨bl.x + c, bl.y - r⟩

attribute [simp]
def grid_rows := rows g

attribute [simp]
def grid_cols := cols g

attribute [simp]
def gbl := bl g

def gtr := tr (bl g) (rows g) (cols g)

def tl : point := ⟨(bl g).x, (bl g).y - rows g⟩

def br : point := ⟨(bl g).x + cols g, (bl g).y⟩

lemma expand_gbl : gbl g = bl g := by simp

lemma expand_gtr : gtr g = ⟨(bl g).x + cols g, (bl g).y - rows g⟩ :=
  by simp [gtr, tr]

lemma blx_eq_tlx {g : α} : (bl g).x = (tl g).x := by simp [bl, tl]

lemma brx_eq_trx {g : α} : (br g).x = (gtr g).x := by simp [br, gtr, tr]

lemma bly_eq_bry {g : α} : (bl g).y = (br g).y := by simp [br]

lemma tly_eq_try {g : α} : (tl g).y = (gtr g).y := by simp [gtr, tr, tl]

private lemma linear_bounds {l r : ℤ} {c : ℕ} (h₁ : l < r) (h₂ : r - ↑c ≤ l) :
  |l + ↑c - r| < c :=
begin
  rw [← sub_nonneg, ← sub_add, sub_add_eq_add_sub] at h₂,
  rw [
    ← int.coe_nat_lt, int.nat_abs_of_nonneg h₂,
    sub_lt_iff_lt_add', add_lt_add_iff_right
  ], exact h₁
end

structure bounding_box := (p₁ : point) (p₂ : point) (h : p₁ ↗ p₂)

def bbox_str : bounding_box → string
  | ⟨p₁, p₂, _⟩ := "<(" ++ to_string p₁ ++ ", " ++ to_string p₂ ++ ")>"

instance : has_to_string bounding_box := ⟨bbox_str⟩

instance : has_repr bounding_box := ⟨bbox_str⟩

def points_of_box (bb : bounding_box) : point × point := ⟨bb.p₁, bb.p₂⟩

def rows_of_box (bb : bounding_box) : ℕ :=
  |bb.p₁.y - bb.p₂.y|
  
def cols_of_box (bb : bounding_box) : ℕ :=
  |bb.p₂.x - bb.p₁.x|

private def data_option (g : α) (x y : ℕ) :=
  if h : is_bounded 0 (cols g) y
  then if h₁ : is_bounded 0 (rows g) x
       then some $ relative_grid.data g ⟨x, h₁⟩ ⟨y, h⟩
       else none
  else none

end grid_defs

section grid_lemmas

open grid relative_grid function

variables {α : Type*} [grid α] {g : α}

private theorem data_data_option {x y : ℕ}
  (h₁ : is_bounded 0 (rows g) y) (h₂ : is_bounded 0 (cols g) x) :
  some (relative_grid.data g ⟨y, h₁⟩ ⟨x, h₂⟩) = data_option g y x :=
  by unfold data_option; repeat { rw dif_pos; try { unfold is_bounded } };
     simp [h₂.2]

lemma rows_of_box_pos {bb : bounding_box} : rows_of_box bb > 0 :=
let ⟨⟨_, y₁⟩, ⟨_, y₂⟩, h⟩ := bb in
begin
  simp only [rows_of_box, gt_from_lt], simp [grid_bounded_iff] at h,
  rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg]; omega
end

lemma cols_of_box_pos {bb : bounding_box} : cols_of_box bb > 0 :=
let ⟨⟨x₁, _⟩, ⟨x₂, _⟩, h⟩ := bb in
begin
  simp only [cols_of_box, gt_from_lt], simp [grid_bounded_iff] at h,
  rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg]; omega
end

lemma rows_pos : 0 < rows g :=
  (gt_and_gt_of_mul_gt (unempty g)).1

lemma cols_pos : 0 < cols g :=
  (gt_and_gt_of_mul_gt (unempty g)).2

lemma abs_rows_pos : 0 < |rows g| := rows_pos

lemma abs_cols_pos : 0 < |cols g| := cols_pos

lemma coe_rows_pos : (0 : ℤ) < ↑(rows g) := by simp [rows_pos]

lemma coe_cols_pos {g : α} : (0 : ℤ) < ↑(cols g) := by simp [cols_pos]

lemma idx_div_cols_bounded {n} (h : n < size g) :
  (gtr g).y + ↑n / ↑(cols g) < (bl g).y :=
begin
  simp [expand_gtr] at *,
  apply add_lt_of_lt_sub_right, simp,
  apply int.div_lt_of_lt_mul coe_cols_pos,
  rwa [← int.coe_nat_mul, int.coe_nat_lt_coe_nat_iff]
end

lemma idx_mod_cols_bounded {n} (h : n < size g) :
  (bl g).x + ↑n % ↑(cols g) < (gtr g).x :=
by simp [expand_gtr]; exact int.mod_lt_of_pos _ coe_cols_pos

lemma grid_is_bounding_box : bl g ↗ gtr g :=
let ⟨h₁, h₂⟩ := gt_and_gt_of_mul_gt (relative_grid.unempty g) in
  grid_bounded_iff.2 ⟨
    by simpa [gtr, tr],
    sub_lt_self _ $ by simpa [gt_from_lt, h₁]
  ⟩

def bbox_of_grid (g : α) : bounding_box :=
  ⟨bl g, gtr g, grid_is_bounding_box⟩

theorem bbox_of_grid_p₁ : (bbox_of_grid g).p₁ = (gbl g) := rfl

theorem bbox_of_grid_p₂ : (bbox_of_grid g).p₂ = (gtr g) := rfl

structure relative_point (g : α) :=
  (x : bounded 0 (rows g))
  (y : bounded 0 (cols g))

def relative_point_str (g : α) : relative_point g → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "]"

instance : has_to_string (relative_point g) :=
  ⟨relative_point_str g⟩ 

instance : has_repr (relative_point g) :=
  ⟨relative_point_str g⟩ 

structure grid_point (g : α) :=
  (x : bounded (gtr g).y (bl g).y)
  (y : bounded (bl g).x (gtr g).x)

def grid_point_str (g : α) : grid_point g → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "] - "
              ++ to_string (bl g)

instance : has_to_string (grid_point g) := ⟨grid_point_str g⟩

instance : has_repr (grid_point g) := ⟨grid_point_str g⟩

lemma gtry_lt_bly : (gtr g).y < (bl g).y :=
  by simp only [expand_gtr];
     exact sub_lt_iff_lt_add.2 (lt_add_of_pos_right _ coe_rows_pos)

lemma gblx_lt_gtrx : (gbl g).x < (gtr g).x :=
  by simp only [expand_gtr, expand_gbl];
     exact lt_add_of_pos_right _ coe_cols_pos

def relpoint_of_gpoint {g : α} (p : grid_point g) : relative_point g :=
    ⟨
      ⟨int.nat_abs (p.1.1 - (tl g).y),
      have h : p.1.1 - (tl g).y ≥ 0,
        {
          apply le_sub_iff_add_le.2,
          let lbx := p.1.2.1,
          simp [expand_gtr] at lbx, simpa [tl]
        },
      ⟨
        (int.le_of_coe_nat_le_coe_nat $ (int.nat_abs_of_nonneg h).symm ▸ h),
        ((int.coe_nat_lt_coe_nat_iff _ _).1 $
        (int.nat_abs_of_nonneg h).symm ▸
        begin
          simp only [tl],
          rw [← sub_add, ← zero_add (↑(rows g))],
          conv { to_lhs, simp only [zero_add] },
          simp [add_lt_add_iff_right, sub_lt, p.1.2.2]
        end)
      ⟩
      ⟩,
      ⟨int.nat_abs (p.2.1 - (tl g).x),
      have h : p.2.1 - (tl g).x ≥ 0,
        from le_sub_iff_add_le.2 (by simp [tl, p.2.2.1]),
      ⟨
        (int.le_of_coe_nat_le_coe_nat $ (int.nat_abs_of_nonneg h).symm ▸ h),
        (iff.elim_left (int.coe_nat_lt_coe_nat_iff _ _) $
        (int.nat_abs_of_nonneg h).symm ▸
        begin
          let uby := p.2.2.2,
          simp only [expand_gtr] at uby,
          simp only [tl],
          rw [sub_lt_iff_lt_add, add_comm],
          exact uby
        end
        )
      ⟩
      ⟩
    ⟩

def gpoint_of_relpoint {g : α} (p : relative_point g) : grid_point g :=
  ⟨
    ⟨(tl g).y + p.1.1,
      ⟨
        by simp [tl, expand_gtr],
        by simp [tl, expand_gtr, p.1.2.2]
      ⟩
    ⟩,
    ⟨(tl g).x + p.2.1,
      ⟨
        by simp [tl],
        by simp [tl, expand_gtr, p.2.2.2]
      ⟩
    ⟩
  ⟩

lemma relpoint_gpoint_id {g : α} {p : grid_point g} :
  gpoint_of_relpoint (relpoint_of_gpoint p) = p :=
begin
  cases p with x y,
  simp [relpoint_of_gpoint, gpoint_of_relpoint],
  split,
    {
      cases x with x hx, simp,
      rw ← sub_eq_add_neg,
      have : x - (tl g).y ≥ 0,
        {
          simp only [(≥)],
          rw [tly_eq_try, le_sub_iff_add_le, zero_add],
          exact hx.1
        },
      rw int.nat_abs_of_nonneg this,
      simp
    },
    {
      cases y with y hy, simp,
      rw ← sub_eq_add_neg,
      have : y - (tl g).x ≥ 0,
        {
          simp only [(≥)],
          rw [← blx_eq_tlx, le_sub_iff_add_le, zero_add],
          exact hy.1
        },
      rw int.nat_abs_of_nonneg this,
      simp
    }
end

lemma gpoint_relpoint_id {g : α} {p : relative_point g} :
  relpoint_of_gpoint (gpoint_of_relpoint p) = p :=
  by cases p with x y; simp [gpoint_of_relpoint, relpoint_of_gpoint]

def prod_of_rel_point {g : α} (rp : relative_point g) := (rp.x, rp.y)

def prod_of_grid_point {g : α} (ap : grid_point g) := (ap.x, ap.y)

def grid_point_of_prod {g : α}
  (p : bounded (bl g).x (gtr g).x ×
       bounded (gtr g).y (bl g).y) : grid_point g :=
  ⟨p.snd, p.fst⟩

def grid_point_of_prod' {g : α}
  (p : bounded (gtr g).y (bl g).y ×
       bounded (bl g).x (gtr g).x) : grid_point g :=
  ⟨p.fst, p.snd⟩

def abs_data (g : α) :=
  (uncurry (data g)) ∘ prod_of_rel_point ∘ relpoint_of_gpoint

private def grid_row_point_of_prod {g : α}
  (p : bounded (bl g).x (gtr g).x × 
       bounded (gtr g).y ((gtr g).y + 1)) :
       grid_point g :=
  ⟨@make_bounded _ _ (gtr g).y (bl g).y p.snd
   begin
     split,
      {
        let h := p.2.2.1,
        cases p with _ p, cases p,
        simpa [-gtr, z_of_bounded]
      },
      {
        let h := p.2.2.2,
        unfold_coes, cases p with _ p, cases p,
        simp [z_of_bounded, expand_gtr] at *,
        apply lt_of_lt_of_le h,
        rw [← sub_eq_add_neg, add_sub, add_comm, ← add_sub],
        conv_rhs { rw ← add_zero (bl g).y },
        rw [add_le_add_iff_left, sub_le, sub_zero],
        exact coe_rows_pos
      }
   end,
   p.fst⟩

lemma try_lt_bly : (gtr g).y < (gbl g).y :=
  (grid_bounded_iff.1 grid_is_bounding_box).2

private lemma grid_rows_eq_bly_sub_try :
  grid_rows g = |(bl g).y - (gtr g).y| :=
  by simp [expand_gtr]

lemma rows_eq_bly_sub_try :
  rows g = |((bl g).y - (gtr g).y)| := grid_rows_eq_bly_sub_try

private lemma grid_cols_eq_trx_sub_blx 
  : grid_cols g = |((gtr g).x - (bl g).x)| :=
  by simp [expand_gtr]

lemma cols_eq_trx_sub_blx 
  : cols g = |((gtr g).x - (bl g).x)| := grid_cols_eq_trx_sub_blx

private lemma bounded_establishes_bounds {a b : ℤ}
  (h : a < b) (x : bounded 0 ( |b - a| )) :
  a ≤ a + ↑x ∧ a + ↑x < b :=
have xpos : ↑x ≥ 0, from positive_bounded _,
have xmax : ↑x < int.nat_abs (b - a), from bounded_lt _,
  ⟨
    by apply le_add_of_nonneg_right; unfold coe,
    begin
      unfold_coes at *,
      rw add_comm,
      rw [← int.coe_nat_lt, int.nat_abs_of_nonneg, lt_sub_iff_add_lt] at xmax,
        {exact xmax},
        {
          simp [ge_from_le],
          rw [
            ← sub_eq_add_neg, ← add_le_add_iff_right a,
            zero_add, sub_add_cancel
          ],
          exact int.le_of_lt h,
        }
    end
  ⟩

end grid_lemmas

end grids

section grid_impls

structure grid₀ (α : Type) :=
  (r : ℕ)
  (c : ℕ)
  (h : r * c > 0)
  (data : vector α (r * c))

structure agrid₀ (α : Type) extends grid₀ α :=
  (o : point)

structure fgrid (α : Type) :=
  (r : ℕ)
  (c : ℕ)
  (h : r * c > 0)
  (o : point)
  (data : bounded (o.y - r) o.y → bounded o.x (o.x + c) → α)

end grid_impls

section grid_instances

lemma data_not_empty {α : Type} {g : agrid₀ α} : ¬empty_list g.data.to_list :=
assume contra,
begin
  simp [empty_list] at contra,
  have contra₁ := contra.symm,
  rw [list_empty_iff_len, vector.to_list_length] at contra₁,
  cases g with g _, cases g with _ _ h _,
  rw contra₁ at h,
  exact absurd h (gt_irrefl _)
end

lemma linearize_array {x y r c : ℕ}
  (xb : is_bounded 0 c x) (yb : is_bounded 0 r y) : y * c + x < r * c :=
let ⟨xl, xu⟩ := xb in
let ⟨yl, yu⟩ := yb in
have rows_pos : 0 < r, from lt_of_le_of_lt yl yu,
have cols_pos : 0 < c, from lt_of_le_of_lt xl xu,
have h₁ : y * c < r * c,
  from mul_lt_mul yu (le_refl _) cols_pos (le_of_lt rows_pos),
have h₂ : ∃n, nat.succ y + n = r, from nat_le_dest yu,
let ⟨n, h₂⟩ := h₂ in
by rw [← h₂, right_distrib, nat.succ_mul, add_assoc];
   exact add_lt_add_of_le_of_lt (le_refl _)
         (@nat.lt_add_right _ _ _ xu)

instance rg_grid₀ {α : Type} :
  relative_grid (grid₀ α) := {
    carrier := α,
    rows    := λg, g.r,
    cols    := λg, g.c,
    unempty := λg, g.h,
    data    :=
    λg y x,
      g.data.nth ⟨
        y.1 * g.c + x.1,
        linearize_array (is_bounded_of_bounds x.2.1 x.2.2)
                        (is_bounded_of_bounds y.2.1 y.2.2)
      ⟩    
}

instance rg_agrid₀ {α : Type} :
  relative_grid (agrid₀ α) := {
    carrier := α,
    rows    := λg, g.r,
    cols    := λg, g.c,
    unempty := λg, g.h,
    data    :=
    λg y x,
      g.data.nth ⟨
        y.1 * g.c + x.1,
        linearize_array (is_bounded_of_bounds x.2.1 x.2.2)
                        (is_bounded_of_bounds y.2.1 y.2.2)
      ⟩   
}

private lemma absolute_bounds {o : ℤ} {r : ℕ}
                              (x : bounded 0 r) : o - ↑r + ↑x < o :=
  by cases x with _ h; simp; exact h.2

instance rg_fgrid {α : Type} :
  relative_grid (fgrid α) := {
    carrier := α,
    rows    := λg, g.r,
    cols    := λg, g.c,
    unempty := λg, g.h,
    data    := λg x y,
    g.data ⟨g.o.y - ↑g.r + x,
            ⟨le_add_of_nonneg_right $ by cases x; unfold_coes,
             absolute_bounds x⟩⟩
           ⟨g.o.x + y,
            ⟨le_add_of_nonneg_right $ by cases x; unfold_coes,
             add_lt_add_left (
               let ⟨_, ⟨_, h⟩⟩ := y in
               iff.elim_right int.coe_nat_lt h
            ) g.o.x⟩⟩
}

instance ag_agrid₀ {α : Type} :
  grid (agrid₀ α) := {
    bl := λg, g.o
  }

instance ag_f {α : Type} :
  grid (fgrid α) := {
    bl := λg, g.o
  }

def point_of_grid_point {α : Type*} [grid α] {g : α} : grid_point g → point
  | ⟨b₁, b₂⟩ := ⟨b₂, b₁⟩

instance point_grid_point_coe {α : Type*} [grid α] (g : α) :
  has_coe (grid_point g) point := ⟨point_of_grid_point⟩

end grid_instances

section finite_grid

open list int function

variables {α : Type*} [grid α] (g : α)

def grp (a b row : ℤ) : list point :=
  map (uncurry point.mk) $ zip (range_pure a b)
                                        (repeat row ( |b - a| ))

private lemma expand_grp {a b r} (h : a < b) :
  grp a b r =
  ⟨a, r⟩ :: grp (a + 1) b r :=
begin
  conv_lhs { simp only [grp] },
  rw range_pure_next h,
  have : |b - a| ≥ 1, from nat_abs_ge_one_of_lt h,
  rw repeat_more this, simp [-sub_eq_add_neg],
  exact ⟨
    by simp [uncurry],
    by simp [grp, -sub_eq_add_neg, abs_minus_plus h]
  ⟩
end

private lemma expand_grp_g {g : α} :
  grp (gbl g).x (gtr g).x (gtr g).y = 
  ⟨(gbl g).x, (gtr g).y⟩ ::
  grp ((gbl g).x + 1) (gtr g).x (gtr g).y :=
begin
  simp only [grp],
  have h : range_pure ((gbl g).x) ((gtr g).x) =
           (gbl g).x ::
           range_pure (((gbl g).x) + 1) ((gtr g).x),
    from range_pure_next (grid_bounded_iff.1 grid_is_bounding_box).1,
  rw h,
  have h₁ : repeat ((gtr g).y)
                   ( |(gtr g).x - (gbl g).x| ) = 
            (gtr g).y ::
            repeat (gtr g).y ( |(gtr g).x - (gbl g).x| - 1),
    {
      simp only [expand_gbl], apply repeat_more, 
      rw ← cols_eq_trx_sub_blx,
      exact abs_cols_pos
    },
  simp only [map, h₁, zip_cons_cons],
  exact ⟨
    by simp [uncurry],
    by rw abs_minus_plus;
       exact (grid_bounded_iff.1 grid_is_bounding_box).1
  ⟩
end

private lemma grp_empty_iff {a b r} :
  empty_list (grp a b r) ↔ b ≤ a :=
  ⟨
    assume h, begin
      by_cases contra : a < b,
        {rw expand_grp at h, cases h, exact contra},
        {exact le_of_not_lt contra}
    end,
    assume h, begin
      unfold grp,
      have : range_pure a b = [],
        by unfold1 range_pure; exact if_neg (not_lt_of_le h),
      simp [zip_nil_left, empty_list, this]
    end
  ⟩

open function

private lemma grp_bounds {a b row : ℤ} :
  ∀{c : point}, c ∈ grp a b row →
    is_bounded a b c.x ∧ is_bounded row (row + 1) c.y :=
assume c h,
begin
  simp [grp] at h,
  cases h with a₁ h₁,
  cases h₁ with b₁ h₂,
  cases h₂ with h₂ h₃,
  have h₄ : a₁ ∈ range_pure a b, from pair_in_zip_l h₂,
  have h₅ : b₁ ∈ repeat row ( |b + -a| ), from pair_in_zip_r h₂,
  rw ← h₃,
  split; split,
    {exact (range_pure_bounded h₄).1},
    {exact (range_pure_bounded h₄).2},
    {simp [repeat_bounded h₅, uncurry]},
    {rw (repeat_bounded h₅), exact lt_add_succ _ _}
end

lemma length_grp {a b : ℤ} (h : a < b) {x : ℤ} :
  length (grp a b x) = |b - a| :=
have h₁ : length (range_pure a b) = |b - a|,
  from range_length_pure (int.le_of_lt h),
  by simp [grp, length_map, length_zip_left, length_repeat, h₁]

def gip (p₁ p₂ : point) : list point :=
  join (map (grp p₁.x p₂.x) (range_pure p₂.y p₁.y))

open relative_grid grid

def gip_g := gip (bl g) (gtr g)

private lemma expand_gip {p₁ p₂} (h : p₁ ↗ p₂) : 
  gip p₁ p₂ = ⟨p₁.x, p₂.y⟩ :: grp (p₁.x + 1) p₂.x p₂.y
           ++ gip p₁ ⟨p₂.x, p₂.y + 1⟩ :=
  by simp [
       gip, expand_grp (grid_bounded_iff.1 h).1,
       range_pure_next (grid_bounded_iff.1 h).2
     ]

private lemma expand_row_gip {p₁ p₂} (h : p₁ ↗ p₂) : 
  gip p₁ p₂ = 
  grp p₁.x p₂.x p₂.y ++ gip p₁ ⟨p₂.x, p₂.y + 1⟩ :=
  by simp [gip, range_pure_next (grid_bounded_iff.1 h).2]

private lemma expand_gip_g :
  (gip_g g) = grp (gbl g).x (gtr g).x (gtr g).y
              ++ gip ⟨(gbl g).x, (gbl g).y⟩ ⟨(gtr g).x, ((gtr g).y + 1)⟩ :=
begin
  generalize h : gip ⟨(gbl g).x, (gbl g).y⟩ ⟨(gtr g).x, ((gtr g).y + 1)⟩ = t,
  simp only [gip_g, gip],
  rw range_pure_next, dsimp,
    {apply congr_arg, simp [h.symm, gip]},
    {exact try_lt_bly}
end

def is_in_grid' (xy : point) :=
  is_bounded (gtr g).y (gbl g).y xy.y ∧
  is_bounded (gbl g).x (gtr g).x xy.x

def is_in_grid (bb : bounding_box) (xy : point) :=
  is_bounded bb.p₂.y bb.p₁.y xy.y ∧ is_bounded bb.p₁.x bb.p₂.x xy.x

attribute [reducible]
instance has_mem_grid : has_mem point α := ⟨flip is_in_grid'⟩

attribute [reducible]
instance has_mem_bb : has_mem point bounding_box := ⟨flip is_in_grid⟩

lemma gip_in_grid {p₁ p₂ : point} {h : p₁ ↗ p₂} :
  ∀{a}, a ∈ gip p₁ p₂ → a ∈ (⟨p₁, p₂, h⟩ : bounding_box) :=
assume a h,
begin
  cases a with al ar,
  simp [gip] at h,
  cases h with l h, cases h with h h₁,
  cases h with a₁ h₂, cases h₂ with h₂ h₃,
  have h₄ := range_pure_bounded h₂,
  rw ← h₃ at h₁,
  have h₅ := grp_bounds h₁,
  split; split,
    {
      simp [bounding_box.p₁],
      cases h₅ with h₅l h₅r,
      cases h₅l with h₅l₁ h₅l₂,
      cases h₅r with h₅r₁ h₅r₂,
      simp [point.x, point.y] at *,
      cases h₄ with h₄l h₄r, 
      transitivity a₁; assumption
    },
    {exact lt_of_le_of_lt (le_of_lt_add_one h₅.right.right) h₄.right},
    {exact h₅.left.left},
    {exact h₅.left.right}
end

def gip_g_in_grid {g : α} :
  ∀{a}, a ∈ gip_g g → a ∈ (bbox_of_grid g) :=
assume a h, gip_in_grid h

private def make_bounded_idx {g : α} {p : point} (h : p ∈ (bbox_of_grid g)) :
  bounded ((bl g).x) ((gtr g).x) ×
  bounded ((gtr g).y) ((bl g).y) :=
    (make_bounded h.right, make_bounded h.left)

private def make_bounded_indices (is : list point)
                         (h : ∀p, p ∈ is → p ∈ (bbox_of_grid g)) :
  list (
    bounded ((bl g).x) ((gtr g).x) ×
    bounded ((gtr g).y) ((bl g).y)
  ) := map (λp : {x // x ∈ is},
         (⟨p.val.x, (h p.val p.property).right⟩,
          ⟨p.val.y, (h p.val p.property).left⟩)) (attach is)

instance decidable_is_in_grid' {xy : point}
   : decidable (is_in_grid' g xy) :=
   by simp [is_in_grid']; apply_instance

instance decidable_is_in_grid (bb : bounding_box) {xy : point}
   : decidable (is_in_grid bb xy) :=
   by simp [is_in_grid]; apply_instance

instance decidable_is_in_grid'_op {xy : point}
   : decidable (xy ∈ g) :=
   by simp [(∈), is_in_grid', flip]; apply_instance

instance decidable_is_in_grid_op (bb : bounding_box) {xy : point}
   : decidable (xy ∈ bb) :=
   by simp [is_in_grid, (∈), flip]; apply_instance

private def inject_into_bounded (p : {x // x ∈ gip_g g}) :
  bounded ((bl g).x) ((gtr g).x) ×
  bounded ((gtr g).y) ((bl g).y) :=
  make_bounded_idx (gip_g_in_grid p.property)

private def inject_row_into_bounded
  {a b r} (p : {x // x ∈ grp a b r}) : 
  bounded a b × bounded r (r + 1) :=
  ⟨⟨p.val.x, (grp_bounds p.property).1⟩,
   ⟨p.val.y, (grp_bounds p.property).2⟩⟩

private lemma blgx_trgx_of_mem {g : α} {x} {y} (h : point.mk x y ∈ g) :
  (bl g).x < (gtr g).x :=
begin
  simp only [(∈), flip, is_in_grid'] at h,
  exact lt_of_le_of_lt h.2.1 h.2.2,
end

theorem in_gip_g_of_in_g {α : Type*} [grid α] {g : α} {p}
  (h : p ∈ g) : p ∈ gip_g g :=
begin  
  cases p with x y,
  simp [-gtr, gip_g, gip],
  have h₂ : y ∈ range_pure (gtr g).y (bl g).y,
    {
      simp [(∈), flip, is_in_grid'] at h,
      exact in_range_iff.2 h.1
    },
  split, {
    split,
      {existsi y, exact ⟨h₂, by simp [grp]⟩},
      {
        generalize h₂ : range_pure ((bl g).x) ((gtr g).x) = l₁,
        generalize h₃ : repeat y ( |(gtr g).x - (bl g).x| ) = l₂,
        rw point_in_zip_prod_iff,
        apply point_in_zip_repeat_right _ h₃ _,
          {
            simp [
              h₂.symm, h₃.symm, range_length_pure, length_repeat,
              int.le_of_lt (blgx_trgx_of_mem h)
            ]
          },
          {
            rw [← h₂, in_range_iff],
            simp only [(∈), flip, is_in_grid'] at h, 
            exact h.2
          }
      }
    } 
end

theorem in_grid_iff_in_gip_g {p} {g : α} : p ∈ g ↔ p ∈ gip_g g :=
  ⟨
    in_gip_g_of_in_g,
    λh, by apply gip_in_grid h; exact grid_is_bounding_box
  ⟩
  
private def grid_point_of_mem {p} (h : p ∈ g) : grid_point g :=
  ⟨make_bounded h.1, make_bounded h.2⟩

def generate :=
  map (abs_data g ∘ grid_point_of_prod ∘ inject_into_bounded g)
      (attach $ gip_g g)

notation `℘` g:max := generate g

section grid_instances

instance grid_functor : functor grid₀ := {
  map := λα β f g, ⟨g.r, g.c, g.h, vector.map f g.data⟩
}

instance grid_functor_law : is_lawful_functor grid₀ := {
  id_map := λα ⟨r, c, h, d⟩, by simp [(<$>)],
  comp_map := λα β γ f h ⟨r, c, h, d⟩, by simp [(<$>)]
}

instance agrid_functor : functor agrid₀ := {
  map := λα β f g, ⟨⟨g.r, g.c, g.h, vector.map f g.data⟩, g.o⟩
}

instance agrid_functor_law : is_lawful_functor agrid₀ := {
  id_map := λα ⟨⟨r, c, h, d⟩, o⟩, by simp [(<$>)],
  comp_map := λα β γ f h ⟨⟨r, c, h, d⟩, o⟩, by simp [(<$>)]
}

instance fgrid_functor : functor fgrid := {
  map := λα β f g, ⟨g.r, g.c, g.h, g.o, λx y, f (g.data x y)⟩
}

instance fgrid_functor_law : is_lawful_functor fgrid := {
  id_map := λα ⟨r, c, h, d, o⟩, by simp [(<$>)],
  comp_map := λα β γ f h ⟨r, c, h, d, o⟩, by simp [(<$>)]
}

end grid_instances

attribute [simp]
lemma grid_fmap_r {α β : Type} {g : grid₀ α} {f : α → β} : (f <$> g).r = g.r :=
  by simp [(<$>)]

attribute [simp]
lemma grid_fmap_c {α β : Type} {g : grid₀ α} {f : α → β} : (f <$> g).c = g.c :=
  by simp [(<$>)]

attribute [simp]
lemma agrid_fmap_r {α β : Type} {g : agrid₀ α} {f : α → β} : (f <$> g).r = g.r
  := by simp [(<$>)]

attribute [simp]
lemma agrid_fmap_c {α β : Type} {g : agrid₀ α} {f : α → β} : (f <$> g).c = g.c
  := by simp [(<$>)]

def point_of_bounded_prod {a b c d : ℤ} : bounded a b × bounded c d → point
  | ⟨⟨a, _⟩, ⟨c, _⟩⟩ := ⟨a, c⟩

lemma gip_g_unempty : ¬empty_list (gip_g g) :=
assume contra,
begin
  simp [gip_g, gip] at contra,
  have c₁ : ¬empty_list (
    range_pure (
      (tr (bl g) (rows g) (cols g)).y
    ) (bl g).y
  ),
    {
      simp only [empty_list], intros c₂, symmetry' at c₂,
      rw range_pure_empty_iff at c₂,
      have c₃ := @grid_is_bounding_box _ _ g,
      rw grid_bounded_iff at c₃,
      exact absurd (lt_of_le_of_lt c₂ c₃.2) (lt_irrefl _)
    },
  have c₂ := @not_map_empty_of_not_empty _ _ _
    (grp (bl g).x (tr (bl g) (rows g) (cols g)).x) c₁,
  have c₃ := not_join_empty_of_not_empty contra,
  cases c₃,
    {contradiction},
    {
      revert c₃ contra c₂ c₁,
      generalize c₆ : bl g = bl,
      generalize c₅ : tr bl (rows g) (cols g) = tr',
      generalize c₄ :
        map (grp (bl.x) (tr'.x)) (range_pure (tr'.y) (bl.y)) = l,
      intros,
      have c₅ : ∃z ∈ l, ¬empty_list z,
        {
          let h := grp bl.x tr'.x tr'.y,
          have h₁ : h = grp bl.x tr'.x tr'.y, by cc,
          existsi h, simp, split,
            {
              rw h₁, revert c₄,
              generalize h₂ : range_pure tr'.y bl.y = l₁, intros,
              cases l₁ with w ws,
                {
                  rw range_pure_empty_iff at h₂,
                  let h₃ := @grid_is_bounding_box _ _ g,
                  rw grid_bounded_iff at h₃,
                  simp [gtr, c₆, c₅] at h₃,
                  exact absurd (lt_of_le_of_lt h₂ h₃.2) (lt_irrefl _)
                },
                {
                  dsimp at c₄,
                  have h₃ : w = tr'.y,
                    {
                      unfold1 range_pure at h₂,
                      rw if_pos at h₂,
                        {injection h₂ with h₃ _, rw h₃},
                        {
                          let h₃ := @grid_is_bounding_box _ _ g,
                          rw grid_bounded_iff at h₃,
                          simp [gtr, c₆, c₅] at h₃,
                          exact h₃.2
                        }
                    },
                  simp [c₄.symm, h₃, mem_cons_eq]
                },
            },
            {
              unfold1 grp at h₁,
              have h₂ : tr'.x > bl.x,
                {
                  let h₃ := @grid_is_bounding_box _ _ g,
                  rw grid_bounded_iff at h₃,
                  simp [gtr] at h₃, rw [c₆, c₅] at h₃,
                  exact h₃.1
                },
              have h₄ : range_pure (bl.x) (tr'.x) =
                        bl.x :: range_pure (bl.x + 1) (tr'.x),
                {
                  generalize t₁ : bl.x :: range_pure (bl.x + 1) (tr'.x) = t,
                  unfold1 range_pure, simpa [if_pos h₂]
                },
              rw h₄ at h₁,
              have h₅ : repeat (tr'.y) ( |tr'.x - bl.x| ) =
                tr'.y :: repeat tr'.y (( |tr'.x - bl.x| ) - 1),
                {
                  rw repeat_more, simp [(≥)],
                  apply nat.succ_le_of_lt (lt_of_coe_nat_lt_coe_nat _),
                  rw [nat_abs_of_nonneg, ← sub_eq_add_neg, lt_sub],
                    {simp, exact h₂},
                    {
                      simp only [(≥)], rw ← sub_eq_add_neg,
                      apply int.le_of_lt,
                      rw sub_pos,
                      exact h₂
                    }
                },
              rw [h₅, zip_cons_cons, map_cons] at h₁, rw h₁,
              apply not_empty_cons
            }
        },
      cases c₅ with c₅l c₅r, cases c₅r with c₅₁ c₅₂, rw [← c₄, ← c₅] at c₅₁,
      simp only [gtr] at c₃, subst c₆,
      exact absurd (c₃ c₅l c₅₁) c₅₂
    } 
end

lemma length_gip {p₁ p₂ : point} (h : p₁ ↗ p₂) :
  length (gip p₁ p₂) = |p₁.y - p₂.y| * |p₂.x - p₁.x| :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff, ← nat_abs_mul],
  rw grid_bounded_iff at h,
  have h₁ : (p₁.y - p₂.y) * (p₂.x - p₁.x) > 0,
    {cases p₁, cases p₂, apply mul_pos; omega},
  simp [
    -sub_eq_add_neg, gip, length_join, (∘), length_grp h.1,
    range_length_pure (int.le_of_lt h.2),
    nat_abs_of_nonneg (int.le_of_lt h₁)
  ],
  repeat {rw nat_abs_of_nonneg}; simp [-sub_eq_add_neg, ge_from_le];
  apply int.le_of_lt; simp [h.1, h.2]
end

theorem length_gip_g : length (gip_g g) = rows g * cols g :=
  by simp [
       gip_g, length_gip, rows_eq_bly_sub_try, cols_eq_trx_sub_blx,
       grid_is_bounding_box
     ]

private theorem length_generate {α : Type*} [grid α] (g : α) :
  length (℘ g) = grid_rows g * grid_cols g :=
by unfold generate gip_g;
   rw [
     length_map, grid_rows_eq_bly_sub_try, grid_cols_eq_trx_sub_blx,
     length_attach, length_gip_g, rows_eq_bly_sub_try, cols_eq_trx_sub_blx
   ]

lemma length_generate_eq_size :
  length (℘ g) = size g := by simp [size, length_generate]

lemma map_generate_map_a {α β : Type} {g : agrid₀ α} {f : α → β} :
  f <$> (℘ g) = ℘ (f <$> g) :=
begin
  rcases g with ⟨⟨r, c, h, d⟩, o⟩,
  simp [(<$>), generate],
  generalize h₁ :
    {agrid₀. to_grid₀ :=
      {r := ({agrid₀. to_grid₀ :=
        {r := r, c := c, h := h, data := d}, o := o}.to_grid₀).r,
       c := ({agrid₀. to_grid₀ :=
        {r := r, c := c, h := h, data := d}, o := o}.to_grid₀).c,
       h := _,
       data := vector.map f d},
       o := o} = g₁,
  unfold_projs at h₁,
  generalize h₂ :
    {agrid₀. to_grid₀ := {r := r, c := c, h := h, data := d}, o := o} = g₂,
  simp [abs_data, data], rw [← h₁, ← h₂],
  simp [vector.nth_map, uncurry_def, (∘)],
  refl
end

lemma map_generate_map_f {α β : Type} (g : fgrid α) {f : α → β} :
  f <$> (℘ g) = ℘ (f <$> g) :=
begin
  rcases g with ⟨r, c, h, o, d⟩,
  simp [(<$>), generate, abs_data, data, uncurry_def, (∘)],
  refl
end

lemma dec_grid_len_eq_indices_len :
  length (℘ g) = length (gip_g g) :=
  by simp [length_generate, length_gip_g]

private lemma linear_correct {g : α} {p : grid_point g} :
  z_of_bounded ((relpoint_of_gpoint p).x) * cols g +
  z_of_bounded ((relpoint_of_gpoint p).y) < length (℘ g) :=
begin
  cases p with x y,
  simp [
    relpoint_of_gpoint, length_generate, grid_cols, grid_rows, z_of_bounded
  ], rw add_comm,
  rw cols_eq_trx_sub_blx, rw rows_eq_bly_sub_try,
  revert x, revert y,
  generalize h₂ : (bl g).x = x₁, generalize h₃ : (gtr g).x = x₂,
  generalize h₄ : (bl g).y = y₁, generalize h₅ : (gtr g).y = y₂, intros,
  rcases y with ⟨h₁, h₂, h₃⟩, rcases x with ⟨h₄, h₅, h₆⟩,
  apply linearize_array; split; simp [z_of_bounded];
  rw [← int.coe_nat_lt];
  try { rw cols_eq_trx_sub_blx }; try { rw rows_eq_bly_sub_try };
  repeat { rw int.nat_abs_of_nonneg };
  repeat { rw ← sub_eq_add_neg }; simp [ge_from_le]; try { cc };
  apply le_add_of_neg_add_le; simp; try { cc }; apply int.le_of_lt;
  apply lt_of_le_of_lt; assumption
end

def agrid_of_fgrid {α : Type} (g : fgrid α) : agrid₀ α :=
    ⟨⟨g.r, g.c, g.h, ⟨generate g, length_generate_eq_size _⟩⟩, g.o⟩

def fgrid_of_agrid {α : Type} (g : agrid₀ α) : fgrid α :=
  ⟨g.r, g.c, g.h, g.o, λx y, abs_data g ⟨x, y⟩⟩

instance f_a_coe {α : Type} : has_coe (fgrid α) (agrid₀ α) := ⟨agrid_of_fgrid⟩
instance a_f_coe {α : Type} : has_coe (agrid₀ α) (fgrid α) := ⟨fgrid_of_agrid⟩

attribute [simp]
lemma agrid_of_fgrid_r {α : Type} {g : fgrid α} :
  (agrid_of_fgrid g).r = g.r := by simp [agrid_of_fgrid]

attribute [simp]
lemma agrid_of_fgrid_c {α : Type} {g : fgrid α} :
  (agrid_of_fgrid g).c = g.c := by simp [agrid_of_fgrid]

attribute [simp]
lemma agrid_of_fgrid_o {α : Type} {g : fgrid α} :
  (agrid_of_fgrid g).o = g.o := by simp [agrid_of_fgrid]

attribute [simp]
lemma fgrid_of_agrid_r {α : Type} {g : agrid₀ α} :
  (fgrid_of_agrid g).r = g.r := by simp [fgrid_of_agrid]

attribute [simp]
lemma fgrid_of_agrid_c {α : Type} {g : agrid₀ α} :
  (fgrid_of_agrid g).c = g.c := by simp [fgrid_of_agrid]

attribute [simp]
lemma fgrid_of_agrid_o {α : Type} {g : agrid₀ α} :
  (fgrid_of_agrid g).o = g.o := by simp [fgrid_of_agrid]

attribute [simp]
lemma agrid_of_fgrid_gtr {α : Type} {g : fgrid α} :
  gtr (agrid_of_fgrid g) = gtr g :=
    by simp [expand_gtr, bl, cols, rows, agrid_of_fgrid]

attribute [simp]
lemma fgrid_of_agrid_gtr {α : Type} {g : agrid₀ α} :
  gtr (fgrid_of_agrid g) = gtr g :=
    by simp [expand_gtr, bl, cols, rows, fgrid_of_agrid]

private theorem nth_le_grp {n} {a b r : ℤ} (h : a < b) (H) :
  nth_le (grp a b r) n H = ⟨a + n % |b - a|, r⟩ :=
begin
  rw ← option.some_inj, rw ← nth_le_nth H,
  induction n with n ih generalizing a b,
    {simp [expand_grp h]},
    {
      by_cases h₁ : a + 1 < b,
        {
          specialize @ih (a + 1) b h₁ _,
            {
              simp [expand_grp h, -sub_eq_add_neg], rw ih,
              simp [(abs_minus_plus h).symm, -sub_eq_add_neg],
              rw length_grp h at H,
              rw [
                mod_eq_of_lt (coe_zero_le _),
                mod_eq_of_lt (
                  le_add_of_le_of_nonneg zero_le_one (coe_zero_le _)
                )
              ],
              {
                rw [← nat.one_add,
                  ← int.coe_nat_lt_coe_nat_iff,
                  int.coe_nat_add
                ] at H, exact H,
              },
              {
                rw ← nat.one_add at H,
                rw [
                  int.coe_nat_sub,
                  lt_sub_iff_add_lt,
                  add_comm, ← int.coe_nat_add,
                  int.coe_nat_lt_coe_nat_iff
                ],
                {exact H},
                {
                  rw [add_comm, ← lt_sub_iff_add_lt] at h₁,
                  rw [← int.coe_nat_le_coe_nat_iff,
                      nat_abs_of_nonneg (nonneg_of_lt h)],
                  apply int.le_of_lt, simpa
                }
              }
            },
            {
              rw length_grp at *; try { assumption },
              rw ← nat.add_one at H,
              have : n < |b - a| - 1, from nat.lt_sub_right_of_add_lt H,
              rwa ← abs_minus_plus h
            }
        },
        {
          have : a + 1 = b,
            {
              rw not_lt_iff_eq_or_lt at h₁,
              cases h₁,
                {assumption},
                {
                  rw lt_add_one_iff at h₁,
                  exact absurd (lt_of_lt_of_le h h₁) (lt_irrefl _)
                }
            },
          rw [expand_grp h, this] at H, simp at H,
          have : length (grp b b r) = 0,
            by simp [grp, range_pure_empty_iff.2 (le_refl _), zip_nil_left],
          rw this at H, exfalso, simp at H, cases H, cases H_a
        }
    }
end

theorem nth_grp {n} {a b r : ℤ} (h : a < b) (H : n < length (grp a b r)) :
  nth (grp a b r) n = some ⟨a + n % |b - a|, r⟩ :=
  by rw nth_le_nth H; exact congr_arg _ (nth_le_grp h _)

theorem nth_le_gip {n} {p₁ p₂ : point} (h : p₁ ↗ p₂) (H) :
  nth_le (gip p₁ p₂) n H =
  ⟨p₁.x + n % |p₂.x - p₁.x|, p₂.y + n / |p₂.x - p₁.x|⟩ :=
begin
  cases p₁ with x₁ y₁, cases p₂ with x₂ y₂,
  have x₁x₂ : x₁ < x₂, from (grid_bounded_iff.1 h).1,
  have y₁y₂ : y₂ < y₁, from (grid_bounded_iff.1 h).2,
  rw [← option.some_inj, ← nth_le_nth H], rw length_gip h at H,
  repeat { rw nat_abs_of_nonneg (nonneg_of_lt x₁x₂)},
  simp [-sub_eq_add_neg] at *,
  have : y₂ = y₁ - (y₁ - y₂), from (sub_sub_cancel _ _).symm,
  rw this, clear this,
  have : y₁ - y₂ = ↑|y₁ - y₂|,
    by rw nat_abs_of_nonneg; exact nonneg_of_lt y₁y₂,
  rw this, clear this,
  generalize hrows : |y₁ - y₂| = rows, rw hrows at H,
  induction rows with rows ih generalizing y₁ y₂ n,
    {exfalso, simp at H, cases H},
    {
      rw expand_row_gip,
        {
          by_cases h₁ : n < |x₂ - x₁|,
            {
              simp [-sub_eq_add_neg], rw [nth_split, nth_grp];
                try {simpa [length_grp x₁x₂]},
                congr' 2,
                rw [
                  ← int.coe_nat_lt_coe_nat_iff,
                  nat_abs_of_nonneg (nonneg_of_lt x₁x₂)
                ] at h₁,
                rw div_eq_zero_of_lt (coe_zero_le _) h₁,
                simp [x₁x₂]
            },
            {
              generalize hcols : x₂ - x₁ = cols,
              have rowsnezero : rows ≠ 0, assume contra,
                by simp [contra, -sub_eq_add_neg] at H; contradiction,
              have colsnezero : cols ≠ 0, assume contra,
                {
                  have : x₁ = x₂, by rw [contra, sub_eq_zero] at hcols; cc,
                  rw this at x₁x₂,
                  exact absurd x₁x₂ (lt_irrefl _)
                },
              have x₂x₁n : |x₂ - x₁| ≤ n, from not_lt.1 h₁,
              have lenok : ¬n < length (grp x₁ x₂ (y₁ - (1 + ↑rows))),
                by simpa [length_grp x₁x₂, -sub_eq_add_neg],
              simp [-sub_eq_add_neg], rw nth_split_second lenok,
              have : 1 + (y₁ - (1 + ↑rows)) = y₁ - ↑rows,
                by rw [← sub_sub, add_sub, add_sub_cancel'_right], rw this,
              by_cases h₂ : y₂ + 1 < y₁,
                {
                  have h₃ : {x := x₁, y := y₁}↗{x := x₂, y := y₂ + 1},
                    from ⟨x₁x₂, h₂⟩,
                  have lenok :
                    n - length (grp x₁ x₂ (y₁ - (1 + ↑rows))) < rows * |x₂ - x₁|,
                    {
                      rw nat.succ_mul at H,
                      rw [
                        length_grp x₁x₂, ← int.coe_nat_lt_coe_nat_iff,
                        int.coe_nat_sub x₂x₁n, int.coe_nat_mul,
                        sub_lt_iff_lt_add, ← int.coe_nat_mul, ← int.coe_nat_add
                      ],
                      rwa int.coe_nat_lt_coe_nat_iff
                    },
                  have rowsok : |y₁ - (y₂ + 1)| = rows,
                    by rw [← abs_minus_plus y₁y₂, hrows, nat.succ_sub_one],
                  rw @ih y₁ (y₂ + 1) (n - length (grp x₁ x₂ (y₁ - (1 + ↑rows))))
                         h₃ h₂ rowsok lenok,
                  rw length_grp x₁x₂, simp [-sub_eq_add_neg],
                  exact ⟨
                    begin
                      rw [
                        int.coe_nat_sub x₂x₁n, nat_abs_of_nonneg, ← hcols,
                        mod_eq_mod_iff_mod_sub_eq_zero, mod_eq_zero_of_dvd
                      ],
                      simp, rw ← dvd_neg, simp,
                      exact nonneg_of_lt x₁x₂
                    end,
                    begin
                      rw [
                        int.coe_nat_sub x₂x₁n,
                        nat_abs_of_nonneg (nonneg_of_lt x₁x₂),
                        add_sub, add_comm _ y₁, sub_eq_add_neg, add_assoc,
                        add_sub_assoc
                      ], apply congr_arg,
                      rw [← sub_sub, add_comm],
                      conv_rhs { rw sub_eq_add_neg },
                      rw add_right_cancel_iff, rw hcols,
                      conv_rhs { simp },
                      rw ← int.add_mul_div_left _ _ colsnezero, simp
                    end
                  ⟩
                },
                {
                  have h₃ : y₂ + 1 = y₁,
                    {
                      rw not_lt_iff_eq_or_lt at h₂,
                      cases h₂,
                        {assumption},
                        {
                          rw lt_add_one_iff at h₂,
                          exact absurd (lt_of_lt_of_le y₁y₂ h₂) (lt_irrefl _)
                        }
                    },
                  have h₄ : |y₁ - y₂| = 1, by simp [h₃.symm, add_sub_cancel'],
                  rw h₄ at hrows, injection hrows with contra, cc
                }
            }
      },
      {
        exact ⟨
          (grid_bounded_iff.1 h).1,
          begin
            simp [
              sub_lt_iff_lt_add, lt_add_iff_pos_right, -sub_eq_add_neg
            ],
            cases rows,
              {exact zero_lt_one},
              {exact lt_trans zero_lt_one (lt_add_succ _ _)}
          end
        ⟩
      },
    }
end

theorem nth_le_gip_g {n} (H) :
  nth_le (gip_g g) n H = ⟨(bl g).x + n % cols g, (gtr g).y + n / cols g⟩ :=
begin
  rw cols_eq_trx_sub_blx,
  exact @nth_le_gip n (gbl g) (gtr g) grid_is_bounding_box H
end

theorem nth_generate {n} (H) :
  nth_le (℘ g) n H =
  abs_data g ⟨
    ⟨(gtr g).y + n / cols g, ⟨
      by simp,
      idx_div_cols_bounded (by rwa length_generate_eq_size at H)
    ⟩⟩,
    ⟨(bl g).x + n % cols g, ⟨
      by simp,
      idx_mod_cols_bounded (by rwa length_generate_eq_size at H)⟩
  ⟩⟩ :=
begin
  rw length_generate at H,
  rw [← option.some_inj, ← nth_le_nth],
  simp only [
    abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point, uncurry, expand_gtr,
    data_data_option, generate, nth_map
  ],
  have : n < length (attach (gip_g g)), by simpa [length_attach, length_gip_g],
  simp [
    nth_le_nth this, inject_into_bounded, make_bounded_idx, make_bounded,
    nth_le_gip_g, grid_point_of_prod, data_option
  ],
  repeat { rw dif_pos }, apply congr_arg,
  simp [
    abs_data, relpoint_of_gpoint, prod_of_rel_point, uncurry, expand_gtr
  ]
end

theorem nth_generate' {n} (h : n < length ℘ g) :
  nth (℘ g) n = 
  some (abs_data g ⟨
    ⟨(gtr g).y + n / cols g, ⟨
      by simp,
      idx_div_cols_bounded (by rwa length_generate_eq_size at h)
    ⟩⟩,
    ⟨(bl g).x + n % cols g, ⟨
      by simp,
      idx_mod_cols_bounded (by rwa length_generate_eq_size at h)⟩
  ⟩⟩) := by simp [nth_le_nth h, congr_arg, nth_generate]

lemma generate_eq_data {α : Type} (g : agrid₀ α) :
  ℘ g = g.data.to_list :=
begin
  have h₁ : length (℘ g) = rows g * cols g,
    from length_generate _,
  have h₂ : length (g.data.to_list) = rows g * cols g,
    by simp [rows, cols],
  apply ext_le (eq.trans h₁ h₂.symm) (λi hi₁ hi₂, _),
  rw h₁ at hi₁, rw h₂ at hi₂,
  have : hi₁ = hi₂, by cc, subst this, dedup,
  rw ← option.some_inj, repeat { rw ← nth_le_nth },
  clear hi₁, clear hi₂, rename hi₁_1 hi, clear h₁, clear h₂,
  cases g with g o, cases g with r c h data,
  simp [-sub_eq_add_neg, rows, cols] at *,
  cases data with data hd,
  rw [nth_le_nth, nth_generate],
  simp [
    nth_le_nth, nth_generate, abs_data, relpoint_of_gpoint,
    prod_of_rel_point, uncurry,
    expand_gtr, bl, tl, rows, cols, relative_grid.data, vector.nth
  ],
  rw nth_le_nth,
  have : |↑i % ↑c| + |↑r + (↑i / ↑c + -↑r)| * c = i,
    {
      rw [← int.coe_nat_eq_coe_nat_iff, int.coe_nat_add, int.coe_nat_mul],
      repeat { rw nat_abs_of_nonneg }, rw [add_mul, add_mul],
      simp,
      rw [mul_comm, mod_add_div], rw ← sub_eq_add_neg,
      rw [add_sub_cancel'_right, ← int.coe_nat_div],
      apply coe_zero_le,
      rw ← int.coe_nat_mod, apply coe_zero_le,
    },
  repeat { rw ← nth_le_nth }, simp at this, simp only [this], rwa hd,
  simpa [length_generate_eq_size, size, rows, cols]
end

private theorem generate_inj_a_a {α : Type} {g₁ g₂ : agrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = ℘ g₂) : g₁ = g₂ :=
begin
  repeat { rw generate_eq_data at h },
  cases g₁ with g₁ g₁o, cases g₁ with g₁r g₁c g₁h g₁d,
  cases g₂ with g₂ g₂o, cases g₂ with g₂r g₂c g₂h g₂d,
  dsimp at hrows hcols horig h,
  subst hrows, subst hcols, subst horig,
  congr, exact vector.to_list_inj h
end

theorem grid_eq_iff_a_a {α : Type} {g₁ g₂ : agrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
⟨λh, h ▸ rfl, generate_inj_a_a hrows hcols horig⟩

private theorem generate_inj_f_f {α : Type} {g₁ g₂ : fgrid α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = ℘ g₂) : g₁ = g₂ :=
begin
  have hl₁ : length (℘ g₁) = g₁.r * g₁.c,
    from length_generate _,
  have hl₂ : length (℘ g₂) = g₂.r * g₂.c,
    from length_generate _,
  cases g₁ with g₁r g₁c g₁h g₁o g₁d,
  cases g₂ with g₂r g₂c g₂h g₂o g₂d,
  dsimp at hrows hcols horig hl₁ hl₂,
  subst hrows, subst hcols, subst horig,
  congr,
  apply funext (λx, _), apply funext (λy, _),
  cases x with x xbounds, cases y with y ybounds,
  have rowsnezero : g₁r ≠ 0, assume contra,
    by simp [contra] at g₁h; exact absurd g₁h (lt_irrefl _),
  have colsnezero : g₁c ≠ 0, assume contra,
    by simp [contra] at g₂h; exact absurd g₂h (lt_irrefl _),
  let tly := g₁o.y - g₁r,
  let tlx := g₁o.x,
  let i := |x - tly| * g₁c + |y - tlx|,
  have hi : i = |x - tly| * g₁c + |y - tlx|, refl,
  have r_nonneg : x - tly ≥ 0,
    by simp only [ge_from_le, le_sub_iff_add_le, zero_add]; exact xbounds.1,
  have c_nonneg : y - tlx ≥ 0,
    by simp only [ge_from_le, le_sub_iff_add_le, zero_add]; exact ybounds.1,
  have i_nonneg : 0 ≤ i,
    {
      rw [hi, ← int.coe_nat_le_coe_nat_iff, int.coe_nat_add, int.coe_nat_mul],
      repeat { rw nat_abs_of_nonneg; try { assumption } },
      apply le_add_of_le_of_nonneg _ c_nonneg,
      suffices h : (x - (g₁o.y - ↑g₁r)) * ↑g₁c ≥ 0, from h,
      apply mul_nonneg r_nonneg (int.le_of_lt _), simp,
      exact (gt_and_gt_of_mul_gt g₁h).2
    },
  have i_bounded : i < g₁r * g₁c,
    {
      rw hi,
      apply linearize_array; unfold is_bounded; split;
        try { rw ← int.coe_nat_le_coe_nat_iff };
        try { rw ← int.coe_nat_lt_coe_nat_iff };
        rw nat_abs_of_nonneg; try { assumption },
      rw sub_lt_iff_lt_add', exact ybounds.2,
      rw [← sub_add, add_comm],
      apply add_lt_of_le_of_neg (le_refl _),
      rw [sub_lt_iff_lt_add, zero_add],
      exact xbounds.2
    },
  have h₁ : ∀hh,
    list.nth_le (℘ (
      {r := g₁r, c := g₁c, h := g₁h, o := g₁o, data := g₁d} : fgrid α
    )) i hh =
    list.nth_le (℘ (
      {r := g₁r, c := g₁c, h := g₂h, o := g₁o, data := g₂d} : fgrid α
    )) i (hl₂.symm ▸ i_bounded), { rw h, intro, refl },
  specialize h₁ (hl₁.symm ▸ i_bounded),
  simp [
    -sub_eq_add_neg, generate, abs_data, inject_into_bounded,
    grid_point_of_prod, prod_of_rel_point, make_bounded_idx,
    make_bounded, relpoint_of_gpoint, uncurry,
    relative_grid.data, vector.nth, tl, bl, rows, nth_le_gip_g,
    bl, expand_gtr, rows, cols
  ] at h₁,
  unfold_coes at h₁, simp only [z_of_bounded] at h₁,
  have : g₁o.y - of_nat g₁r + of_nat (
          |g₁o.y - of_nat g₁r +
          (of_nat ( |y - tlx| ) + of_nat ( |x - tly| ) * of_nat g₁c) /
          of_nat g₁c - (g₁o.y - of_nat g₁r)| ) = x,
    {
      repeat { rw of_nat_eq_coe }, repeat { rw add_sub },
      rw add_sub_cancel',
      repeat { rw nat_abs_of_nonneg; try { assumption } },
      change g₁o.y - ↑g₁r with tly,
      rw [int.add_mul_div_right, ← add_assoc, add_sub,
          div_eq_zero_of_lt c_nonneg (sub_lt_iff_lt_add'.2 ybounds.2)],
      simp, simp [colsnezero],
      rw @int.add_mul_div_right _ _ g₁c (by simp [colsnezero]),
      apply add_nonneg, apply int.div_nonneg c_nonneg,
      simp [ge_from_le], exact r_nonneg
    },
  simp only [this] at h₁,
  have : g₁o.x + of_nat
          ( |g₁o.x + of_nat ( |y - tlx| ) % of_nat g₁c - g₁o.x| ) = y,
    {
      repeat { rw of_nat_eq_coe }, repeat { rw add_sub },
      rw add_sub_cancel',
      repeat { rw nat_abs_of_nonneg; try { assumption } },
      rw mod_eq_of_lt c_nonneg,
      simp [tlx],
      apply sub_lt_iff_lt_add'.2 ybounds.2,
      apply mod_nonneg, simp [colsnezero]
    },
  simp only [this] at h₁,
  exact h₁
end

theorem grid_eq_iff_f_f {α : Type} {g₁ g₂ : fgrid α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
⟨λh, h ▸ rfl, generate_inj_f_f hrows hcols horig⟩

def row (n : bounded 0 (relative_grid.rows g)) :
  (bounded 0 (relative_grid.cols g)) → relative_grid.carrier α :=
  relative_grid.data g n

def col (n : bounded 0 (relative_grid.cols g)) :
  (bounded 0 (relative_grid.rows g)) → relative_grid.carrier α :=
  flip (relative_grid.data g) n

def top :=
  row g ⟨
    0,
    ⟨le_refl _, and.elim_left (gt_and_gt_of_mul_gt (relative_grid.unempty g))⟩
  ⟩

def bot :=
  row g ⟨nat.pred (relative_grid.rows g),
         ⟨nat.zero_le _,
          nat.pred_lt (ne_of_gt (gt_and_gt_of_mul_gt (relative_grid.unempty g)).1)⟩
        ⟩

def left :=
  have h : relative_grid.cols g > 0,
    from (gt_and_gt_of_mul_gt (relative_grid.unempty g)).2,
  col g ⟨0, and.intro (le_refl _) h⟩

def right :=
  have h : relative_grid.cols g > 0,
    from (gt_and_gt_of_mul_gt (relative_grid.unempty g)).2,
  col g ⟨nat.pred (relative_grid.cols g),
         ⟨nat.zero_le _, nat.pred_lt (ne_of_gt h)⟩⟩

def grid_bounds : bounding_box :=
  ⟨gbl g, gtr g, grid_is_bounding_box⟩

def overlaid_by (p₁ p₂ : bounding_box) :=
  (p₂.p₁.x ≤ p₁.p₁.x ∧ p₁.p₂.x ≤ p₂.p₂.x) ∧
  (p₂.p₂.y ≤ p₁.p₂.y ∧ p₁.p₁.y ≤ p₂.p₁.y)

def in_grid_bounded (p : point)
  (h : is_in_grid' g p) :=
  let ⟨left, right⟩ :=
    h in (make_bounded left, make_bounded right)

instance overlaid_decidable (p₁ p₂ : bounding_box) :
  decidable (overlaid_by p₁ p₂) := by simp [overlaid_by]; apply_instance

lemma overlaid_by_refl (bb : bounding_box) : overlaid_by bb bb :=
  by simp [overlaid_by]; repeat {split}; refl

lemma overlaid_by_trans {bb₁ bb₂ bb₃ : bounding_box}
  (h : overlaid_by bb₁ bb₂) (h₁ : overlaid_by bb₂ bb₃) : overlaid_by bb₁ bb₃ :=
begin
  simp [overlaid_by] at *; repeat {split}; transitivity,
  exact h₁.left.left, exact h.left.left,
  exact h.left.right, exact h₁.left.right,
  exact h₁.right.left, exact h.right.left,
  exact h.right.right, exact h₁.right.right
end

lemma overlaid_by_antisymm {bb₁ bb₂ : bounding_box}
  (h : overlaid_by bb₁ bb₂) (h₁ : overlaid_by bb₂ bb₁) : bb₁ = bb₂ :=
begin
  simp [overlaid_by] at *,
  cases h with hl hr, cases h₁ with h₁l h₁r,
  cases hl with hll hlr, cases hr with hrl hrr,
  cases h₁l with h₁ll h₁lr, cases h₁r with h₁rl h₁rr,
  cases bb₁ with b₁p₁ b₁p₂, cases bb₂ with b₂p₁ b₂p₂, congr;
  unfold bounding_box.p₁ bounding_box.p₂ at *;
  cases b₁p₁; cases b₁p₂;
  cases b₂p₁; cases b₂p₂;
  unfold point.x point.y at *; congr;
  apply le_antisymm; assumption
end

lemma is_in_larger {bb₁ bb₂ : bounding_box} {xy : point}
  (h : xy ∈ bb₁) (h₁ : overlaid_by bb₁ bb₂) : xy ∈ bb₂ :=
  ⟨⟨le_trans h₁.right.left h.left.left,
   lt_of_lt_of_le h.left.right h₁.right.right⟩,
   ⟨le_trans h₁.left.left h.right.left,
   lt_of_lt_of_le h.right.right h₁.left.right⟩⟩

private def bounded_prod_of_point {p : point} {g : α} (h : p ∈ g) :
  bounded (bl g).x (gtr g).x ×
  bounded (gtr g).y (bl g).y :=
  ⟨make_bounded h.right, make_bounded h.left⟩

def subgrid (bb : bounding_box) (h : overlaid_by bb (bbox_of_grid g)) :
            fgrid (relative_grid.carrier α) :=
  ⟨rows_of_box bb, cols_of_box bb,
   mul_pos rows_of_box_pos cols_of_box_pos, bb.p₁,
   λx y, abs_data g ⟨⟨x.1,
    begin
      unfold overlaid_by at h, cases x with x hx, simp,
      rw bbox_of_grid_p₁ at h, rw bbox_of_grid_p₂ at h, 
      split,
      have : (bb.p₁).y - ↑(rows_of_box bb) = bb.p₂.y,
        {
          cases bb,
          simp [-sub_eq_add_neg, bounding_box.p₁, bounding_box.p₂, rows_of_box],
          rw nat_abs_of_nonneg (nonneg_of_lt (grid_bounded_iff.1 bb_h).2),
          rw sub_sub_cancel
        },
      rw this at hx,
      exact le_trans h.2.1 hx.1,
      exact lt_of_lt_of_le hx.2 h.2.2
    end⟩, ⟨y.1,
    begin
      unfold overlaid_by at h, cases y with y hy, simp,
      rw bbox_of_grid_p₁ at h, rw bbox_of_grid_p₂ at h, 
      have : (bb.p₁).x + ↑(cols_of_box bb) = bb.p₂.x,
        {
          cases bb,
          simp [-sub_eq_add_neg, bounding_box.p₁, bounding_box.p₂, cols_of_box],
          rw nat_abs_of_nonneg (nonneg_of_lt (grid_bounded_iff.1 bb_h).1),
          rw add_sub_cancel'_right
        },
      rw this at hy,
      split,
      exact le_trans h.1.1 hy.1,
      exact lt_of_lt_of_le hy.2 h.1.2
    end⟩⟩⟩

private def modify_vec
  {α : Type} {m} (v : vector α m) (n : ℕ) (x : α) : vector α m :=
  ⟨update_nth v.to_list n x,
    begin
      rw update_nth_pres_len,
      simp*
    end⟩

def modify_at {α : Type} (p : point) (x : α) (g : agrid₀ α) : agrid₀ α :=
  if h : p ∈ g
  then let ⟨r, c⟩ :=
         relpoint_of_gpoint $
           @grid_point.mk _ _ g
           ⟨p.y, by simp only [(∈)] at h; exact h.left⟩
           ⟨p.x, by simp only [(∈)] at h; exact h.right⟩ in
  ⟨⟨g.r, g.c, g.h, modify_vec g.data (r * g.c + c) x⟩, g.o⟩
  else g

def modify_many {α : Type} (l : list (point × α)) (g : agrid₀ α) : agrid₀ α :=
  foldr (function.uncurry modify_at) g l

def count_grid {α : Type} [grid α] [decidable_eq (relative_grid.carrier α)]
  (g : α) (x : relative_grid.carrier α) := list.count x (℘ g)

lemma gen_aof_eq_gen {α : Type} {g : fgrid α} :
  ℘ (agrid_of_fgrid g) = @generate _ ag_f g :=
begin
  simp [agrid_of_fgrid],
  rw generate_eq_data,
  simp
end

private theorem generate_inj_a_f {α : Type} {g₁ : agrid₀ α} {g₂ : fgrid α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = @generate (fgrid α) _ g₂) : g₁ = g₂ :=
begin
  have hl₁ : length (℘ g₁) = g₁.r * g₁.c,
    from length_generate _,
  have hl₂ : length (℘ g₂) = g₂.r * g₂.c,
    from length_generate _,
  cases g₁ with g₁ g₁o, cases g₁ with g₁r g₁c g₁h g₁d,
  cases g₂ with g₂r g₂c g₂h g₂o g₂d,
  dsimp at hrows hcols horig hl₁ hl₂,
  subst hrows, subst hcols, subst horig,
  unfold_coes, simp [agrid_of_fgrid], unfold_projs,
  simp [h.symm], simp [generate_eq_data], cases g₁d, simp
end

lemma gen_foa_eq_gen {α : Type} {g : agrid₀ α} :
  ℘ (fgrid_of_agrid g) = @generate (agrid₀ α) _ g :=
begin
  have hl₁ : length (℘ g) = rows g * cols g,
    from length_generate _,
  have hl₂ : length (℘ (fgrid_of_agrid g)) = rows g * cols g,
    from length_generate _,
  unfold fgrid_of_agrid at hl₂,
  simp [fgrid_of_agrid],
  apply list.ext_le (hl₂.trans hl₁.symm) (λi hi₁ hi₂, _),
  rw nth_generate, rw nth_generate,
  cases g with g o, cases g with r c h d,
  simp [gtr, tr, bl, rows, cols],
  simp [abs_data, data], simp [relpoint_of_gpoint, prod_of_rel_point, tl, bl,
  rows, cols, function.uncurry],
  refl
end

private theorem generate_inj_f_a {α : Type} {g₁ : fgrid α} {g₂ : agrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = @generate (fgrid α) _ g₂) : g₁ = g₂ :=
begin
  have hl₁ : length (℘ g₁) = g₁.r * g₁.c,
    from length_generate _,
  have hl₂ : length (℘ g₂) = g₂.r * g₂.c,
    from length_generate _,
  cases g₁ with g₁r g₁c g₁h g₁o g₁d,
  cases g₂ with g₂ g₂o, cases g₂ with g₂r g₂c g₂h g₂d,
  dsimp at hrows hcols horig hl₁ hl₂,
  subst hrows, subst hcols, subst horig,
  unfold_coes, simp [fgrid_of_agrid],
  unfold_coes at h,
  rw gen_foa_eq_gen at h,
  apply funext (λx, _), apply funext (λy, _),
  cases x with x xbounds, cases y with y ybounds,
  cases g₂d with d₂ hd₂,
  let tly := g₁o.y - g₁r,
  let tlx := g₁o.x,
  let i := |x - tly| * g₁c + |y - tlx|,
  have hi : i = |x - tly| * g₁c + |y - tlx|, refl,
  have r_nonneg : x - tly ≥ 0,
        {
          simp only [(≥)],
          rw le_sub_iff_add_le,
          rw zero_add,
          exact xbounds.1
        },
  have c_nonneg : y - tlx ≥ 0,
    {
      simp only [(≥)],
      rw le_sub_iff_add_le,
      rw zero_add,
      exact ybounds.1
    },
  have i_nonneg : 0 ≤ i,
    {
      rw hi,
      rw ← int.coe_nat_le_coe_nat_iff,
      rw int.coe_nat_add,
      rw int.coe_nat_mul,
      repeat { rw nat_abs_of_nonneg; try { assumption } },
      apply le_add_of_le_of_nonneg _ c_nonneg,
      suffices h : (x - (g₁o.y - ↑g₁r)) * ↑g₁c ≥ 0, from h,
      apply mul_nonneg r_nonneg (int.le_of_lt _),
      simp, exact (gt_and_gt_of_mul_gt g₁h).2
    },
  have i_bounded : i < g₁r * g₁c,
    {
      rw hi,
      apply linearize_array; unfold is_bounded; split;
        try { rw ← int.coe_nat_le_coe_nat_iff };
        try { rw ← int.coe_nat_lt_coe_nat_iff };
        rw nat_abs_of_nonneg; try { assumption },
      rw sub_lt_iff_lt_add', exact ybounds.2,
      rw ← sub_add, rw add_comm, apply add_lt_of_le_of_neg (le_refl _),
      rw sub_lt_iff_lt_add, rw zero_add, exact xbounds.2
    },
  have h₁ : ∀hh,
    list.nth_le (℘ (
      {r := g₁r, c := g₁c, h := g₁h, o := g₁o, data := g₁d} : fgrid α
    )) i hh =
    list.nth_le (℘ (
      {to_grid₀ := {r := g₁r, c := g₁c, h := g₂h, data := ⟨d₂, hd₂⟩},
        o := g₁o} : agrid₀ α)) i _,
      {
        intros, simp [h], unfold_coes,
        simp [gen_foa_eq_gen]
      },
  specialize h₁ _, swap 2,
  rw length_generate_eq_size, exact i_bounded,
  swap 2,
  rw length_generate_eq_size, exact i_bounded,
  unfold_coes at h₁,
  simp [gen_foa_eq_gen] at h₁,
  simp [
    -sub_eq_add_neg, generate, abs_data, inject_into_bounded,
    grid_point_of_prod, prod_of_rel_point, make_bounded_idx,
    make_bounded, relpoint_of_gpoint, function.uncurry,
    relative_grid.data, vector.nth, tl, bl, rows, nth_le_gip_g,
    bl, gtr, tr, rows, cols
  ] at h₁,
  simp [abs_data, relpoint_of_gpoint, prod_of_rel_point, tl, bl, rows, data,
    function.uncurry, vector.nth],
  unfold_coes at h₁, simp only [z_of_bounded] at h₁,
  have : g₁o.y - of_nat g₁r + of_nat (
             |g₁o.y - of_nat g₁r +
             (of_nat ( |y - tlx| ) + of_nat ( |x - tly| ) * of_nat g₁c) /
             of_nat g₁c - (g₁o.y - of_nat g₁r)| ) = x,
        {
          repeat { rw of_nat_eq_coe },
          repeat { rw add_sub },
          rw add_sub_cancel',
          repeat { rw nat_abs_of_nonneg; try { assumption } },
          change g₁o.y - ↑g₁r with tly,
          rw int.add_mul_div_right,
          rw ← add_assoc, rw add_sub,
          rw div_eq_zero_of_lt c_nonneg (sub_lt_iff_lt_add'.2 ybounds.2),
          simp,
          simp, intros contra, rw contra at g₁h,
          have falso : ¬0 > 0, from gt_irrefl _,
          contradiction,
          rw int.add_mul_div_right,
          apply add_nonneg, apply int.div_nonneg c_nonneg,
          simp [(≥)], exact r_nonneg,
          simp, intros contra, rw contra at g₁h,
          have falso : ¬0 > 0, from gt_irrefl _,
          contradiction,
        },
  simp only [this] at h₁,
  have : g₁o.x + of_nat ( |g₁o.x + of_nat ( |y - tlx| ) % of_nat g₁c - g₁o.x| )
          = y,
    {
      repeat { rw of_nat_eq_coe },
      repeat { rw add_sub },
      rw add_sub_cancel',
      repeat { rw nat_abs_of_nonneg; try { assumption } },
      rw mod_eq_of_lt c_nonneg,
      simp [tlx],
      apply sub_lt_iff_lt_add'.2 ybounds.2,
      apply mod_nonneg,
      simp, intros contra, rw contra at g₁h,
      have falso : ¬0 > 0, from gt_irrefl _,
      contradiction,
    },
  simp only [this] at h₁,
  have : |g₁o.x + of_nat ( |y - tlx| ) % of_nat g₁c - g₁o.x| +
         |g₁o.y - of_nat g₁r + (of_nat ( |y - tlx| ) + of_nat ( |x - tly| ) *
         of_nat g₁c) / of_nat g₁c - (g₁o.y - of_nat g₁r)| * g₁c =
  |y + -g₁o.x| + |x + (↑g₁r + -g₁o.y)| * g₁c,
    {
      repeat { rw of_nat_eq_coe },
      rw add_sub_cancel',
      rw add_sub_cancel',
      simp only [tlx],
      repeat { rw ← sub_eq_add_neg },
      rw mul_comm,
      repeat { rw nat_abs_of_nonneg },
      rw ← int.coe_nat_eq_coe_nat_iff,
      repeat { rw int.coe_nat_add },
      repeat { rw nat_abs_of_nonneg },
      rw int.coe_nat_mul,
      repeat { rw nat_abs_of_nonneg },
      rw int.add_mul_div_right,
      simp only [mul_add],
      rw ← add_assoc,
      rw mod_add_div (y - g₁o.x) ↑g₁c,
      rw int.coe_nat_mul,
      repeat { rw nat_abs_of_nonneg },
      simp [tly],
      rw mul_comm,
      rw add_sub, simp only [(≥)],
      rw le_sub_iff_add_le, simp,
      rw sub_le_iff_le_add at xbounds,
      exact xbounds.1,
      intros contra, simp at contra, rw contra at g₂h,
      simp at g₂h, have : ¬0 > 0, from gt_irrefl _, contradiction,
      simp only [tly],
      rw int.add_mul_div_right,
      apply add_nonneg,
      apply int.div_nonneg,
      simp [(≥)],
      apply le_add_of_sub_right_le,
      simp, exact ybounds.1,
      simp [(≥)],
      rw le_sub_iff_add_le,
      rw zero_add,
      exact xbounds.1,
      intros contra, simp at contra, rw contra at g₂h,
      simp at g₂h, have : ¬0 > 0, from gt_irrefl _, contradiction,
      simp only [(≥)],
      rw le_sub_iff_add_le,
      rw zero_add,
      exact ybounds.1,
      simp only [(≥)],
      apply mod_nonneg,
      intros contra, simp at contra, rw contra at g₂h,
      simp at g₂h, have : ¬0 > 0, from gt_irrefl _, contradiction,
      simp [tly, (≥)],
      rw ← add_assoc,
      rw ← sub_eq_add_neg,
      rw sub_add,
      rw le_sub_iff_add_le,
      rw zero_add,
      exact xbounds.1,
      simp only [(≥)],
      rw le_sub_iff_add_le,
      rw zero_add,
      exact ybounds.1,
    },
  simp only [this] at h₁,
  exact h₁
end

theorem grid_eq_iff_a_f
  {α : Type} {g₁ : agrid₀ α} {g₂ : fgrid α}
  (h₁ : g₁.r = g₂.r)
  (h₂ : g₁.c = g₂.c)
  (h₃ : g₁.o = g₂.o) :
  g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
    ⟨λh, h ▸ rfl, λh, generate_inj_a_f h₁ h₂ h₃ $ by rwa gen_aof_eq_gen.symm⟩ 

theorem grid_eq_iff_f_a
  {α : Type} {g₁ : fgrid α} {g₂ : agrid₀ α}
  (h₁ : g₁.r = g₂.r)
  (h₂ : g₁.c = g₂.c)
  (h₃ : g₁.o = g₂.o) :
  g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
    ⟨λh, h ▸ rfl, λh, generate_inj_f_a h₁ h₂ h₃ h⟩ 

lemma nth_agrid_of_fgrid {α : Type} {g : fgrid α} {n} :
  list.nth (agrid_of_fgrid g).to_grid₀.data.val n = list.nth (℘ g) n :=
begin
  delta agrid_of_fgrid, simp
end  

instance decidable_eq_a_a {α : Type} [decidable_eq α]
  : decidable_eq (agrid₀ α) :=
  λg₁ g₂, if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
            begin
              simp [grid_eq_iff_a_a, *], apply_instance
            end
          else is_false $ by finish

instance decidable_eq_f_f {α : Type} [decidable_eq α]
  : decidable_eq (fgrid α) :=
  λg₁ g₂, if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
            begin
              simp [grid_eq_iff_f_f, *], apply_instance
            end
          else is_false $ by finish

instance decidable_eq_a_f {α : Type} [decidable_eq α]
  {g₁ : agrid₀ α} {g₂ : fgrid α} : decidable (g₁ = g₂) :=
  if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
    begin
      simp [grid_eq_iff_a_f, *], apply_instance
    end
  else is_false $ by finish

instance decidable_eq_f_a {α : Type} [decidable_eq α]
  {g₁ : fgrid α} {g₂ : agrid₀ α} : decidable (g₁ = g₂) :=
  if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
    begin
      simp [grid_eq_iff_f_a, *], apply_instance
    end
  else is_false $ by finish

lemma subgrid_self {α : Type} {g : agrid₀ α} {bb : bounding_box}
  (h : bb = {bounding_box. p₁ := bl g, p₂ := gtr g, h := grid_is_bounding_box })
  : subgrid g bb begin unfold bbox_of_grid, rw h, exact overlaid_by_refl _ end =
    g :=
begin
  cases g with g o, cases g with r c h d, 
  simp [h, subgrid], unfold_coes, rw grid_eq_iff_f_f, rw gen_foa_eq_gen,
  apply ext_le, rw length_generate_eq_size, rw length_generate_eq_size,
  simp [size, rows, cols, rows_of_box, cols_of_box, bl, gtr, tr],
  intros,
  rw nth_generate,
  rw nth_generate,
  simp only [abs_data, data, gtr, tr, bl, (∘),
  relpoint_of_gpoint, prod_of_rel_point, function.uncurry, rows, cols, tl,
  rows_of_box, cols_of_box], simp, unfold_coes,
  simp [z_of_bounded], simp [rows_of_box, bl, gtr, tr, rows],
  simp [cols_of_box, bl, gtr, tr, cols],  
  simp [cols_of_box, bl, gtr, tr, cols]
end

end finite_grid

section grid_instances

def split_rows_cols : ℕ → ℕ → list string → list string
  | cols 0 ls := [""]
  | cols (k + 1) ls := list.take cols ls ++ ["\n"]
                       ++ split_rows_cols cols k (list.drop cols ls)

def grid_str {α : Type*} [grid α]
  [has_to_string (relative_grid.carrier α)] (g : α) : string :=
  let points := list.map to_string $ ℘ g in
    " " ++ (list.foldr append "" $
                       list.intersperse " " $
                       split_rows_cols (relative_grid.cols g)
                                       (relative_grid.rows g) points)

instance grid_repr {α : Type*} [grid α]
  [has_to_string (relative_grid.carrier α)] : has_repr α := ⟨grid_str⟩ 

instance grid_to_string {α : Type*} [grid α]
  [has_to_string (relative_grid.carrier α)] : has_to_string α := ⟨grid_str⟩ 

end grid_instances